package viper.HHLVerifier.typing

import viper.HHLVerifier.generation.Generator
import viper.HHLVerifier.management.Logger
import viper.HHLVerifier.symbols.SymbolChecker
import viper.HHLVerifier._
import viper.HHLVerifier.ast.{AssertStmt, AssertVar, AssertVarDecl, Assertion, AssignStmt, AssumeStmt, BinaryExpr, BoolLit, CombExpr, CompositeStmt, DeclareStmt, Expr, FrameStmt, HHLProgram, HavocStmt, Hint, HyperAssertStmt, HyperAssumeStmt, Id, IfElseStmt, ImpliesExpr, LengthExpr, LookupExpr, LoopIndex, MapAssignExpr, Method, MethodCallExpr, MethodCallStmt, MultiAssignStmt, Num, PVarDecl, ProofVar, ProofVarDecl, ReuseStmt, SeqAssignExpr, SetAssignExpr, StateExistsExpr, Stmt, UnaryExpr, UpdateMapExpr, UseHintStmt, WhileLoopStmt}

object TypeChecker {
  val boolOp = List("==", "!=", "&&", "||", "forall", "exists", "==>")
  val boolOpForNums = List(">=", "<=", ">", "<", "==", "!=")
  val numOp = List("+", "-", "*", "/", "%")

  var currMethod: Method = null

  var assertVars: Map[String, Type] = Map.empty
  var isPre: Boolean = false

  var declaredTypes: Set[Type] = Set.empty
  var hasSeqs: Boolean = false
  var hasMaps: Boolean = false

  def addToDeclaredTypes(typ: Type): Unit = {
    declaredTypes += typ
    if (typ.isInstanceOf[SeqType] && !hasSeqs) hasSeqs = true
    else if (typ.isInstanceOf[MapType] && !hasMaps) hasMaps = true
  }

  def reset(): Unit = {
    currMethod = null
    assertVars = Map.empty
  }

  def typeCheckProg(p: HHLProgram): Unit = {
    p.content.foreach(m => typeCheckMethod(m))
  }

  def typeCheckMethod(m: Method): Unit = {
    currMethod = m
    var isHyperAssertion = true
    isPre = true
    m.pre.foreach(p => isHyperAssertion = isHyperAssertion && typeCheckExpr(p, true))
    isPre = false
    if (!isHyperAssertion) throw new Logger("At least one precondition of method " + m.mName + " is not a hyper assertion").addTitle("Type Checker Error").addOffset((m.pre(0).offsetLeft, m.pre.last.offsetRight))
    m.post.foreach(p => isHyperAssertion = isHyperAssertion && typeCheckExpr(p, true))
    if (!isHyperAssertion) throw new Logger("At least one postcondition of method " + m.mName + " is not a hyper assertion").addTitle("Type Checker Error").addOffset((m.post(0).offsetLeft, m.post.last.offsetRight))
    typeCheckStmt(m.body, false)

    // add types
    m.params.foreach(id => addToDeclaredTypes(id.typ))
    m.res.foreach(id => addToDeclaredTypes(id.typ))
  }

  def typeCheckStmt(s: Stmt, isInLoop: Boolean): Boolean = {
    var res = true
    var isTotal = true
    s match {
      case CompositeStmt(stmts) =>
        stmts.foreach(stmt => {
          val stmtIsTotal = typeCheckStmt(stmt, isInLoop)
          isTotal = isTotal && stmtIsTotal
        })
      case e@AssignStmt(left, right) =>
        typeCheckExprWithChecks(s, left, false)
        typeCheckExprWithChecks(s, right, false)
        res = checkIfTypeMatch(left.typ, right.typ)
      case MultiAssignStmt(left, right) =>
        left.foreach(v => typeCheckExprWithChecks(s, v, false))
        typeCheckExprWithChecks(s, right, false)
        // Check the variable types on the LHS match with the method return types on the RHS
        left.foreach(
          v => res = res && checkIfTypeMatch(v.typ, right.method.res(left.indexOf(v)).typ)
        )
      case HavocStmt(id, _) =>
        typeCheckExprWithChecks(s, id, false)
      case AssumeStmt(e) =>
        typeCheckExprWithChecks(s, e, false)
        res = checkIfTypeMatch(e.typ, BoolType())
        //isTotal = !isInLoop
      case AssertStmt(e) =>
        typeCheckExprWithChecks(s, e, false)
        res = checkIfTypeMatch(e.typ, BoolType())
      case stmt@HyperAssumeStmt(e) =>
        val isHyperAssertion = typeCheckExprWithChecks(s, e, true)
        if (!isHyperAssertion) throw new Logger("Only hyper assertions can be used in a hyper-assume statement").addTitle("Type Checker Error").addOffset((stmt.offsetLeft, stmt.offsetRight))
        res = checkIfTypeMatch(e.typ, BoolType())
      case stmt@HyperAssertStmt(e) =>
        val isHyperAssertion = typeCheckExprWithChecks(s, e, true)
        if (!isHyperAssertion)  throw new Logger("Only hyper assertions can be used in a hyper-assert statement").addTitle("Type Checker Error").addOffset((stmt.offsetLeft, stmt.offsetRight))
        res = checkIfTypeMatch(e.typ, BoolType())
      case IfElseStmt(cond, ifStmt, elseStmt) =>
        typeCheckExprWithChecks(s, cond, false)
        res =  checkIfTypeMatch(cond.typ, BoolType())
        val isTotalIf = typeCheckStmt(ifStmt, isInLoop)
        val isTotalElse = typeCheckStmt(elseStmt, isInLoop)
        isTotal = isTotal && isTotalIf && isTotalElse
      case DeclareStmt(blockId, stmts) =>
        res = checkIfTypeMatch(blockId.typ, StmtBlockType())
        val isTotalBody = typeCheckStmt(stmts, isInLoop)
        isTotal = isTotal && isTotalBody
      case ReuseStmt(blockId) =>
        res = checkIfTypeMatch(blockId.typ, StmtBlockType())
      case loop@WhileLoopStmt(cond, body, inv, decr, rule) =>
        var isHyperAssertion = true
        typeCheckExprWithChecks(s, cond, false)
        res = checkIfTypeMatch(cond.typ, BoolType())
        inv.map(i => i._2).foreach(i => {
          isHyperAssertion = isHyperAssertion && typeCheckExprWithChecks(s, i, true)
          res = res && checkIfTypeMatch(i.typ, BoolType())
        })
        if (!isHyperAssertion)  throw new Logger("At least one loop invariant is not a hyper assertion").addTitle("Type Checker Error").addOffset((loop.offsetLeft, loop.offsetRight))
        if (rule == "existsRule" && decr.isEmpty)  throw new Logger("To use the exists rule, the loop itself must have a decreases clause").addTitle("Type Checker Error").addOffset((loop.offsetLeft, loop.offsetRight))
        if (rule == "existsRule" && !Generator.autoSelectRules)  throw new Logger("To use the exists rule, users must enable auto-selection of loop rules").addTitle("Type Checker Error").addOffset((loop.offsetLeft, loop.offsetRight))
        if (!decr.isEmpty) {
          typeCheckExprWithChecks(s, decr.get, false)
          res = res && checkIfTypeMatch(decr.get.typ, IntType())
        }
        val loopBodyIsTotal = typeCheckStmt(body, true)
        loop.isTotal = !decr.isEmpty && loopBodyIsTotal
        isTotal = isTotal && loop.isTotal
        if (!loop.isTotal && rule == "syncTotRule")
          throw new Logger("To use the syncTot rule, the loop itself must have a decreases clause, and its body must not contain any assume statements or nested loops without decreases clauses").addTitle("Type Checker Error").addOffset((loop.offsetLeft, loop.offsetRight))
      case FrameStmt(framedAssertion, body) =>
        val isHyperAssertion = typeCheckExprWithChecks(s, framedAssertion, true)
        if (!isHyperAssertion)  throw new Logger("Only hyper assertions can be framed").addTitle("Type Checker Error").addOffset((framedAssertion.offsetLeft, framedAssertion.offsetRight))
        res = checkIfTypeMatch(framedAssertion.typ, BoolType())
        val bodyIsTotal = typeCheckStmt(body, isInLoop)
        isTotal = isTotal && bodyIsTotal
      case PVarDecl(vName, vType) =>
        vName.typ = vType
        addToDeclaredTypes(vType)
        res = true
      case ProofVarDecl(_, p) =>
        // hyperAssertionExpected set to true so that program variables can't occur in p
        typeCheckExprWithChecks(s, p, true)
        res = checkIfTypeMatch(p.typ, BoolType())
      case UseHintStmt(hint) =>
        // Program variables cannot appear as a hint argument
        // So we set hyperAssertionExpected to true, without verifying if we indeed have a hyper assertion
        typeCheckExprWithChecks(s, hint, true)
        res = checkIfTypeMatch(hint.typ, BoolType())
      case call@MethodCallStmt(name, args) =>
        args.foreach(a => {
          typeCheckExprWithChecks(s, a, false)
          res = res && checkIfTypeMatch(a.typ, call.method.params(args.indexOf(a)).typ)
        })
        if (!res) throw new Logger("The types of the arguments in the call to method " + name + " do not match with the types of the method parameters").addTitle("Type Checker Error").addOffset((call.offsetLeft, call.offsetRight))
      case _ => throw new Logger("Unkown statement detected").addTitle("Type Checker Error").addOffset((s.offsetLeft, s.offsetRight))
    }
    if (!res) throw new Logger("The statement has a type error: " + s).addTitle("Type Checker Error").addOffset((s.offsetLeft, s.offsetRight))
    else isTotal
  }

  var lookupAccesses: Seq[LookupExpr] = Seq.empty
  def typeCheckExprWithChecks(s: Stmt, e: Expr, hyperAssertionExpected: Boolean, polarity: Int = 1): Boolean = {
    val isHyperAssertion = typeCheckExpr(e, hyperAssertionExpected, polarity)

    s.lookUpAccesses = lookupAccesses
    lookupAccesses = Seq.empty

    isHyperAssertion
  }

  // hyperAssertionExpected is true if e is expected to be (part of) a hyper assertion
  // Returns true if e indeed is (or contains) a hyper assertion
  def typeCheckExpr(e: Expr, hyperAssertionExpected: Boolean, polarity: Int = 1) : Boolean = {
    var res = true
    var isHyperAssertion = false

    e match {
      case id@Id(_) =>
        if (hyperAssertionExpected)  throw new Logger("Program variables cannot appear in a hyper assertion or a hint").addTitle("Type Checker Error").addOffset((id.offsetLeft, id.offsetRight))
        if (currMethod.allVars.contains(id.name)) id.typ = currMethod.allVars.get(id.name).get
        else res = false
      case be@BinaryExpr(e1, op, e2) =>
        val isHyperAssertionLeft = typeCheckExpr(e1, hyperAssertionExpected, polarity)
        val isHyperAssertionRight = typeCheckExpr(e2, hyperAssertionExpected, polarity)
        isHyperAssertion = isHyperAssertionLeft || isHyperAssertionRight
        val typeMatched = checkIfTypeMatch(e1.typ, e2.typ)
        res = res && typeMatched
        if (!typeMatched) res = false
        else if (e1.typ.isInstanceOf[IntType]) {
            res = res && (numOp ++ boolOpForNums).contains(op)
            if (numOp.contains(op)) be.typ = IntType()
            else be.typ = BoolType()
        } else if (e1.typ.isInstanceOf[BoolType]) {
            res = res && boolOp.contains(op)
            be.typ = BoolType()
        } else {
          res = true
          be.typ = BoolType() // TODO: Check if this is correct
        }  // e1 & e2 have the same type, but their type is undefined for the binary operator
      case ue@UnaryExpr(op, e) =>
        if (op == "!") {
          isHyperAssertion = typeCheckExpr(e, hyperAssertionExpected, polarity)
          res = checkIfTypeMatch(e.typ, BoolType())
          ue.typ = BoolType()
        } else if (op == "-") {
          typeCheckExpr(e, hyperAssertionExpected, polarity)
          res = checkIfTypeMatch(e.typ, IntType())
          ue.typ = IntType()
        }
      case num@Num(_) =>
        num.typ = IntType()
      case bool@BoolLit(_) =>
        bool.typ = BoolType()
      case av@AssertVar(name) =>
        if (assertVars.keySet.contains(name)) av.typ = assertVars.get(name).get
        else res = false
      case e@AssertVarDecl(vName, vType) =>
        if (!hyperAssertionExpected && vType.isInstanceOf[StateType])  throw new Logger("Variables of type State" + vName +" can only appear in a hyper assertion.").addTitle("Type Checker Error").addOffset((e.offsetLeft, e.offsetRight))
        vName.typ = vType
      // AssertVarDecl expression itself doesn't have a concrete type
      case ie@ImpliesExpr(left, right) =>
        val isHyperAssertionLeft = typeCheckExpr(left, hyperAssertionExpected, polarity * (-1))
        val isHyperAssertionRight = typeCheckExpr(right, hyperAssertionExpected, polarity * 1)
        isHyperAssertion = isHyperAssertionLeft || isHyperAssertionRight
        res = checkIfTypeMatch(left.typ, BoolType()) && checkIfTypeMatch(right.typ, BoolType())
        ie.typ = BoolType()
      case ast@Assertion(_, assertVarDecls, body) =>
        isHyperAssertion = typeCheckAssertionHelper(assertVarDecls, body, hyperAssertionExpected, polarity)
        ast.typ = BoolType()
        // TODO: ADAPT THIS
      /*case gve@GetValExpr(state, id) =>
        isHyperAssertion = true
        // When type checking for id in a GetValExpr, fix hyperAssertionExpected to be false
        // Any other occurrence of Id instances should be type checked with the correct inHyperAssertion flag
        exprContainsHyperAssertion(state, hyperAssertionExpected)
        exprContainsHyperAssertion(id, false)
        res = checkIfTypeMatch(state.typ, stateType)
        gve.typ = id.typ*/
      case se@StateExistsExpr(state, _) =>
        isHyperAssertion = true
        se.useForAll = (polarity < 0)
        typeCheckExpr(state, hyperAssertionExpected)
        res = checkIfTypeMatch(state.typ, StateType())
        se.typ = BoolType()
        if (se.err && isPre)  throw new Logger("Preconditions cannot refer to failure states").addTitle("Type Checker Error").addOffset((se.offsetLeft, se.offsetRight))
      case li@LoopIndex() =>
        li.typ = IntType()
      case pv@ProofVar(name) =>
        isHyperAssertion = true
        if (currMethod.allVars.contains(name)) {
          pv.typ = currMethod.allVars.get(name).get
        } else res = false
      case h@Hint(name, arg) =>
        if (!hyperAssertionExpected)  throw new Logger("Hint" + name + " can only appear in a hyper assertion or a use hint statement").addTitle("Type Checker Error").addOffset((h.offsetLeft, h.offsetRight))
        typeCheckExpr(arg, hyperAssertionExpected)
        // At the moment, we only allow hints to take 1 argument of type Int
        res = checkIfTypeMatch(arg.typ, IntType())
        h.typ = BoolType()
      case call@MethodCallExpr(name, args) =>
        args.foreach(a => {
          typeCheckExpr(a, false)
          res = res && checkIfTypeMatch(a.typ, call.method.params(args.indexOf(a)).typ)
        })
        if (!res)
          throw new Logger("The types of the arguments in the call to method " + name + " do not match with the types of the method parameters").addTitle("Type Checker Error").addOffset((call.offsetLeft, call.offsetRight))
        val calledMethodList = SymbolChecker.allMethods.filter(m => m.mName == name)
        if (calledMethodList.isEmpty)
          throw new Logger("The function " + name + " was not found").addTitle("Type Checker Error").addOffset((call.offsetLeft, call.offsetRight))
      case SeqAssignExpr(elements) =>
        elements.foreach(el => {
          typeCheckExpr(el, hyperAssertionExpected)
          res = res && checkIfTypeMatch(e.typ.asInstanceOf[SeqType].sType, el.typ)
        })
      case SetAssignExpr(elements) =>
        elements.foreach(el => {
          typeCheckExpr(el, hyperAssertionExpected)
          res = res && checkIfTypeMatch(e.typ.asInstanceOf[SetType].sType, el.typ)
        })
      case MapAssignExpr(elements) =>
        elements.foreach(el => {
          typeCheckExpr(el.k, hyperAssertionExpected)
          typeCheckExpr(el.v, hyperAssertionExpected)
          res = res && checkIfTypeMatch(e.typ.asInstanceOf[MapType].kType, el.k.typ) && checkIfTypeMatch(e.typ.asInstanceOf[MapType].vType, el.v.typ)
        })
      case e@LookupExpr(id, ind) =>
        typeCheckExpr(id, hyperAssertionExpected)

        if (id.typ.isInstanceOf[SeqType]) {
          typeCheckExpr(ind, hyperAssertionExpected)
          res = ind.typ.isInstanceOf[IntType]
          e.baseType = id.typ.asInstanceOf[SeqType]
          e.typ = id.typ.asInstanceOf[SeqType].sType
          lookupAccesses = lookupAccesses :+ e
        } else if (id.typ.isInstanceOf[MapType]) {
          typeCheckExpr(ind, hyperAssertionExpected)
          res = checkIfTypeMatch(id.typ.asInstanceOf[MapType].kType, ind.typ)
          e.baseType = id.typ.asInstanceOf[MapType]
          e.typ = id.typ.asInstanceOf[MapType].kType
          lookupAccesses = lookupAccesses :+ e
        } else if (id.typ.isInstanceOf[StateType]) {
          typeCheckExpr(ind, false)
          isHyperAssertion = true
          e.typ = ind.typ
        } else throw new Logger("Lookup can only be applied to SeqType, MapType or StateType").addTitle("Type Checker Error").addOffset((e.offsetLeft, e.offsetRight))
      case e@LengthExpr(id) =>
        typeCheckExpr(id, hyperAssertionExpected)
        if (!id.typ.isInstanceOf[SeqType] && !id.typ.isInstanceOf[SetType] && !id.typ.isInstanceOf[MapType]) throw new Logger("|.| can only be applied to composite types").addTitle("Type Checker Error").addOffset((e.offsetLeft, e.offsetRight))
        e.typ = IntType()
      case e@UpdateMapExpr(id, update) =>
        typeCheckExpr(id, hyperAssertionExpected)
        typeCheckExpr(update.k, hyperAssertionExpected)
        typeCheckExpr(update.v, hyperAssertionExpected)
        if (!id.typ.isInstanceOf[MapType]) throw new Logger("Map update can only be applied to variables of type Map").addTitle("Type Checker Error").addOffset((e.offsetLeft, e.offsetRight))
        val t = id.typ.asInstanceOf[MapType]
        res = checkIfTypeMatch(t.kType, update.k.typ) && checkIfTypeMatch(t.vType, update.v.typ)
        e.typ = t
      case e@CombExpr(lhs, rhs, op) =>
        typeCheckExpr(lhs, hyperAssertionExpected)
        typeCheckExpr(rhs, hyperAssertionExpected)

        if (op == "in") {
          if (rhs.typ.isInstanceOf[SetType]) res = checkIfTypeMatch(lhs.typ, rhs.typ.asInstanceOf[SetType].sType)
          else if (rhs.typ.isInstanceOf[MapType]) res = checkIfTypeMatch(lhs.typ, rhs.typ.asInstanceOf[MapType].kType)
          else throw new Logger("in operation can only be applied to maps or sets").addTitle("Type Checker Error").addOffset((e.offsetLeft, e.offsetRight))
          e.typ = BoolType()
        } else if (op == "++") {
          if (!rhs.typ.isInstanceOf[SeqType] || !lhs.typ.isInstanceOf[SeqType]) throw new Logger("++ operation can only be applied to seqs").addTitle("Type Checker Error").addOffset((e.offsetLeft, e.offsetRight))
          res = checkIfTypeMatch(rhs.typ, lhs.typ)
          e.typ = rhs.typ
        } else {
          if (!rhs.typ.isInstanceOf[SetType] || !lhs.typ.isInstanceOf[SetType]) throw new Logger("Set operation can only be applied to sets").addTitle("Type Checker Error").addOffset((e.offsetLeft, e.offsetRight))
          res = checkIfTypeMatch(lhs.typ, rhs.typ)
          e.typ = lhs.typ
        }
      case _ => throw new Logger("Unkown type detected in Expression" + e.getClass()).addTitle("Type Checker Error").addOffset((e.offsetLeft, e.offsetRight))
    }
    if (!res) throw new Logger(f"The expression has a type error: $e is of type ${e.getClass()}").addTitle("Type Checker Error").addOffset((e.offsetLeft, e.offsetRight))
    isHyperAssertion
  }

  def typeCheckAssertionHelper(assertVarDecls: Seq[AssertVarDecl], body: Expr, hyperAssertionExpected: Boolean, polarity: Int): Boolean = {
    // Check whether at least one assertion variable has type State
    var isHyperAssertion = assertVarDecls.exists(decl => decl.vType.isInstanceOf[StateType])
    assertVarDecls.foreach(decl => typeCheckExpr(decl, hyperAssertionExpected))
    val originalAssertVars = assertVars
    // AssertVar will appear in the body. Update the assertVars map before type checking the body
    assertVars = assertVars ++ assertVarDecls.map(decl => decl.vName.name -> decl.vType).toMap
    val bodyIsHyperAssertion = typeCheckExpr(body, hyperAssertionExpected, polarity)
    isHyperAssertion = isHyperAssertion || bodyIsHyperAssertion
    if (!checkIfTypeMatch(body.typ, BoolType())) throw new Logger("The expression " + body + " should have type Bool").addTitle("Type Checker Error").addOffset((body.offsetLeft, body.offsetRight))
    assertVars = originalAssertVars
    isHyperAssertion
  }

  def checkIfTypeMatch(t1: Type, t2: Type): Boolean = {
    (t1, t2) match {
      // Primitive types
      case (s: IntType, t: IntType) => true
      case (s: BoolType, t: BoolType) => true
      case (s: StateType, t: StateType) => true
      case (s: StmtBlockType, t: StmtBlockType) => true
      // Composite types
      case (s: SeqType, t: SeqType) => checkIfTypeMatch(s.sType, t.sType)
      case (s: SetType, t: SetType) => checkIfTypeMatch(s.sType, t.sType)
      case (s: MapType, t: MapType) => checkIfTypeMatch(s.kType, t.kType) && checkIfTypeMatch(s.vType, t.vType)
      // Non-matching types
      case _ => false
    }
  }

}
