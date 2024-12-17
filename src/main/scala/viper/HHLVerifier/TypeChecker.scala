package viper.HHLVerifier

object TypeChecker {
  val boolOp = List("==", "!=", "&&", "||", "forall", "exists", "==>")
  val boolOpForNums = List(">=", "<=", ">", "<", "==", "!=")
  val numOp = List("+", "-", "*", "/", "%")
  val boolType = TypeInstance.boolType
  val intType = TypeInstance.intType
  val stateType = TypeInstance.stateType
  val blockType = TypeInstance.stmtBlockType

  var currMethod: Method = null

  var assertVars: Map[String, Type] = Map.empty
  var isPre: Boolean = false

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
    if (!isHyperAssertion) throw TypeException("At least one precondition of method " + m.mName + " is not a hyper assertion")
    m.post.foreach(p => isHyperAssertion = isHyperAssertion && typeCheckExpr(p, true))
    if (!isHyperAssertion) throw TypeException("At least one postcondition of method " + m.mName + " is not a hyper assertion")
    typeCheckStmt(m.body, false)
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
      case AssignStmt(left, right) =>
        typeCheckExpr(left, false)
        typeCheckExpr(right, false)
        res = checkIfTypeMatch(left.typ, right.typ)
      case MultiAssignStmt(left, right) =>
        left.foreach(v => typeCheckExpr(v, false))
        typeCheckExpr(right, false)
        // Check the variable types on the LHS match with the method return types on the RHS
        left.foreach(
          v => res = res && checkIfTypeMatch(v.typ, right.method.res(left.indexOf(v)).typ)
        )
      case HavocStmt(id, _) =>
        typeCheckExpr(id, false)
      case AssumeStmt(e) =>
        typeCheckExpr(e, false)
        res = checkIfTypeMatch(e.typ, boolType)
        //isTotal = !isInLoop
      case AssertStmt(e) =>
        typeCheckExpr(e, false)
        res = checkIfTypeMatch(e.typ, boolType)
      case HyperAssumeStmt(e) =>
        val isHyperAssertion = typeCheckExpr(e, true)
        if (!isHyperAssertion) throw UnknownException("Only hyper assertions can be used in a hyper-assume statement")
        res = checkIfTypeMatch(e.typ, boolType)
      case HyperAssertStmt(e) =>
        val isHyperAssertion = typeCheckExpr(e, true)
        if (!isHyperAssertion) throw UnknownException("Only hyper assertions can be used in a hyper-assert statement")
        res = checkIfTypeMatch(e.typ, boolType)
      case IfElseStmt(cond, ifStmt, elseStmt) =>
        typeCheckExpr(cond, false)
        res =  checkIfTypeMatch(cond.typ, boolType)
        val isTotalIf = typeCheckStmt(ifStmt, isInLoop)
        val isTotalElse = typeCheckStmt(elseStmt, isInLoop)
        isTotal = isTotal && isTotalIf && isTotalElse
      case DeclareStmt(blockId, stmts) =>
        res = checkIfTypeMatch(blockId.typ, blockType)
        val isTotalBody = typeCheckStmt(stmts, isInLoop)
        isTotal = isTotal && isTotalBody
      case ReuseStmt(blockId) =>
        res = checkIfTypeMatch(blockId.typ, blockType)
      case loop@WhileLoopStmt(cond, body, inv, decr, rule) =>
        var isHyperAssertion = true
        typeCheckExpr(cond, false)
        res = checkIfTypeMatch(cond.typ, boolType)
        inv.map(i => i._2).foreach(i => {
          isHyperAssertion = isHyperAssertion && typeCheckExpr(i, true)
          res = res && checkIfTypeMatch(i.typ, boolType)
        })
        if (!isHyperAssertion) throw TypeException("At least one loop invariant is not a hyper assertion")
        if (rule == "existsRule" && decr.isEmpty) throw UnknownException("To use the exists rule, the loop itself must have a decreases clause")
        if (rule == "existsRule" && !Generator.autoSelectRules) throw UnknownException("To use the exists rule, users must enable auto-selection of loop rules")
        if (!decr.isEmpty) {
          typeCheckExpr(decr.get, false)
          res = res && checkIfTypeMatch(decr.get.typ, intType)
        }
        val loopBodyIsTotal = typeCheckStmt(body, true)
        loop.isTotal = !decr.isEmpty && loopBodyIsTotal
        isTotal = isTotal && loop.isTotal
        if (!loop.isTotal && rule == "syncTotRule")
          throw UnknownException("To use the syncTot rule, the loop itself must have a decreases clause," +
            " and its body must not contain any assume statements or nested loops without decreases clauses")
      case FrameStmt(framedAssertion, body) =>
        val isHyperAssertion = typeCheckExpr(framedAssertion, true)
        if (!isHyperAssertion) throw TypeException("Only hyper assertions can be framed")
        res = checkIfTypeMatch(framedAssertion.typ, boolType)
        val bodyIsTotal = typeCheckStmt(body, isInLoop)
        isTotal = isTotal && bodyIsTotal
      case PVarDecl(vName, vType) =>
        vName.typ = vType
        res = true
      case ProofVarDecl(_, p) =>
        // hyperAssertionExpected set to true so that program variables can't occur in p
        typeCheckExpr(p, true)
        res = checkIfTypeMatch(p.typ, boolType)
      case UseHintStmt(hint) =>
        // Program variables cannot appear as a hint argument
        // So we set hyperAssertionExpected to true, without verifying if we indeed have a hyper assertion
        typeCheckExpr(hint, true)
        res = checkIfTypeMatch(hint.typ, boolType)
      case call@MethodCallStmt(name, args) =>
        args.foreach(a => {
          typeCheckExpr(a, false)
          res = res && checkIfTypeMatch(a.typ, call.method.params(args.indexOf(a)).typ)
        })
        if (!res) throw TypeException("The types of the arguments in the call to method " + name + " do not match with the types of the method parameters")
    }
    if (!res) throw TypeException("The statement has a type error: " + s)
    else isTotal
  }

  // hyperAssertionExpected is true if e is expected to be (part of) a hyper assertion
  // Returns true if e indeed is (or contains) a hyper assertion
  def typeCheckExpr(e: Expr, hyperAssertionExpected: Boolean, polarity: Int = 1) : Boolean = {
    var res = true
    var isHyperAssertion = false
    e match {
      case id@Id(_) =>
        if (hyperAssertionExpected) throw TypeException("Program variables cannot appear in a hyper assertion or a hint")
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
            if (numOp.contains(op)) be.typ = intType
            else be.typ = boolType
        } else if (e1.typ.isInstanceOf[BoolType]) {
            res = res && boolOp.contains(op)
            be.typ = boolType
        } else res = false  // e1 & e2 have the same type, but their type is undefined for the binary operator
      case ue@UnaryExpr(op, e) =>
        if (op == "!") {
          isHyperAssertion = typeCheckExpr(e, hyperAssertionExpected, polarity)
          res = checkIfTypeMatch(e.typ, boolType)
          ue.typ = boolType
        } else if (op == "-") {
          typeCheckExpr(e, hyperAssertionExpected, polarity)
          res = checkIfTypeMatch(e.typ, intType)
          ue.typ = intType
        }
      case num@Num(_) =>
        num.typ = intType
      case bool@BoolLit(_) =>
        bool.typ = boolType
      case av@AssertVar(name) =>
        if (assertVars.keySet.contains(name)) av.typ = assertVars.get(name).get
        else res = false
      case AssertVarDecl(vName, vType) =>
        if (!hyperAssertionExpected && vType.isInstanceOf[StateType]) throw TypeException("Variables of type State" + vName +" can only appear in a hyper assertion. ")
        vName.typ = vType
      // AssertVarDecl expression itself doesn't have a concrete type
      case ie@ImpliesExpr(left, right) =>
        val isHyperAssertionLeft = typeCheckExpr(left, hyperAssertionExpected, polarity * (-1))
        val isHyperAssertionRight = typeCheckExpr(right, hyperAssertionExpected, polarity * 1)
        isHyperAssertion = isHyperAssertionLeft || isHyperAssertionRight
        res = checkIfTypeMatch(left.typ, boolType) && checkIfTypeMatch(right.typ, boolType)
        ie.typ = boolType
      case ast@Assertion(_, assertVarDecls, body) =>
        isHyperAssertion = typeCheckAssertionHelper(assertVarDecls, body, hyperAssertionExpected, polarity)
        ast.typ = boolType
      case gve@GetValExpr(state, id) =>
        isHyperAssertion = true
        // When type checking for id in a GetValExpr, fix hyperAssertionExpected to be false
        // Any other occurrence of Id instances should be type checked with the correct inHyperAssertion flag
        typeCheckExpr(state, hyperAssertionExpected)
        typeCheckExpr(id, false)
        res = checkIfTypeMatch(state.typ, stateType)
        gve.typ = id.typ
      case se@StateExistsExpr(state, _) =>
        isHyperAssertion = true
        se.useForAll = (polarity < 0)
        typeCheckExpr(state, hyperAssertionExpected)
        res = checkIfTypeMatch(state.typ, stateType)
        se.typ = boolType
        if (se.err && isPre) throw UnknownException("Preconditions cannot refer to failure states")
      case li@LoopIndex() =>
        li.typ = intType
      case pv@ProofVar(name) =>
        isHyperAssertion = true
        if (currMethod.allVars.contains(name)) {
          pv.typ = currMethod.allVars.get(name).get
        } else res = false
      case h@Hint(name, arg) =>
        if (!hyperAssertionExpected) throw UnknownException("Hint" + name + " can only appear in a hyper assertion or a use hint statement")
        typeCheckExpr(arg, hyperAssertionExpected)
        // At the moment, we only allow hints to take 1 argument of type Int
        res = checkIfTypeMatch(arg.typ, intType)
        h.typ = boolType
      case call@MethodCallExpr(name, args) =>
        args.foreach(a => {
          typeCheckExpr(a, false)
          res = res && checkIfTypeMatch(a.typ, call.method.params(args.indexOf(a)).typ)
        })
        if (!res) throw TypeException("The types of the arguments in the call to method " + name + " do not match with the types of the method parameters")
    }
    if (!res) throw TypeException("The expression has a type error: " + e)
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
    if (!checkIfTypeMatch(body.typ, boolType)) throw TypeException("The expression " + body + " should have type Bool")
    assertVars = originalAssertVars
    isHyperAssertion
  }

  def checkIfTypeMatch(t1: Type, t2: Type): Boolean = {
    (t1.isInstanceOf[IntType] && t2.isInstanceOf[IntType]) ||
      (t1.isInstanceOf[BoolType] && t2.isInstanceOf[BoolType]) ||
      (t1.isInstanceOf[StateType] && t2.isInstanceOf[StateType]) ||
      (t1.isInstanceOf[StmtBlockType] && t2.isInstanceOf[StmtBlockType])
  }

}
