package viper.HHLVerifier

object TypeChecker {
  val boolOp = List("==", "!=", "&&", "||", "forall", "exists", "implies")
  val boolOpForNums = List(">=", "<=", ">", "<", "==", "!=")
  val numOp = List("+", "-", "*", "/", "%")
  val boolType = TypeInstance.boolType
  val intType = TypeInstance.intType
  val stateType = TypeInstance.stateType
  val blockType = TypeInstance.stmtBlockType

  var currMethod: Method = null

  var assertVars: Map[String, Type] = Map.empty

  def typeCheckProg(p: HHLProgram): Unit = {
    p.content.foreach(m => typeCheckMethod(m))
  }

  def typeCheckMethod(m: Method): Unit = {
    currMethod = m
    var isHyperAssertion = true
    m.pre.foreach(p => isHyperAssertion = isHyperAssertion && typeCheckExpr(p, true))
    if (!isHyperAssertion) throw TypeException("At least one precondition of method " + m.mName + " is not a hyper assertion")
    m.post.foreach(p => isHyperAssertion = isHyperAssertion && typeCheckExpr(p, true))
    if (!isHyperAssertion) throw TypeException("At least one postcondition of method " + m.mName + " is not a hyper assertion")
    typeCheckStmt(m.body)
  }

  def typeCheckStmt(s: Stmt): Unit = {
    var res = true
    s match {
      case CompositeStmt(stmts) =>
        stmts.foreach(stmt => typeCheckStmt(stmt))
      case AssignStmt(left, right) =>
        typeCheckExpr(left, false)
        typeCheckExpr(right, false)
        res =checkIfTypeMatch(left.typ, right.typ)
      case HavocStmt(id, _) =>
        typeCheckExpr(id, false)
      case AssumeStmt(e) =>
        typeCheckExpr(e, false)
        res = checkIfTypeMatch(e.typ, boolType)
      case AssertStmt(e) =>
        typeCheckExpr(e, false)
        res = checkIfTypeMatch(e.typ, boolType)
      case HyperAssumeStmt(e) =>
        val isHyperAssertion = typeCheckExpr(e, false)
        // if (!isHyperAssertion) throw UnknownException("Only hyper assertions can be used in a hyper-assume statement")
        res = checkIfTypeMatch(e.typ, boolType)
      case HyperAssertStmt(e) =>
        val isHyperAssertion = typeCheckExpr(e, true)
        if (!isHyperAssertion) throw UnknownException("Only hyper assertions can be used in a hyper-assert statement")
        res = checkIfTypeMatch(e.typ, boolType)
      case IfElseStmt(cond, ifStmt, elseStmt) =>
        typeCheckExpr(cond, false)
        res =  checkIfTypeMatch(cond.typ, boolType)
        typeCheckStmt(ifStmt)
        typeCheckStmt(elseStmt)
      case DeclareStmt(blockId, stmts) =>
        res = checkIfTypeMatch(blockId.typ, blockType)
        typeCheckStmt(stmts)
      case ReuseStmt(blockId) =>
        res = checkIfTypeMatch(blockId.typ, blockType)
      case WhileLoopStmt(cond, body, inv) =>
        var isHyperAssertion = true
        typeCheckExpr(cond, false)
        res = checkIfTypeMatch(cond.typ, boolType)
        inv.map(i => i._2).foreach(i => {
          isHyperAssertion = isHyperAssertion && typeCheckExpr(i, true)
          res = res && checkIfTypeMatch(i.typ, boolType)
        })
        if (!isHyperAssertion) throw TypeException("At least one loop invariant is not a hyper assertion")
        typeCheckStmt(body)
      case FrameStmt(framedAssertion, body) =>
        val isHyperAssertion = typeCheckExpr(framedAssertion, true)
        if (!isHyperAssertion) throw TypeException("Only hyper assertions can be framed")
        res = checkIfTypeMatch(framedAssertion.typ, boolType)
        typeCheckStmt(body)
      case PVarDecl(vName, vType) =>
        vName.typ = vType
        res = true
      case ProofVarDecl(_, p) =>
        typeCheckExpr(p, false)
        res = checkIfTypeMatch(p.typ, boolType)
      case UseHintStmt(hint) =>
        // Program variables cannot appear as a hint argument
        // So we set hyperAssertionExpected to true, without verifying if we indeed have a hyper assertion
        typeCheckExpr(hint, true)
        res = checkIfTypeMatch(hint.typ, boolType)
    }
    if (!res) throw TypeException("The statement has a type error: " + s)
  }

  // hyperAssertionExpected is true if e is expected to be (part of) a hyper assertion
  // Returns true if e indeed is (or contains) a hyper assertion
  def typeCheckExpr(e: Expr, hyperAssertionExpected: Boolean, inHintUse: Boolean = false) : Boolean = {
    var res = true
    var isHyperAssertion = false
    e match {
      case id@Id(_) =>
        if (hyperAssertionExpected) throw TypeException("Program variables cannot appear in a hyper assertion or a hint")
        if (currMethod.allVars.contains(id.name)) id.typ = currMethod.allVars.get(id.name).get
        else res = false
      case be@BinaryExpr(e1, op, e2) =>
        isHyperAssertion = typeCheckExpr(e1, hyperAssertionExpected) || typeCheckExpr(e2, hyperAssertionExpected)
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
          isHyperAssertion = typeCheckExpr(e, hyperAssertionExpected)
          res = checkIfTypeMatch(e.typ, boolType)
          ue.typ = boolType
        } else if (op == "-") {
          typeCheckExpr(e, hyperAssertionExpected)
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
        if (!hyperAssertionExpected && vType.isInstanceOf[StateType]) throw TypeException("Variables of type State can only appear in a hyper assertion. ")
        vName.typ = vType
      // AssertVarDecl expression itself doesn't have a concrete type
      case ie@ImpliesExpr(left, right) =>
        isHyperAssertion = typeCheckExpr(left, hyperAssertionExpected) || typeCheckExpr(right, hyperAssertionExpected)
        res = checkIfTypeMatch(left.typ, boolType) && checkIfTypeMatch(right.typ, boolType)
        ie.typ = boolType
      case ast@Assertion( _, assertVarDecls, body) =>
        res = typeCheckAssertionHelper(assertVarDecls, body, true)
        ast.typ = boolType
        isHyperAssertion = true
      case gve@GetValExpr(state, id) =>
        // When type checking for id in a GetValExpr, fix inHyperAssertion to be false to avoid exceptions
        // Any other occurrence of Id instances should be type checked with the correct inHyperAssertion flag
        typeCheckExpr(state, hyperAssertionExpected)
        typeCheckExpr(id, false)
        res = checkIfTypeMatch(state.typ, stateType)
        gve.typ = id.typ
      case se@StateExistsExpr(state) =>
        typeCheckExpr(state, hyperAssertionExpected)
        res = checkIfTypeMatch(state.typ, stateType)
        se.typ = boolType
      case li@LoopIndex() =>
        li.typ = intType
      case pv@ProofVar(name) =>
        if (currMethod.allVars.contains(name)) {
          pv.typ = currMethod.allVars.get(name).get
        } else res = false
      case h@Hint(name, args) =>
        if (!hyperAssertionExpected) throw UnknownException("Hints can only appear in a hyper assertion or a use hint statement")
        val expectedArgs = SymbolChecker.allHints.get(name).get
        if (expectedArgs.length != args.length) throw UnknownException("The hint " + name + " is expected to be used with " + expectedArgs.length + " arguments. ")
        args.foreach(a => typeCheckExpr(a, hyperAssertionExpected))
        expectedArgs.foreach(
          a => checkIfTypeMatch(a, args(expectedArgs.indexOf(a)).typ)
        )
        h.typ = boolType
    }
    if (!res) throw TypeException("The expression has a type error: " + e)
    isHyperAssertion
  }

  def typeCheckAssertionHelper(assertVarDecls: Seq[AssertVarDecl], body: Expr, inHyperAssertion: Boolean): Boolean = {
    var res = true
    assertVarDecls.foreach(decl => typeCheckExpr(decl, inHyperAssertion))
    if (inHyperAssertion
        && !assertVarDecls.exists(decl => decl.vType.isInstanceOf[StateType])
        && !assertVars.exists(v => v._2.isInstanceOf[StateType]))
      throw TypeException("Hyper assertions must quantifier over states. ")

    val originalAssertVars = assertVars
    assertVars = assertVars ++ assertVarDecls.map(decl => decl.vName.name -> decl.vType).toMap
    // AssertVar will appear in the body. Update the assertVars map before type checking the body
    typeCheckExpr(body, inHyperAssertion)
    res = checkIfTypeMatch(body.typ, boolType)
    assertVars = originalAssertVars
    res
  }

  def checkIfTypeMatch(t1: Type, t2: Type): Boolean = {
    (t1.isInstanceOf[IntType] && t2.isInstanceOf[IntType]) ||
      (t1.isInstanceOf[BoolType] && t2.isInstanceOf[BoolType]) ||
      (t1.isInstanceOf[StateType] && t2.isInstanceOf[StateType]) ||
      (t1.isInstanceOf[StmtBlockType] && t2.isInstanceOf[StmtBlockType])
  }

}
