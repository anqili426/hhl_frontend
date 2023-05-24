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
    m.pre.foreach(p => typeCheckExpr(p, true))
    m.post.foreach(p => typeCheckExpr(p, true))
    typeCheckStmt(m.body)
  }

  def typeCheckStmt(s: Stmt): Boolean = {
    var res = true
    s match {
      case CompositeStmt(stmts) =>
        stmts.foreach(stmt => res = res && typeCheckStmt(stmt))
      case AssignStmt(left, right) =>
        res = typeCheckExpr(left, false) && typeCheckExpr(right, false) && checkIfTypeMatch(left.typ, right.typ)
      case HavocStmt(id) =>
        res = typeCheckExpr(id, false)
      case AssumeStmt(e) =>
        res = typeCheckExpr(e, false) && checkIfTypeMatch(e.typ, boolType)
      case AssertStmt(e) =>
        res = typeCheckExpr(e, false) && checkIfTypeMatch(e.typ, boolType)
      case IfElseStmt(cond, ifStmt, elseStmt) =>
        res = typeCheckExpr(cond, false) && checkIfTypeMatch(cond.typ, boolType)
        res = res && typeCheckStmt(ifStmt) && typeCheckStmt(elseStmt)
      case DeclareStmt(blockId, stmts) =>
        res = checkIfTypeMatch(blockId.typ, blockType)
        res = res && typeCheckStmt(stmts)
      case ReuseStmt(blockId) =>
        res = checkIfTypeMatch(blockId.typ, blockType)
      case WhileLoopStmt(cond, body, inv) =>
        res = typeCheckExpr(cond, false) && checkIfTypeMatch(cond.typ, boolType)
        inv.foreach(i => res = res && typeCheckExpr(i, true) && checkIfTypeMatch(i.typ, boolType))
        res = res && typeCheckStmt(body)
      case FrameStmt(framedAssertion, body) =>
        res = typeCheckExpr(framedAssertion, true) && checkIfTypeMatch(framedAssertion.typ, boolType)
        res = res && typeCheckStmt(body)
      case PVarDecl(vName, vType) =>
        vName.typ = vType
        res = true
    }
    if (!res) throw TypeException("The statement has a type error: " + s)
    res
  }

  def typeCheckExpr(e: Expr, inHyperAssertion: Boolean): Boolean = {
    var res = true
    e match {
      case id@Id(_) =>
        if (inHyperAssertion) throw TypeException("Program variables cannot appear in a hyper assertion")
        if (currMethod.allVars.contains(id.name)) id.typ = currMethod.allVars.get(id.name).get
        else res = false
      case be@BinaryExpr(e1, op, e2) =>
        res = typeCheckExpr(e1, inHyperAssertion) && typeCheckExpr(e2, inHyperAssertion)
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
          res = typeCheckExpr(e, inHyperAssertion) && checkIfTypeMatch(e.typ, boolType)
          ue.typ = boolType
        } else if (op == "-") {
          res = typeCheckExpr(e, inHyperAssertion) && checkIfTypeMatch(e.typ, intType)
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
        if (!inHyperAssertion && vType.isInstanceOf[StateType]) throw TypeException("Variables of type State can only appear in a hyper assertion. ")
        vName.typ = vType
      // AssertVarDecl expression itself doesn't have a concrete type
      case ie@ImpliesExpr(left, right) =>
        res = typeCheckExpr(left, inHyperAssertion) && typeCheckExpr(right, inHyperAssertion)
        res = res && checkIfTypeMatch(left.typ, boolType) && checkIfTypeMatch(right.typ, boolType)
        ie.typ = boolType
      case ast@Assertion(_, assertVarDecls, body) =>
        res = typeCheckAssertionHelper(assertVarDecls, body, inHyperAssertion)
        ast.typ = boolType
      case gve@GetValExpr(state, id) =>
        if (!inHyperAssertion) throw TypeException("Expression " + gve + " can only appear in a hyper assertion. ")
        // When type checking for id in a GetValExpr, fix inHyperAssertion to be false to avoid exceptions
        // Any other occurrence of Id instances should be type checked with the correct inHyperAssertion flag
        res = typeCheckExpr(state, inHyperAssertion) && typeCheckExpr(id, false) && checkIfTypeMatch(state.typ, stateType)
        gve.typ = id.typ
      case se@StateExistsExpr(state) =>
        if (!inHyperAssertion) throw TypeException("Expression " + se + " can only appear in a hyper assertion. ")
        res = typeCheckExpr(state, inHyperAssertion) && checkIfTypeMatch(state.typ, stateType)
        se.typ = boolType
      case li@LoopIndex() =>
        li.typ = intType
    }
    if (!res) throw TypeException("The expression has a type error: " + e)
    res
  }

  def typeCheckAssertionHelper(assertVarDecls: Seq[AssertVarDecl], body: Expr, inHyperAssertion: Boolean): Boolean = {
    var res = true
    assertVarDecls.foreach(decl => res = res && typeCheckExpr(decl, inHyperAssertion))
    if (inHyperAssertion
        && !assertVarDecls.exists(decl => decl.vType.isInstanceOf[StateType])
        && !assertVars.exists(v => v._2.isInstanceOf[StateType]))
      throw TypeException("Hyper assertions must quantifier over states. ")

    val originalAssertVars = assertVars
    assertVars = assertVars ++ assertVarDecls.map(decl => decl.vName.name -> decl.vType).toMap
    // AssertVar will appear in the body. Update the assertVars map before type checking the body
    res = res && typeCheckExpr(body, inHyperAssertion) && checkIfTypeMatch(body.typ, boolType)
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
