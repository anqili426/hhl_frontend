package viper.HHLVerifier

object TypeChecker {
  val boolOp = List("==", "!=", "&&", "!!", "forall", "exists", "implies")
  val boolOpForNums = List(">=", "<=", ">", "<", "==", "!=")
  val numOp = List("+", "-", "*", "/")
  val boolType = TypeInstance.boolType
  val intType = TypeInstance.intType
  val stateType = TypeInstance.stateType

  var assertVars: Map[String, Type] = Map.empty

  def typeCheckProg(p: HHLProgram): Boolean = {
    typeCheckStmt(p.stmts)
  }

  def typeCheckStmt(s: Stmt): Boolean = {
    var res = true
    s match {
      case CompositeStmt(stmts) =>
        stmts.foreach(stmt => res = res && typeCheckStmt(stmt))
      case AssignStmt(left, right) =>
        res = typeCheckExpr(left) && typeCheckExpr(right) && checkIfTypeMatch(left.typ, right.typ)
      case HavocStmt(id) =>
        res = typeCheckExpr(id)
      case AssumeStmt(e) =>
        res = typeCheckExpr(e) && checkIfTypeMatch(e.typ, boolType)
      case AssertStmt(e) =>
        res = typeCheckExpr(e) && checkIfTypeMatch(e.typ, boolType)
      case IfElseStmt(cond, ifStmt, elseStmt) =>
        res = typeCheckExpr(cond) && checkIfTypeMatch(cond.typ, boolType)
        res = res && typeCheckStmt(ifStmt) && typeCheckStmt(elseStmt)
      case WhileLoopStmt(cond, body, inv) =>
        res = typeCheckExpr(cond) && checkIfTypeMatch(cond.typ, boolType)
        inv.foreach(i => res = res && typeCheckExpr(i) && checkIfTypeMatch(i.typ, boolType))
        res = res && typeCheckStmt(body)
      case PVarDecl(vName, vType) =>
        vName.typ = vType
        res = true
    }
    if (!res) throw TypeException("The statement has a type error: " + s)
    res
  }

  def typeCheckExpr(e: Expr): Boolean = {
    var res = true
    e match {
      case id@Id(_) =>
        if (SymbolChecker.allVars.contains(id.name)) id.typ = SymbolChecker.allVars.get(id.name).get
        else res = false
      case be@BinaryExpr(e1, op, e2) =>
        res = typeCheckExpr(e1) && typeCheckExpr(e2)
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
          res = typeCheckExpr(e) && checkIfTypeMatch(e.typ, boolType)
          ue.typ = boolType
        } else if (op == "-") {
          res = typeCheckExpr(e) && checkIfTypeMatch(e.typ, intType)
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
        vName.typ = vType
      // AssertVarDecl expression itself doesn't have a concrete type
      case ie@ImpliesExpr(left, right) =>
        res = typeCheckExpr(left) && typeCheckExpr(right)
        res = res && checkIfTypeMatch(left.typ, boolType) && checkIfTypeMatch(right.typ, boolType)
        ie.typ = boolType
      case ee@ExistsExpr(assertVarDecls, body) =>
        res = typeCheckQuantifierExprHelper(assertVarDecls, body)
        ee.typ = boolType
      case fe@ForAllExpr(assertVarDecls, body) =>
        res = typeCheckQuantifierExprHelper(assertVarDecls, body)
        fe.typ = boolType
      case gve@GetValExpr(state, id) =>
        res = typeCheckExpr(state) && typeCheckExpr(id) && checkIfTypeMatch(state.typ, stateType)
        gve.typ = id.typ
    }
    if (!res) throw TypeException("The expression has a type error: " + e)
    res
  }

  def typeCheckQuantifierExprHelper(assertVarDecls: Seq[AssertVarDecl], body: Expr): Boolean = {
    var res = true
    assertVarDecls.foreach(decl => res = res && typeCheckExpr(decl))
    val originalAssertVars = assertVars
    assertVars = assertVars ++ assertVarDecls.map(decl => decl.vName.name -> decl.vType).toMap
    // AssertVar will appear in the body. Update the assertVars map before type checking the body
    res = res && typeCheckExpr(body) && checkIfTypeMatch(body.typ, boolType)
    assertVars = originalAssertVars
    res
  }

  def checkIfTypeMatch(t1: Type, t2: Type): Boolean = {
    (t1.isInstanceOf[IntType] && t2.isInstanceOf[IntType]) ||
      (t1.isInstanceOf[BoolType] && t2.isInstanceOf[BoolType]) ||
      (t1.isInstanceOf[StateType] && t2.isInstanceOf[StateType])
  }

}
