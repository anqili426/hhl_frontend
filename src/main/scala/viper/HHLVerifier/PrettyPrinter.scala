package viper.HHLVerifier

object PrettyPrinter {

  def printStmt(stmt: Stmt): String = {
    stmt match {
      case CompositeStmt(stmts) =>
        stmts.map(s => printStmt(s)).mkString("\n")
      case AssignStmt(left, right) =>
        printExpr(left) + " := " + printExpr(right)
      case MultiAssignStmt(left, right) =>
        left.map(l => printExpr(l)).mkString(", ") + " := " + printExpr(right)
      case HavocStmt(id, hintDecl) =>
        if (hintDecl.isEmpty) "havoc " + printExpr(id)
        else "havoc " + printExpr(id) + " (" + printExpr(hintDecl.get) + ")"
      case AssumeStmt(e) => "assume " + printExpr(e)
      case AssertStmt(e) => "assert " + printExpr(e)
      case HyperAssumeStmt(e) => "hyperAssume " + printExpr(e)
      case HyperAssertStmt(e) => "hyperAssert " + printExpr(e)
      case IfElseStmt(cond, ifStmt, elseStmt) =>
        val ifStmtStr = "if ( " + printExpr(cond) + " ) {\n" + printStmt(ifStmt) + "\n}"
        val elseStmtStr = if (!elseStmt.stmts.isEmpty) "" else " else {\n" + printStmt(elseStmt) + "\n}"
        ifStmtStr + elseStmtStr
      case WhileLoopStmt(cond, body, inv, decr, rule) =>
        val ruleStr = if (rule == "unspecified") "" else rule
        val condStr = "while " + ruleStr + " ( " + printExpr(cond) + " ) {\n"
        val invStr = if (inv.isEmpty) "" else inv.map(i => "invariant " + printExpr(i._2) + "\n").mkString
        val decrStr = if (decr.isEmpty) "" else "decreases " + printExpr(decr.get) + "\n"
        condStr + invStr + decrStr + "{\n" + printStmt(body) + "\n}"
      case PVarDecl(vName, vType) =>
        "var " + printExpr(vName) + ": " + printType(vType)
      case ProofVarDecl(proofVar, p) =>
        "let " + printExpr(proofVar) + " :: " + printExpr(p)
      case FrameStmt(framedAssertion, body) =>
        "frame " + printExpr(framedAssertion) + " {\n" + printStmt(body) + "\n}"
      case DeclareStmt(blockName, stmts) =>
        "declare " + printExpr(blockName) + " {\n" + printStmt(stmts) + "\n}"
      case ReuseStmt(blockName) => "reuse " + printExpr(blockName)
      case UseHintStmt(hint) => "use " + printExpr(hint)
      case MethodCallStmt(methodName, args) => methodName + "(" + args.map(a => printExpr(a)).mkString(", ") + ")"
    }
  }

  def printExpr(expr: Expr): String = {
    expr match {
      case Id(name) => name
      case AssertVar(name) => name
      case ProofVar(name) => name
      case AssertVarDecl(vName, vType) => vName + ": " + printType(vType)
      case Num(value) => value.toString
      case BoolLit(value) => value.toString
      case BinaryExpr(e1, op, e2) => "(" + printExpr(e1) + ") " + op + " (" + printExpr(e2) + ")"
      case UnaryExpr(op, e) => op + "(" + printExpr(e) + ")"
      case ImpliesExpr(left, right) => "(" + printExpr(left) + ") ==> (" + printExpr(right) + ")"
      case Assertion(quantifier, assertVarDecls, body) =>
        quantifier + assertVarDecls.map(a => printExpr(a)).mkString(", ") + " :: (" + printExpr(body) + ")"
      case GetValExpr(state, id) => printExpr(state) + "[" + printExpr(id) + "]"
      case StateExistsExpr(state, err) => if (err) "<<" + printExpr(state) + ">>" else "<" + printExpr(state) + ">"
      case LoopIndex() => "$n"
      case HintDecl(name) => "(" + name + ")"
      case Hint(name, arg) => name + "(" + printExpr(arg) + ")"
      case MethodCallExpr(methodName, args) => methodName + "(" + args.map(a => printExpr(a)).mkString(", ") + ")"
    }
  }

  def printType(typ: Type): String = {
    typ match {
      case UnknownType() => "Unknown"
      case IntType() => "Int"
      case BoolType() => "Bool"
      case StateType() => "State"
      case StmtBlockType() => "StmtBlock"
    }
  }
}