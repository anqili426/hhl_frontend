package viper.HHLVerifier

object PrettyPrinter {

  // prints a statement by matching recursively on AST
  def formatStmt(stmt: Stmt): String = {
    stmt match {
      case CompositeStmt(stmts) => stmts.map(s => formatStmt(s)).mkString("\n")
      // Composite statement will be matched on individual parts
      case AssignStmt(left, right) =>
        // Assign Expression
        formatExpr(left) + " := " + formatExpr(right)
      case MultiAssignStmt(left, right) =>
        // Multi Assign Expression
        left.map(l => formatExpr(l)).mkString(", ") + " := " + formatExpr(right)
      case HavocStmt(id, hintDecl) =>
        // Havoc statement, optionally extended with a hint
        if (hintDecl.isEmpty) "havoc " + formatExpr(id)
        else "havoc " + formatExpr(id) + " (" + formatExpr(hintDecl.get) + ")"
      case AssumeStmt(e) => "assume " + formatExpr(e)
      // Assume statment
      case AssertStmt(e) => "assert " + formatExpr(e)
      // Assert statement
      case HyperAssumeStmt(e) => "hyperAssume " + formatExpr(e)
      // HyperAssume statement
      case HyperAssertStmt(e) => "hyperAssert " + formatExpr(e)
      // HyperAssert statement
      case IfElseStmt(cond, ifStmt, elseStmt) =>
        // If statement, creates condition and executable statement
        // May include else statement
        val ifStmtStr = "if ( " + formatExpr(cond) + " ) {\n" + formatStmt(ifStmt) + "\n}"
        val elseStmtStr = if (elseStmt.stmts.nonEmpty) "" else " else {\n" + formatStmt(elseStmt) + "\n}"
        ifStmtStr + elseStmtStr
      case WhileLoopStmt(cond, body, inv, decr, rule) =>
        // While Statement, includes (possibly) specified rule, condition, invariant, variant, body
        val ruleStr = if (rule == "unspecified") "" else rule
        val condStr = "while " + ruleStr + " ( " + formatExpr(cond) + " ) {\n"
        val invStr = if (inv.isEmpty) "" else inv.map(i => "invariant " + formatExpr(i._2) + "\n").mkString
        val decrStr = if (decr.isEmpty) "" else "decreases " + formatExpr(decr.get) + "\n"
        condStr + invStr + decrStr + "{\n" + formatStmt(body) + "\n}"
      case PVarDecl(vName, vType) =>
        // Variable declaration
        "var " + formatExpr(vName) + ": " + formatType(vType)
      case ProofVarDecl(proofVar, p) =>
        // Proof variable declaration
        "let " + formatExpr(proofVar) + " :: " + formatExpr(p)
      case FrameStmt(framedAssertion, body) =>
        // Frame declaration
        "frame " + formatExpr(framedAssertion) + " {\n" + formatStmt(body) + "\n}"
      case DeclareStmt(blockName, stmts) =>
        // declare statement
        "declare " + formatExpr(blockName) + " {\n" + formatStmt(stmts) + "\n}"
      case ReuseStmt(blockName) => "reuse " + formatExpr(blockName)
      case UseHintStmt(hint) => "use " + formatExpr(hint)
      case MethodCallStmt(methodName, args) => methodName + "(" + args.map(a => formatExpr(a)).mkString(", ") + ")"
    }
  }

  // prints expression by matching recursively on AST
  def formatExpr(expr: Expr): String = {
    expr match {
      case Id(name) => name
      case AssertVar(name) => name
      case ProofVar(name) => name
      case AssertVarDecl(vName, vType) => vName + ": " + formatType(vType)
      case Num(value) => value.toString
      case BoolLit(value) => value.toString
      case BinaryExpr(e1, op, e2) => "(" + formatExpr(e1) + ") " + op + " (" + formatExpr(e2) + ")"
      case UnaryExpr(op, e) => op + "(" + formatExpr(e) + ")"
      case ImpliesExpr(left, right) => "(" + formatExpr(left) + ") ==> (" + formatExpr(right) + ")"
      case Assertion(quantifier, assertVarDecls, body) =>
        quantifier + " " + assertVarDecls.map(a => "<" + formatExpr(a) + ">").mkString(", ") + " :: (" + formatExpr(body) + ")"
      case StateExistsExpr(state, err) => if (err) "<<" + formatExpr(state) + ">>" else "<" + formatExpr(state) + ">"
      case LoopIndex() => "$n"
      case HintDecl(name) => "(" + name + ")"
      case Hint(name, arg) => name + "(" + formatExpr(arg) + ")"
      case MethodCallExpr(methodName, args) => methodName + "(" + args.map(a => formatExpr(a)).mkString(", ") + ")"
      case SeqAssignExpr(elements) => "Seq(" + elements.foldLeft("")((a, b) => f"$a${formatExpr(b)}, ") + ")"
      case SetAssignExpr(elements) => "Set(" + elements.foldLeft("")((a, b) => f"$a${formatExpr(b)}, ") + ")"
      case MapAssignExpr(elements) => "Map(" + elements.foldLeft("")((a, b) => f"$a${formatExpr(b.k)} := ${formatExpr(b.v)}, ") + ")"
      case LookupExpr(id, ind) => f"${formatExpr(id)}[${formatExpr(ind)}]"
      case LengthExpr(id) => f"|${formatExpr(id)}|"
      case CombExpr(lhs, rhs, op) => f"${formatExpr(lhs)} ${op} ${formatExpr(rhs)}"
    }
  }

  // prints type by simple case distinction
  def formatType(typ: Type): String = {
    typ match {
      case t: UnknownType => "unknown"
      case t: IntType => "int"
      case t: BoolType => "bool"
      case t: StateType => "state"
      case t: StmtBlockType => "StmtBlock"
      case t: SetType => f"set_${formatType(t.sType)}_"
      case t: SeqType => f"seq_${formatType(t.sType)}_"
      case t: MapType => f"map_${formatType(t.kType)}1${formatType(t.vType)}_"
    }
  }

  def getErrorMessage(expr: Expr, source: String): String = {
    // determine position
    val (line, char) = findLineNumber(source, expr.pos)

    f"[$line:$char] ${expr.toString()}"
  }

  def findLineNumber(source: String, charPosition: Int): (Int, Int) = {
    val lines = source.split("\n")

    var currentCharCount = 0
    var lineNumber = 0

    for (i <- lines.indices) {
      currentCharCount += lines(i).length + 1

      if (currentCharCount > charPosition) {
        lineNumber = i + 1
        return (lineNumber, charPosition - currentCharCount + lines(i).length + 1)
      }
    }

    (lineNumber, charPosition - currentCharCount)
  }
}