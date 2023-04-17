package viper.HHLVerifier

object SymbolChecker {
  var allVars: Map[String, Type] = Map.empty
  def checkSymbolsProg(p: HHLProgram): Unit = {
    checkSymbolsStmt(p.stmts)
  }

  def checkSymbolsStmt(stmt: Stmt): Unit = {
    stmt match {
      case CompositeStmt(stmts) => stmts.foreach(s => checkSymbolsStmt(s))
      case PVarDecl(id, typ) =>
        checkIdDup(id)
        allVars = allVars + (id.name -> typ)
      case AssignStmt(id, exp) =>
        checkSymbolsExpr(id)
        checkSymbolsExpr(exp)
      case HavocStmt(id) =>
        checkSymbolsExpr(id)
      case AssumeStmt(e) =>
        checkSymbolsExpr(e)
      case AssertStmt(e) =>
        checkSymbolsExpr(e)
      case IfElseStmt(cond, ifBlock, elseBlock) =>
        checkSymbolsExpr(cond)
        checkSymbolsStmt(ifBlock)
        checkSymbolsStmt(elseBlock)
      case WhileLoopStmt(cond, body, inv) =>
        checkSymbolsExpr(cond)
        inv.foreach(i => checkSymbolsExpr(i))
        checkSymbolsStmt(body)
      case _ =>
        throw UnknownException("Statement " + stmt + " is of unexpected type " + stmt.getClass)
    }

    def checkSymbolsExpr(exp: Expr): Unit = {
      exp match {
        case id@Id(_) => // This is identifier used. Id in variable declarations are not checked here
          checkIdDefined(id)
        case av@AssertVar(_) => checkIdDefined(av)
        case AssertVarDecl(vName, vType) =>
          checkIdDup(vName)
          allVars = allVars + (vName.name -> vType)
          case Num(_) =>
          case BoolLit(_) =>
          case BinaryExpr(left, _, right) =>
            checkSymbolsExpr(left)
            checkSymbolsExpr(right)
          case UnaryExpr(_, e) => checkSymbolsExpr(e)
          case ImpliesExpr(left, right) =>
            checkSymbolsExpr(left)
            checkSymbolsExpr(right)
        case ForAllExpr(assertVars, body) =>
            val originalTable = allVars
            // Assertion variables will be added to the symbol table
            assertVars.foreach(v => checkSymbolsExpr(v))
            checkSymbolsExpr(body)
            // Remove the assertion variables from the symbol table
            allVars = originalTable
       case ExistsExpr(assertVars, body) =>
            val originalTable = allVars
            assertVars.foreach(v => checkSymbolsExpr(v))
            checkSymbolsExpr(body)
            allVars = originalTable
        case _ =>
          throw UnknownException("Expression " + exp + " is of unexpected type " + exp.getClass)
      }
    }

    def checkIdDup(id: Expr): Unit = {
      val idName = getIdName(id)
      if (allVars.contains(idName)) throw DuplicateIdentifierException("Duplicate identifier " + idName)
    }

    def checkIdDefined(id: Expr): Unit = {
      val idName = getIdName(id)
      if (!allVars.contains(idName)) throw IdentifierNotFoundException("Identifier " + idName + " not found")
    }

    def getIdName(id: Expr): String = {
      id match {
        case Id (name) => name
        case AssertVar(name) => name
        case AssertVarDecl (vName, _) => vName.name
        case _ =>
          throw UnknownException("In getIdName(id: Expr): Expression " + id + " is of unexpected type " + stmt.getClass)
      }
    }
  }

}