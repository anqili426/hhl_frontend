package viper.HHLVerifier

object SymbolChecker {
  // This map is used to keep track of the declared program variables + assertion variables for each method
  var allVars: Map[String, Type] = Map.empty
  var allArgNames: Set[String] = Set.empty
  var allMethodNames: Seq[String] = List.empty

  def checkSymbolsProg(p: HHLProgram): Unit = {
    // Check that each method has a unique identifier
    allMethodNames = p.content.map(m => m.mName)
    val dupMethodNames = allMethodNames.diff(allMethodNames.distinct)
    if (dupMethodNames.size > 0) throw DuplicateIdentifierException("Duplicate method name " + dupMethodNames)
    p.content.foreach(checkSymbolsMethod)
  }

  def checkSymbolsMethod(m: Method): Unit = {
    m.args.foreach(a => {
      checkIdDup(a)
      allVars = allVars + (a.name -> a.typ)
    })
    allArgNames = m.argsMap.keySet
    m.pre.foreach(p => checkSymbolsExpr(p, false))
    // The return variables can only be referred to in the method body or postconditions
    allVars = allVars ++ m.res.map(r => r.name -> r.typ)
    m.post.foreach(p => checkSymbolsExpr(p, false))
    checkSymbolsStmt(m.body)
    m.allVars = allVars
    // Reset
    allVars = Map.empty
  }

  def checkSymbolsStmt(stmt: Stmt): Seq[(String, Type)] = {
    stmt match {
      case cs@CompositeStmt(stmts) =>
        var res: Seq[(String, Type)] = Seq.empty
        stmts.foreach(s => res = res ++ checkSymbolsStmt(s))
        cs.allProgVars = res.distinct.toMap
        res.distinct
      case PVarDecl(id, typ) =>
        checkIdDup(id)
        allVars = allVars + (id.name -> typ)
        Seq((id.name, typ))
      case as@AssignStmt(id, exp) =>
        // Do not allow assignment to method arguments
        if (allArgNames.contains(id.name)) throw IllegalAssignmentException("Cannot reassign to method argument " + id.name)
        val rightVars = checkSymbolsExpr(exp, false)
        as.IdsOnRHS = rightVars.map(tuple => tuple._1)
        checkSymbolsExpr(id, false) ++ rightVars
      case HavocStmt(id) =>
        if (allArgNames.contains(id.name)) throw IllegalAssignmentException("Cannot reassign to method argument " + id.name)
        checkSymbolsExpr(id, false)
      case AssumeStmt(e) =>
        checkSymbolsExpr(e, false)
      case AssertStmt(e) =>
        checkSymbolsExpr(e, false)
      case IfElseStmt(cond, ifBlock, elseBlock) =>
        checkSymbolsExpr(cond, false) ++ checkSymbolsStmt(ifBlock) ++ checkSymbolsStmt(elseBlock)
      case WhileLoopStmt(cond, body, inv, frame) =>
        val framedVars = frame.map(f => checkSymbolsExpr(f, false)).flatten
        val bodyVars = checkSymbolsStmt(body)
        val framedVarsInBody = framedVars.intersect(bodyVars)
        if (framedVarsInBody.size > 0) throw UnknownException("Variables " + framedVarsInBody + " in framed assertions are also used in the loop body. ")
        val allVars = checkSymbolsExpr(cond, false) ++ inv.map(i => checkSymbolsExpr(i, true)).flatten ++ bodyVars
        body.allProgVars = allVars.distinct.toMap // Contains all program variables in the loop guard, invariant & loop body
        allVars
      case _ =>
        throw UnknownException("Statement " + stmt + " is of unexpected type " + stmt.getClass)
    }
  }

    def checkSymbolsExpr(exp: Expr, isInLoopInv: Boolean): Seq[(String, Type)] = {
      exp match {
        case id@Id(_) => // This is identifier used. Id in variable declarations are not checked here
          checkIdDefined(id)
          Seq((id.name, allVars.get(id.name).get))
        case av@AssertVar(_) =>
          checkIdDefined(av)
          Seq.empty
        case AssertVarDecl(vName, vType) =>
          checkIdDup(vName)
          allVars = allVars + (vName.name -> vType)
          Seq.empty
        case Num(_) => Seq.empty
        case BoolLit(_) => Seq.empty
        case BinaryExpr(left, _, right) =>
            checkSymbolsExpr(left, isInLoopInv) ++ checkSymbolsExpr(right, isInLoopInv)
        case UnaryExpr(_, e) => checkSymbolsExpr(e, isInLoopInv)
        case ImpliesExpr(left, right) =>
            checkSymbolsExpr(left, isInLoopInv) ++ checkSymbolsExpr(right, isInLoopInv)
        case Assertion(_, assertVars, body) =>
          val originalTable = allVars
          // Assertion variables will be added to the symbol table
          assertVars.foreach(v => checkSymbolsExpr(v, isInLoopInv))
          val varsInBody = checkSymbolsExpr(body, isInLoopInv)
          // Remove the assertion variables from the symbol table
          allVars = originalTable
          varsInBody
        case GetValExpr(state, id) =>
            checkIdDefined(state)
            checkIdDefined(id)
            Seq((id.name, allVars.get(id.name).get))
        case StateExistsExpr(state) =>
            checkIdDefined(state)
            Seq.empty
        case LoopIndex() =>
            if (!isInLoopInv) throw UnknownException("Loop index $n can only be used in a loop invariant")
            Seq.empty
        case _ =>
          throw UnknownException("Expression " + exp + " is of unexpected type " + exp.getClass)
      }
    }

    def checkIdDup(id: Expr): Unit = {
      val idName = getIdName(id)
      if (allVars.contains(idName) || allMethodNames.contains(idName)) throw DuplicateIdentifierException("Duplicate identifier " + idName)
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
          throw UnknownException("In getIdName(id: Expr): Expression " + id + " is of unexpected type " + id.getClass)
      }
    }


}