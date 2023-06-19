package viper.HHLVerifier

object SymbolChecker {
  // This map is used to keep track of the declared program variables + assertion variables for each method
  var allVars: Map[String, Type] = Map.empty  // All variables used in one method
  var allArgNames: Set[String] = Set.empty  // All arguments of one method
  var allMethodNames: Seq[String] = List.empty  // All method names of one program

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
    m.pre.foreach(p => checkSymbolsExpr(p, false, false))
    // The return variables can only be referred to in the method body or postconditions
    allVars = allVars ++ m.res.map(r => r.name -> r.typ)
    m.post.foreach(p => checkSymbolsExpr(p, false, false))
    checkSymbolsStmt(m.body)
    m.allVars = allVars
    // Reset
    allVars = Map.empty
  }

  // Returns
  // 1. Sequence of all program variables that appear in the statement
  // 2. Sequence of all program variables that are modified in the statement
  def checkSymbolsStmt(stmt: Stmt): (Seq[(String, Type)], Seq[(String, Type)]) = {
    stmt match {
      case cs@CompositeStmt(stmts) =>
        var res1: Seq[(String, Type)] = Seq.empty
        var res2: Seq[(String, Type)] = Seq.empty
        stmts.foreach(s => {
          val res = checkSymbolsStmt(s)
          res1 = res1 ++ res._1
          res2 = res2 ++ res._2
        })
        cs.allProgVars = res1.distinct.toMap
        cs.modifiedProgVars = res2.distinct.toMap
        (res1.distinct, res2.distinct)
      case PVarDecl(id, typ) =>
        checkIdDup(id)
        allVars = allVars + (id.name -> typ)
        (Seq((id.name, typ)), Seq.empty)
      case as@AssignStmt(id, exp) =>
        // Do not allow assignment to method arguments
        if (allArgNames.contains(id.name)) throw IllegalAssignmentException("Cannot reassign to method argument " + id.name)
        val rightVars = checkSymbolsExpr(exp, false, false)
        // TODO: the following assignment can be removed, since as.IdsOnRHS is not used any more
        as.IdsOnRHS = rightVars.map(tuple => tuple._1)
        val idAssignedTo = checkSymbolsExpr(id, false, false)
        (idAssignedTo ++ rightVars, idAssignedTo)

      case HavocStmt(id) =>
        if (allArgNames.contains(id.name)) throw IllegalAssignmentException("Cannot reassign to method argument " + id.name)
        val idAssignedTo = checkSymbolsExpr(id, false, false)
        (idAssignedTo, idAssignedTo)

      case AssumeStmt(e) =>
        (checkSymbolsExpr(e, false, false), Seq.empty)

      case AssertStmt(e) =>
        (checkSymbolsExpr(e, false, false), Seq.empty)

      case IfElseStmt(cond, ifBlock, elseBlock) =>
        val declareStmts = ifBlock.stmts.filter(s => s.isInstanceOf[DeclareStmt])
        val reuseStmts = elseBlock.stmts.filter(s => s.isInstanceOf[ReuseStmt])
        val numOfDeclareStmts = declareStmts.size
        val numOfReuseStmts = reuseStmts.size
        if (numOfDeclareStmts > 1) throw UnknownException("There can be at most 1 declare statement in an if-block")
        if (numOfReuseStmts > 1) throw UnknownException("There can be at most 1 reuse statement in an else-block")
        if (numOfDeclareStmts != numOfReuseStmts) throw UnknownException("Declare & reuse statements must both exist")

        // Check that the reuse statement is using the identifier of the matching declare statement
        if (numOfDeclareStmts == 1) {
          val declareStmt = declareStmts(0).asInstanceOf[DeclareStmt]
          val reuseStmt = reuseStmts(0).asInstanceOf[ReuseStmt]
          checkIdDup(declareStmt.blockName)
          allVars = allVars + (declareStmt.blockName.name -> declareStmt.blockName.typ)
          if (declareStmt.stmts.stmts.size == 0) throw UnknownException("Declare statement block cannot be empty")
          if (reuseStmt.blockName.name != declareStmt.blockName.name) throw UnknownException("Reuse statement must refer to the matching declare statement")
          reuseStmt.reusedBlock = declareStmt.stmts
        }

        val condSymbols = checkSymbolsExpr(cond, false, false)
        val ifSymbols = checkSymbolsStmt(ifBlock)
        val elseSymbols = checkSymbolsStmt(elseBlock)
        (condSymbols ++ ifSymbols._1 ++ elseSymbols._1, ifSymbols._2 ++ elseSymbols._2)

      case DeclareStmt(_, stmts) =>
        // blockName should have been checked before reaching here
        val allSymbols = checkSymbolsStmt(stmts)
        (allSymbols._1, allSymbols._2)

      case ReuseStmt(_) =>
        // blockName should have been checked before reaching here
        // TODO: should we return the symbols in the reused block?
        (Seq.empty, Seq.empty)

      case WhileLoopStmt(cond, body, inv) =>
        val bodyVars = checkSymbolsStmt(body)
        val allVars = checkSymbolsExpr(cond, false, false) ++ inv.map(i => checkSymbolsExpr(i, true, false)).flatten ++ bodyVars._1
        // The following assignment cannot be removed
        // body.allProgVars must contain all program variables in the loop guard, invariant & loop body
        body.allProgVars = allVars.distinct.toMap
        (allVars, bodyVars._2)
      case FrameStmt(framedAssertion, body) =>
        val framedVars = checkSymbolsExpr(framedAssertion, false, true)
        val allBodyVars = checkSymbolsStmt(body)
        val framedVarsModified = framedVars.intersect(allBodyVars._2)
        // Make sure that the program variables in the frame are not modified in the body
        if (framedVarsModified.size > 0) throw UnknownException("Variables " + framedVarsModified + " in framed assertions cannot be modified. ")
        (framedVars ++ allBodyVars._1, allBodyVars._2)
      case _ =>
        throw UnknownException("Statement " + stmt + " is of unexpected type " + stmt.getClass)
    }
  }

    // isInLoopInv: indicates whether exp is part of a loop invariant
    // isFrame: indicates whether exp is part of a framed assertion -- used to check whether state-exists-expression can appear in exp
    // Returns a sequence of all program variables that appear in the expression
    def checkSymbolsExpr(exp: Expr, isInLoopInv: Boolean, isFrame: Boolean): Seq[(String, Type)] = {
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
            checkSymbolsExpr(left, isInLoopInv, isFrame) ++ checkSymbolsExpr(right, isInLoopInv, isFrame)
        case UnaryExpr(_, e) => checkSymbolsExpr(e, isInLoopInv, isFrame)
        case ImpliesExpr(left, right) =>
            // State-exists-expressions can appear on the left-hand side of an implication, so isFrame is fixed as false here
            checkSymbolsExpr(left, isInLoopInv, false) ++ checkSymbolsExpr(right, isInLoopInv, isFrame)
        case Assertion(_, assertVars, body) =>
          val originalTable = allVars
          // Assertion variables will be added to the symbol table
          assertVars.foreach(v => checkSymbolsExpr(v, isInLoopInv, isFrame))
          val varsInBody = checkSymbolsExpr(body, isInLoopInv, isFrame)
          // Remove the assertion variables from the symbol table
          allVars = originalTable
          varsInBody
        case GetValExpr(state, id) =>
            checkIdDefined(state)
            checkIdDefined(id)
            Seq((id.name, allVars.get(id.name).get))
        case StateExistsExpr(state) =>
            if (isFrame) throw UnknownException("Framed assertion cannot include state-exists-expression")
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