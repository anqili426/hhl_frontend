package viper.HHLVerifier

import viper.HHLVerifier.comm.SymbolCheckerError

object SymbolChecker {
  // This map is used to keep track of the declared program variables + assertion variables for each method
  var allVars: Map[String, Type] = Map.empty  // All variables used in one method (including method arguments, block names), used to collect all identifiers defined
  var allVarsInCurrScope: Map[String, Type] = Map.empty // All variables available in the current scope
  var allArgNames: Set[String] = Set.empty  // All arguments of one method
  var allMethodNames: Seq[String] = List.empty  // All method names of one program
  var allMethods: Seq[Method] = Seq.empty // All methods of one program
  var allHintNames: Set[String] = Set.empty // All hints declared in one program
  var allHintsInMethod: Set[String] = Set.empty // All hints declared in one method

  def reset(): Unit = {
    allVars = Map.empty
    allVarsInCurrScope = Map.empty
    allArgNames = Set.empty
    allMethods = Seq.empty
    allMethodNames = List.empty
    allHintNames = Set.empty
    allHintsInMethod = Set.empty
  }

  def checkSymbolsProg(p: HHLProgram): Unit = {
    // Check that each method has a unique identifier
    allMethods = p.content
    allMethodNames = p.content.map(m => m.mName)
    val dupMethodNames = allMethodNames.diff(allMethodNames.distinct)
    if (dupMethodNames.size > 0) {
      val m = allMethods.filter(m => m.mName == dupMethodNames(0))(0)

      throw SymbolCheckerError("Duplicate method name", m.offsetLeft, m.offsetRight)
    }
    p.content.foreach(checkSymbolsMethod)
  }

  def checkSymbolsMethod(m: Method): Unit = {
    var varsAllowedInPost: Map[String, Type] = Map.empty
    m.params.foreach(a => {
      checkIdDup(a)
      allVarsInCurrScope = allVarsInCurrScope + (a.name -> a.typ)
      allVars = allVars + (a.name -> a.typ)
      varsAllowedInPost = varsAllowedInPost + (a.name -> a.typ)
    })
    allArgNames = m.paramsMap.keySet
    m.pre.foreach(p => checkSymbolsExpr(p, false, false))
    // The return variables can only be referred to in the method body or postconditions
    m.res.foreach { r =>
      checkIdDup(r)
      allVarsInCurrScope = allVarsInCurrScope + (r.name -> r.typ)
      allVars = allVars + (r.name -> r.typ)
      varsAllowedInPost = varsAllowedInPost + (r.name -> r.typ)
    }
    checkSymbolsStmt(m.body)
    m.allVars = allVars

    // Because postconditions can contain hints declared in the method body
    // We must perform the symbol checking for postcondition after the symbol checking for method body
    // Note that now allVars must be updated to contain only the args and return variables
    allVars = varsAllowedInPost
    m.post.foreach(p => checkSymbolsExpr(p, false, false))

    // Reset
    allVars = Map.empty
    allVarsInCurrScope = Map.empty
    allHintsInMethod = Set.empty
  }

  // Returns
  // 1. Sequence of all program variables that appear in the statement
  // 2. Sequence of all program variables that are modified in the statement
  def checkSymbolsStmt(stmt: Stmt): (Seq[(String, Type)], Seq[(String, Type)]) = {
    stmt match {
      case cs@CompositeStmt(stmts) =>
        val varsBeforeNewScope = allVarsInCurrScope
        var res1: Seq[(String, Type)] = Seq.empty
        var res2: Seq[(String, Type)] = Seq.empty
        stmts.foreach(s => {
          val res = checkSymbolsStmt(s)
          res1 = res1 ++ res._1
          res2 = res2 ++ res._2
        })
        allVarsInCurrScope = varsBeforeNewScope
        cs.allProgVars = res1.distinct.toMap
        cs.modifiedProgVars = res2.distinct.toMap
        (res1.distinct, res2.distinct)

      case PVarDecl(id, typ) =>
        checkIdDup(id)
        allVars = allVars + (id.name -> typ)
        allVarsInCurrScope = allVarsInCurrScope + (id.name -> typ)
        (Seq((id.name, typ)), Seq.empty)

      case ex@ProofVarDecl(pv, p) =>
        checkIdDup(pv)
        allVars = allVars + (pv.name -> pv.typ)
        allVarsInCurrScope = allVarsInCurrScope + (pv.name -> pv.typ)
        val allVarsInP = checkSymbolsExpr(p, false, false)
        if (allVarsInP.filter(v => pv.name == v._1).isEmpty) {
          throw SymbolCheckerError("The proof variable " + pv.name + " must appear on the right-hand side of the statement", pv.offsetLeft, pv.offsetRight)
        }
        (allVarsInP, Seq.empty)

      case stmt@AssignStmt(id, exp) =>
        // Do not allow assignment to method arguments
        if (allArgNames.contains(id.name)) throw SymbolCheckerError("Cannot reassign to method argument " + id.name, stmt.offsetLeft, stmt.offsetRight)
        val rightVars = checkSymbolsExpr(exp, false, false)
        val idAssignedTo = checkSymbolsExpr(id, false, false)
        (idAssignedTo ++ rightVars, idAssignedTo)

      case stmt@MultiAssignStmt(left, right) =>
        val idAssignedTo = left.map(id => checkSymbolsExpr(id, false, false)).flatten
        val idAssignedToNames = left.map(id => id.name)
        if (idAssignedToNames.toSet.size != idAssignedToNames.length) throw SymbolCheckerError("A variable cannot appear on the RHS of an assignment more than once", stmt.offsetLeft, stmt.offsetRight) //throw SymbolCheckerError("A variable cannot appear on the RHS of an assignment more than once", stmt)
        val args = checkSymbolsExpr(right, false, false)
        val argNames = right.args.map(a => a.name)
        idAssignedToNames.foreach(
          id => {
            if (allArgNames.contains(id)) throw SymbolCheckerError("Cannot reassign to method argument " + id, stmt.offsetLeft, stmt.offsetRight) //throw IllegalAssignmentException("Cannot reassign to method argument " + id)
            if (argNames.contains(id)) throw SymbolCheckerError("Cannot assign to variables that are used as arguments in a method call in the same statement", stmt.offsetLeft, stmt.offsetRight) // throw IllegalAssignmentException("Cannot assign to variables that are used as arguments in a method call in the same statement")
          }
        )
        val numRet = right.method.res.length
        if (left.length != numRet) throw SymbolCheckerError("The call to method " + right.methodName + " should be assigned to exactly " + numRet + " variables.", stmt.offsetLeft, stmt.offsetRight)// throw UnknownException("The call to method " + right.methodName + " should be assigned to exactly " + numRet + " variables. ")
        val resNames = right.method.res.map(r => r.name)
        right.paramsToArgs = right.paramsToArgs ++ resNames.zip(idAssignedToNames).toMap
        (idAssignedTo, args)

      case HavocStmt(id, hintDecl) =>
        if (allArgNames.contains(id.name)) throw SymbolCheckerError("Cannot reassign to method argument " + id.name, stmt.offsetLeft, stmt.offsetRight) // throw IllegalAssignmentException("Cannot reassign to method argument " + id.name)
        if (!hintDecl.isEmpty) checkHintDecl(hintDecl.get)
        val idAssignedTo = checkSymbolsExpr(id, false, false)
        (idAssignedTo, idAssignedTo)

      case AssumeStmt(e) =>
        (checkSymbolsExpr(e, false, false), Seq.empty)

      case AssertStmt(e) =>
        (checkSymbolsExpr(e, false, false), Seq.empty)

      case HyperAssumeStmt(e) =>
        (checkSymbolsExpr(e, false, false), Seq.empty)

      case HyperAssertStmt(e) =>
        (checkSymbolsExpr(e, false, false), Seq.empty)

      case stmt@IfElseStmt(cond, ifBlock, elseBlock) =>
        val declareStmts = ifBlock.stmts.filter(s => s.isInstanceOf[DeclareStmt])
        val reuseStmts = elseBlock.stmts.filter(s => s.isInstanceOf[ReuseStmt])
        val numOfDeclareStmts = declareStmts.size
        val numOfReuseStmts = reuseStmts.size
        if (numOfDeclareStmts > 1) throw SymbolCheckerError("There can be at most 1 declare statement in an if-block", stmt.offsetLeft, stmt.offsetRight) // throw UnknownException("There can be at most 1 declare statement in an if-block")
        if (numOfReuseStmts > 1) throw SymbolCheckerError("There can be at most 1 reuse statement in an else-block", stmt.offsetLeft, stmt.offsetRight) // throw UnknownException("There can be at most 1 reuse statement in an else-block")
        if (numOfDeclareStmts != numOfReuseStmts) throw SymbolCheckerError("Declare & reuse statements must both exist", stmt.offsetLeft, stmt.offsetRight) //throw UnknownException("Declare & reuse statements must both exist")

        // Check that the reuse statement is using the identifier of the matching declare statement
        if (numOfDeclareStmts == 1) {
          val declareStmt = declareStmts(0).asInstanceOf[DeclareStmt]
          val reuseStmt = reuseStmts(0).asInstanceOf[ReuseStmt]
          checkIdDup(declareStmt.blockName)
          allVars = allVars + (declareStmt.blockName.name -> declareStmt.blockName.typ)
          if (declareStmt.stmts.stmts.size == 0) throw SymbolCheckerError("Declare statement block cannot be empty", stmt.offsetLeft, stmt.offsetRight) // throw UnknownException("Declare statement block cannot be empty")
          if (reuseStmt.blockName.name != declareStmt.blockName.name) throw SymbolCheckerError("Reuse statement must refer to the matching declare statement", stmt.offsetLeft, stmt.offsetRight) // throw UnknownException("Reuse statement must refer to the matching declare statement")
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
        (Seq.empty, Seq.empty)

      case loop@WhileLoopStmt(cond, body, inv, decr, _) =>
        val allHintDecls = inv.map(i => i._1).filter(h => !h.isEmpty)
        allHintDecls.foreach(h => checkHintDecl(h.get))
        // When using the sync rule/forall-exists rule, loop invariants cannot use the loop index
        var allVarsOfLoop = checkSymbolsExpr(cond, false, false) ++ inv.map(i => checkSymbolsExpr(i._2, loop.rule=="desugaredRule", false)).flatten
        if (!decr.isEmpty) allVarsOfLoop = allVarsOfLoop ++ checkSymbolsExpr(decr.get, false, false)
        // Body must be checked after loop condition and invariants are checked
        val bodyVars = checkSymbolsStmt(body)
        allVarsOfLoop = allVarsOfLoop ++ bodyVars._1
        // The following assignment cannot be removed
        // body.allProgVars must contain all program variables in the loop guard, invariant & loop body
        body.allProgVars = allVarsOfLoop.distinct.toMap
        (allVarsOfLoop, bodyVars._2)

      case stmt@FrameStmt(framedAssertion, body) =>
        val framedVars = checkSymbolsExpr(framedAssertion, false, true)
        val allBodyVars = checkSymbolsStmt(body)
        val framedVarsModified = framedVars.intersect(allBodyVars._2)
        // Make sure that the program variables in the frame are not modified in the body
        if (framedVarsModified.size > 0) throw SymbolCheckerError("Variables " + framedVarsModified + " in framed assertions cannot be modified.", stmt.offsetLeft, stmt.offsetRight) // throw UnknownException("Variables " + framedVarsModified + " in framed assertions cannot be modified. ")
        (framedVars ++ allBodyVars._1, allBodyVars._2)

      case UseHintStmt(hint) =>
        checkIfHintUseWellformed(hint)
        val varsInHint = checkSymbolsExpr(hint, false, false)
        (varsInHint, Seq.empty)

      case stmt@MethodCallStmt(name, args) =>
        if (!allMethodNames.contains(name)) throw SymbolCheckerError("Method " + name + " is undefined, so it cannot be called", stmt.offsetLeft, stmt.offsetRight) // throw UnknownException("Method " + name + " is undefined, so it cannot be called")
        stmt.method = allMethods.find(m => m.mName == name).get
        if (stmt.method.params.length != args.length) throw SymbolCheckerError("Call to method " + name + " has an unexpected number of arguments", stmt.offsetLeft, stmt.offsetRight) // throw UnknownException("Call to method " + name + " has an unexpected number of arguments")
        val varsInArgs = args.map(a => checkSymbolsExpr(a, false, false)).flatten
        if (stmt.method.res.length > 0) throw SymbolCheckerError("The call to method " + name + " should be assigned to exactly " + stmt.method.res.length + " variables.", stmt.offsetLeft, stmt.offsetRight) // throw UnknownException("The call to method " + name + " should be assigned to exactly " + stmt.method.res.length + " variables. ")
        val argNames = args.map(a => a.name)
        val paramNames = stmt.method.params.map(p => p.name)
        stmt.paramsToArgs = paramNames.zip(argNames).toMap
        (varsInArgs, Seq.empty)

      case stmt => throw SymbolCheckerError("Statement " + stmt + " is of unexpected type " + stmt.getClass(), stmt.offsetLeft, stmt.offsetRight) // throw UnknownException("Statement " + stmt + " is of unexpected type " + stmt.getClass)
    }
  }

    // isInLoopInv: indicates whether exp is part of a loop invariant
    // isFrame: indicates whether exp is part of a framed assertion -- used to check whether state-exists-expression can appear in exp
    // Returns a sequence of all program variables that appear in the expression
    // TODO: Modify Lookupexpr in order add proof variables
    def checkSymbolsExpr(exp: Expr, isInLoopInv: Boolean, isFrame: Boolean): Seq[(String, Type)] = {
      exp match {
        case id@Id(_) => // This is identifier used. Id in variable declarations are not checked here
          checkIdDefined(id)
          Seq((id.name, allVarsInCurrScope.get(id.name).get))
        case av@AssertVar(_) =>
          checkIdDefined(av)
          Seq.empty
        case pv@ProofVar(name) =>
          checkIdDefined(pv)
          Seq((name, allVars.get(name).get))
        case AssertVarDecl(vName, vType) =>
          checkIdDup(vName)
          allVars = allVars + (vName.name -> vType)
          allVarsInCurrScope = allVarsInCurrScope + (vName.name -> vType)
          Seq.empty
        case Num(_) => Seq.empty
        case BoolLit(_) => Seq.empty
        case BinaryExpr(left, _, right) =>
            checkSymbolsExpr(left, isInLoopInv, isFrame) ++ checkSymbolsExpr(right, isInLoopInv, isFrame)
        case UnaryExpr(_, e) => checkSymbolsExpr(e, isInLoopInv, isFrame)
        case ImpliesExpr(left, right) =>
            // State-exists-expressions can appear on the left-hand side of an implication, so isFrame is fixed as false here
            checkSymbolsExpr(left, isInLoopInv, false) ++ checkSymbolsExpr(right, isInLoopInv, isFrame)
        case Assertion(quantifier, assertVars, body) =>
          val originalAllVars = allVars
          val originalAllVarsInScope = allVarsInCurrScope
          // Assertion variables will be added to the symbol table
          assertVars.foreach(v => checkSymbolsExpr(v, isInLoopInv, isFrame))
          val varsInBody = checkSymbolsExpr(body, isInLoopInv, isFrame)
          // Remove the assertion variables from the symbol table
          allVars = originalAllVars
          allVarsInCurrScope = originalAllVarsInScope
          varsInBody
        /*case GetValExpr(state, id) =>
            checkIdDefined(state)
            checkIdDefined(id)
          var varsInExpr = Seq((id.name, allVarsInCurrScope.get(id.name).get))
          if (state.isInstanceOf[ProofVar]) varsInExpr = varsInExpr :+ (state.idName, allVarsInCurrScope.get(state.idName).get)
          varsInExpr*/
        case LookupExpr(id, ind) =>
          var varsInExpr = checkSymbolsExpr(id, isInLoopInv, isFrame) ++ checkSymbolsExpr(ind, isInLoopInv, isFrame)
          if (id.isInstanceOf[ProofVar]) varsInExpr = varsInExpr :+ (id.asInstanceOf[ProofVar].idName, allVarsInCurrScope.get(id.asInstanceOf[ProofVar].idName).get)
          varsInExpr
        case expr@StateExistsExpr(state, _) =>
            if (isFrame) throw SymbolCheckerError("Framed assertion cannot include state-exists-expression", expr.offsetLeft, expr.offsetRight) // throw UnknownException("Framed assertion cannot include state-exists-expression")
            checkIdDefined(state)
            if (state.isInstanceOf[ProofVar]) Seq((state.idName, allVarsInCurrScope.get(state.idName).get))
            else Seq.empty  // No need to return anything if it's an assertion variable
        case expr@LoopIndex() =>
            if (!isInLoopInv) throw SymbolCheckerError("Loop index $n can only appear in the invariant of a loop that does not use the sync rule", expr.offsetLeft, expr.offsetRight) // throw UnknownException("Loop index $n can only appear in the invariant of a loop that does not use the sync rule")
            Seq.empty
        case h@Hint(_, arg) =>
            checkHintDefined(h)
            val varsInArg = checkSymbolsExpr(arg, isInLoopInv, isFrame)
            varsInArg
        case expr@MethodCallExpr(name, args) =>
            if (!allMethodNames.contains(name)) throw SymbolCheckerError("Method " + name + " is undefined, so it cannot be called", expr.offsetLeft, expr.offsetRight) // throw UnknownException("Method " + name + " is undefined, so it cannot be called")
            expr.method = allMethods.find(m => m.mName == name).get
            if (expr.method.params.length != args.length) throw SymbolCheckerError("Call to method " + name + " has an unexpected number of arguments", expr.offsetLeft, expr.offsetRight) // throw UnknownException("Call to method " + name + " has an unexpected number of arguments")
            val varsInArgs = args.map(a => checkSymbolsExpr(a, false, false)).flatten
            val argNames = args.map(a => a.name)
            val paramNames = expr.method.params.map(p => p.name)
            expr.paramsToArgs = paramNames.zip(argNames).toMap
            varsInArgs
        case SeqAssignExpr(elements) =>
          elements.foldRight(Seq.empty[(String, Type)]) {
            case (l, r) => r ++ checkSymbolsExpr(l, isInLoopInv, isFrame)
          }
        case SetAssignExpr(elements) =>
          elements.foldRight(Seq.empty[(String, Type)]) {
            case (l, r) => r ++ checkSymbolsExpr(l, isInLoopInv, isFrame)
          }
        case MapAssignExpr(elements) =>
          elements.foldRight(Seq.empty[(String, Type)]) {
            case (l, r) => r ++ checkSymbolsExpr(l.k, isInLoopInv, isFrame) ++ checkSymbolsExpr(l.v, isInLoopInv, isFrame)
          }
        case LengthExpr(id) => checkSymbolsExpr(id, isInLoopInv, isFrame)
        case UpdateMapExpr(id, update) => checkSymbolsExpr(id, isInLoopInv, isFrame) ++ checkSymbolsExpr(update, isInLoopInv, isFrame)
        case MapTupleExpr(k, v) => checkSymbolsExpr(k, isInLoopInv, isFrame) ++ checkSymbolsExpr(v, isInLoopInv, isFrame)
        case CombExpr(lhs, rhs, _) => checkSymbolsExpr(lhs, isInLoopInv, isFrame) ++ checkSymbolsExpr(rhs, isInLoopInv, isFrame)
        case expr => throw SymbolCheckerError("Symbol checker: Expression " + exp + " is of unexpected type " + exp.getClass(), expr.offsetLeft, expr.offsetRight) // throw UnknownException("Symbol checker: Expression " + exp + " is of unexpected type " + exp.getClass)
      }
    }

    def checkIdDup(id: Expr): Unit = {
      val idName = getIdName(id)
      val allNames = allVars.keySet ++ allMethodNames ++ allHintNames
      if (allNames.contains(idName)) throw SymbolCheckerError("Duplicate identifier " + idName, id.offsetLeft, id.offsetRight) // throw DuplicateIdentifierException("Duplicate identifier " + idName)
    }

    def checkHintDefined(hint: Hint): Unit = {
      if (!allHintsInMethod.contains(hint.name)) throw SymbolCheckerError("Hint " + hint.name + " not found", hint.offsetLeft, hint.offsetRight) // throw IdentifierNotFoundException("Hint " + hint.name + " not found")
    }

    def checkIdDefined(id: Expr): Unit = {
      val idName = getIdName(id)
      if (!allVarsInCurrScope.contains(idName)) throw SymbolCheckerError("Identifier " + idName + " not found", id.offsetLeft, id.offsetRight) // throw SymbolCheckerError("Identifier not found", id.offsetLeft, id.offsetRight) // throw IdentifierNotFoundException("Identifier " + idName + " not found")
    }

    def getIdName(id: Expr): String = {
      id match {
        case Id (name) => name
        case AssertVar(name) => name
        case AssertVarDecl (vName, _) => vName.name
        case ProofVar(name) => name
        case HintDecl(name) => name
        case Hint(name, _) => name
        case _ => throw SymbolCheckerError("In getIdName(id: Expr): Expression " + id + " is of unexpected type " + id.getClass, id.offsetLeft, id.offsetRight) // throw UnknownException("In getIdName(id: Expr): Expression " + id + " is of unexpected type " + id.getClass)
      }
    }

    def checkHintDecl(decl: HintDecl): Unit = {
      // Check that the hint name is distinct
      checkIdDup(decl)
      // Update the hint set
      allHintNames = allHintNames + decl.name
      allHintsInMethod = allHintsInMethod + decl.name
    }

    def checkIfHintUseWellformed(hint: Expr): Unit = {
      def checkIfHintOnly(e: Expr): Boolean = {
        e match {
          case Hint(_, _) => true
          case BinaryExpr(e1, _, e2) => checkIfHintOnly(e1) && checkIfHintOnly(e2)
          case ImpliesExpr(left, right) => checkIfHintOnly(right) // TODO: need to improve this
          case _ => false
        }
      }

      var res = false
      hint match {
        case Hint(_, _) => res = true
        case be@BinaryExpr(_, _, _) => res = checkIfHintOnly(be)
        case Assertion(quantifier, _, body) =>
          res = (quantifier == "forall" && body.isInstanceOf[ImpliesExpr] &&
            checkIfHintOnly(body.asInstanceOf[ImpliesExpr].right))
        case _ =>
      }
      if (!res) throw SymbolCheckerError("The expression in the use statement is not well-formed:\n " + hint + "\nExpected syntax: use <hints> or use forall: ... ==> <hints>", hint.offsetLeft, hint.offsetRight) // throw UnknownException("The expression in the use statement is not well-formed:\n " +
    }
}