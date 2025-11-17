package viper.HHLVerifier.syntactic

import viper.HHLVerifier.ast._
import viper.HHLVerifier.syntactic.PathBuilder.CharPath
import viper.HHLVerifier.syntactic.SyntacticEngine.Triple
import viper.HHLVerifier.syntactic.handler.IfElseHandler.{varsRead, varsWritten}
import viper.HHLVerifier.typing.StateType

object Framer {

  /**
   * Applies framing to a method's split verification triples.
   *
   * Framing consists of two phases:
   *
   *  - [[propagatePre]]: preconditions that are not invalidated by later
   *     assignments are propagated forward across triples of the same method.
   *     This effectively threads "stable" assumptions through the entire
   *     method.
   *  - [[addPrevAliases]]: path-sensitive aliases (simple equalities of the
   *     form `x := rhs`) discovered in earlier triples are turned into
   *     explicit preconditions for later triples. These aliasing
   *     preconditions act as frame conditions that relate the current state
   *     of variables to their previously computed values.
   *
   * @param method the method for which the triples were generated.
   * @param split the sequence of loop-free verification triples obtained
   *              from the method (e.g. via structural splitting).
   * @return the same triples as were passed with `split` with enriched preconditions.
   *         The statements and postconditions of the triples are not modified.
   */
  def frameMethod(method: Method, split: Seq[Triple]): Seq[Triple] = {
    val withPropagatedPres = propagatePre(method, split)
    addPrevAliases(method, withPropagatedPres)
  }

  /**
   * Part 1 of framing: Propagates stable preconditions forward across a method’s triples.
   *
   * A precondition is considered stable and is propagated (i.e. it serves as an invariant), as long as it:
   *  - doesn't contain a state-existential assertion (in case of a non-terminating call
   *    the existence of a state after the call cannot be guaranteed)
   *  - doesn't refer to a variable that is modified in the code before the triple (this modification
   *    might invalidate the precondition).
   */
  private def propagatePre(method: Method, split: Seq[Triple]): Seq[Triple] = {
    // We track the set of preconditions we are propagating throughout the method
    var active: Seq[(Expr, Set[Id])] = Seq.empty

    split.map { triple =>
      // Add active preconditions to the triple
      val propagatedPres: Seq[Expr] = active.map(_._1)
      val newPre: Seq[Expr] = (triple.pre ++ propagatedPres).distinct

      // Update active precondition set for the next triple
      val newCandidates: Seq[(Expr, Set[Id])] = triple.pre
        .filterNot(containsStateExistential)
        .map(e => (e, varsRead(e)))
      val allCandidatesBefore: Seq[(Expr, Set[Id])] = active ++ newCandidates

      // If candidates mention modified variables, they may no longer hold
      val modifiedHere = varsWritten(triple.stmt)
      active = allCandidatesBefore.filter { case (_, fv) =>
        (fv intersect modifiedHere).isEmpty
      }

      triple.copy(pre = newPre)
    }
  }

  /**
   * Helper method to check whether an expression contains an existential
   * quantification over a state variable.
   */
  private def containsStateExistential(e: Expr): Boolean = e match {
    case Id(_) | Num(_) | BoolLit(_) | LookupExpr(_, _) | StateExistsExpr(_, _) | AssertVar(_) => false
    case BinaryExpr(e1, _, e2) => containsStateExistential(e1) || containsStateExistential(e2)
    case UnaryExpr(_, e) => containsStateExistential(e)
    case ImpliesExpr(left, right) => containsStateExistential(left) || containsStateExistential(right)
    case Assertion("exists", vars, _) if vars.exists(_.vType == StateType()) => true
    case Assertion(_, _, body) => containsStateExistential(body)
  }

  /**
   * Part 2 of framing: Augments triples with alias-based frame conditions derived from
   * previous statements in the method.
   *
   * For each triple:
   *  - It identifies which aliases happening before the triple are relevant for it by checking
   *    whether the aliased variable occurs in the triple's pre- or postcondition.
   *  - For each relevant alias it generates a universally quantified frame assertion,
   *    also including the path condition of the alias. This information is determined
   *    with a [[PathBuilder.Characterizer]].
   *  - The generated frame assertions are appended to the triple's pre.
   *
   * Variables that appear on the left-hand side of any [[MultiAssignStmt]] in the
   * method body are not considered in the alias map. They originate from method calls and hence
   * don't allow trivial syntactic reasoning.
   */
  private def addPrevAliases(method: Method, split: Seq[Triple]): Seq[Triple] = {
    // We keep track of the aliases we have until now
    // variable -> List[(path condition, rhs expression)]
    var aliases: Map[Id, Seq[(Expr, Expr)]] = Map.empty

    // Exclude all variables that are assigned through MultiAssignStmt --> they cannot be trusted
    val blockList = assignedByMultiAssignOrHavoc(method.body)

    split.map { triple =>
      // First, incorporate the previous aliases into the triple
      val varsUsedInPost = triple.post.flatMap(varsRead).toSet
      val varsUsedInPre = triple.pre.flatMap(varsRead).toSet
      val applicableAliases = aliases.filter(x => varsUsedInPost.contains(x._1) || varsUsedInPre.contains(x._1))
      val additionalPre = applicableAliases.flatMap { case (x, aliasList) =>
        aliasList.map { case (pc, rhs) =>
          val assertVar = AssertVar("_intState")
          Assertion("forall", List(AssertVarDecl(assertVar, StateType())),
            ImpliesExpr(
              StateExistsExpr(assertVar, false),
              ImpliesExpr(
                WeakestPrecondition.substitutePathCondition(pc, assertVar),
                BinaryExpr(
                  LookupExpr(assertVar, x),
                  "==",
                  WeakestPrecondition.substitutePathCondition(rhs, assertVar)
                )
              )
            )
          )
        }
      }
      val newPre = triple.pre ++ additionalPre

      // Then, collect the new aliases from this triple to pass them on to the next triple
      val characterizer = PathBuilder.characterizeStmt(triple.stmt)
      val newAliasPairs = for {
        CharPath(pc, subst) <- characterizer.paths
        (x, rhs) <- subst
      } yield x -> (pc, rhs)
      val newAliases = newAliasPairs.groupMap(_._1)(_._2)

      aliases = (aliases ++ newAliases) -- blockList

      triple.copy(pre = newPre)
    }
  }

  /**
   * Helper function to collect all variables that are ever assigned
   * through a [[MultiAssignStmt]] or [[HavocStmt]] in a statement.
   */
  private def assignedByMultiAssignOrHavoc(s: Stmt): Set[Id] = s match {
    case AssignStmt(_, _) => Set.empty
    case MultiAssignStmt(left, _) => left.toSet
    case HavocStmt(id, _) => Set(id)
    case IfElseStmt(_, ifStmt, elseStmt) => assignedByMultiAssignOrHavoc(ifStmt) ++ assignedByMultiAssignOrHavoc(elseStmt)
    case CompositeStmt(stmts) => stmts.flatMap(assignedByMultiAssignOrHavoc).toSet
    case WhileLoopStmt(_, body, _, _, _) => assignedByMultiAssignOrHavoc(body)
    case _ => Set.empty
  }
}
