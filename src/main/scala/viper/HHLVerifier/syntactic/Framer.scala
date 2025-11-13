package viper.HHLVerifier.syntactic

import viper.HHLVerifier.ast._
import viper.HHLVerifier.syntactic.PathBuilder.CharPath
import viper.HHLVerifier.syntactic.SyntacticEngine.Triple
import viper.HHLVerifier.syntactic.handler.IfElseHandler.{varsRead, varsWritten}
import viper.HHLVerifier.typing.StateType

object Framer {
  def frameMethod(method: Method, split: Seq[Triple]): Seq[Triple] = {
    val withPropagatedPres = propagatePre(method, split)
    addPrevAliases(method, withPropagatedPres)
  }

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

  private def containsStateExistential(e: Expr): Boolean = e match {
    case Id(_) | Num(_) | BoolLit(_) | LookupExpr(_, _) | StateExistsExpr(_, _) | AssertVar(_) => false
    case BinaryExpr(e1, _, e2) => containsStateExistential(e1) || containsStateExistential(e2)
    case UnaryExpr(_, e) => containsStateExistential(e)
    case ImpliesExpr(left, right) => containsStateExistential(left) || containsStateExistential(right)
    case Assertion("exists", vars, _) if vars.exists(_.vType == StateType()) => true
    case Assertion(_, _, body) => containsStateExistential(body)
  }

  private def addPrevAliases(method: Method, split: Seq[Triple]): Seq[Triple] = {
    // We keep track of the aliases we have until now
    // variable -> List[(path condition, rhs expression)]
    var aliases: Map[Id, Seq[(Expr, Expr)]] = Map.empty

    // Exclude all variables that are assigned through MultiAssignStmt --> they cannot be trusted
    val blockList = assignedByMultiAssign(method.body)

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

  private def assignedByMultiAssign(s: Stmt): Set[Id] = s match {
    case AssignStmt(_, _) => Set.empty
    case MultiAssignStmt(left, _) => left.toSet
    case IfElseStmt(_, ifStmt, elseStmt) => assignedByMultiAssign(ifStmt) ++ assignedByMultiAssign(elseStmt)
    case CompositeStmt(stmts) => stmts.flatMap(assignedByMultiAssign).toSet
    case WhileLoopStmt(_, body, _, _, _) => assignedByMultiAssign(body)
    case _ => Set.empty
  }
}
