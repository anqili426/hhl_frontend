package viper.HHLVerifier.syntactic

import viper.HHLVerifier.ast._
import viper.HHLVerifier.syntactic.SyntacticEngine.Triple
import viper.HHLVerifier.syntactic.handler.IfElseHandler.{varsRead, varsWritten}
import viper.HHLVerifier.typing.StateType

object Framer {
  def frameMethod(method: Method, split: Seq[Triple]): Seq[Triple] = {
    propagatePre(method, split)
  }

  private def propagatePre(method: Method, split: Seq[Triple]): Seq[Triple] = {
    // we track the set of preconditions we are propagating throughout the method
    var active: Seq[(Expr, Set[Id])] = Seq.empty

    split.map { triple =>
      // Add active preconditions to the triple
      val propagatedPres: Seq[Expr] = active.map(_._1)
      val newPre: Seq[Expr] = triple.pre ++ propagatedPres

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
}
