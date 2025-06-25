package viper.HHLVerifier.syntactic

import viper.HHLVerifier.ast._
import Characterizer._

object WeakestPrecondition {
  /**
   * Computes the '''weakest precondition (WP)''' for a given program (described by a characterizer) and
   * given postconditions.
   *
   * @param characterizer characterizer, characterizing all execution paths of a program.
   * @param post          non-empty sequence of postconditions.
   * @return              an [[Expr]] that is the '''weakest precondition''' for the given
   *                      program and postconditions.
   * @throws java.lang.RuntimeException if `post` is empty.
   */
  def compute(characterizer: Characterizer, post: Seq[Expr]): Expr = post match {
    case Nil => sys.error("WeakestPrecondition: No postcondition given")
    case _ => post
      .map(x => computeSinglePost(characterizer, x))
      .reduceLeft((acc,x) => BinaryExpr(acc, "&&", x))
  }

  /**
   * Helper function computing the '''weakest precondition (WP)''' for a given characterizer and
   * a ''single'' postcondition.
   */
  private def computeSinglePost(characterizer: Characterizer, post: Expr): Expr = {
    implicit val c: Characterizer = characterizer

    post match {
      case Assertion("forall", assertVarDecls, body) => {
        Assertion("forall", assertVarDecls,
          characterizer // TODO: which AssertVar to take when there are multiple in assert statement?
            .map { case CharPath(pc, subst) => (substitutePathCondition(pc, assertVarDecls.last.vName), substituteExprPath(body, subst, assertVarDecls.map { case AssertVarDecl(x, _) => x })) }
            .map(x => ImpliesExpr(x._1, x._2))
            .reduceLeft[Expr]((acc, e) => BinaryExpr(acc, "&&", e))
        )
      }
      case Assertion("exists", assertVarDecls, body) => {
        Assertion("exists", assertVarDecls,
          characterizer
            .map { case CharPath(pc, subst) => (substitutePathCondition(pc, assertVarDecls.last.vName), substituteExprPath(body, subst, assertVarDecls.map { case AssertVarDecl(x, _) => x })) }
            .map(x => BinaryExpr(x._1, "&&", x._2))
            .reduceLeft[Expr]((acc, e) => BinaryExpr(acc, "||", e))
        )
      }
    }
  }

  /**
   * Helper function substituting all variables in an assertion for a given path and given assertion variables.
   * The substitution is only taking place if we encounter a [[LookupExpr]] for one of the variables in `assertVars.
   * Otherwise, the substitution will be (or has been) handled by another quantifier.
   */
  private def substituteExprPath(expr: Expr, map: Map[Id, Expr], assertVars: Seq[AssertVar])(implicit c: Characterizer): Expr = expr match {
    case Assertion(quantifier, assertVarDecls, body) => {
      val substitutedOuter = Assertion(quantifier, assertVarDecls, substituteExprPath(body, map, assertVars))
      computeSinglePost(c, substitutedOuter)
    }
    case BinaryExpr(e1, op, e2) => BinaryExpr(substituteExprPath(e1, map, assertVars), op, substituteExprPath(e2, map, assertVars))
    case UnaryExpr(op, e) => UnaryExpr(op, substituteExprPath(e, map, assertVars))
    case ImpliesExpr(left, right) => ImpliesExpr(substituteExprPath(left, map, assertVars), substituteExprPath(right, map, assertVars))
    case le@LookupExpr(id, index) => {
      if (assertVars.contains(id)) LookupExpr(id, Characterizer.applySubstitution(index, map))
      else le
    }
    case _ => expr // TODO: Double-check which other Expr are possible
  }

  /**
   * Helper function substituting the path condition for a given state. In particular, identifiers are
   * substituted for a [[LookupExpr]] for the particular state. This is, because we need to make sure that
   * every variable reference in the path condition is bound to a state.
   */
  private def substitutePathCondition(pc: Expr, state: AssertVar): Expr = pc match {
    case Id(_) => LookupExpr(state, pc)
    case Num(_) | BoolLit(_) => pc
    case BinaryExpr(e1, op, e2) => BinaryExpr(substitutePathCondition(e1, state), op, substitutePathCondition(e2, state))
    case UnaryExpr(op, e) => UnaryExpr(op, substitutePathCondition(e, state))
    case ImpliesExpr(left, right) => ImpliesExpr(substitutePathCondition(left, state), substitutePathCondition(right, state))
    case _ => sys.error("WeakestPrecondition: Yet unsupported expression in path-condition substitution: " + state.toString) // TODO: Check which other expressions could be assigned
  }
}
