package viper.HHLVerifier.syntactic

import viper.HHLVerifier.ast._
import Characterizer._
import viper.HHLVerifier.typing.StateType

import scala.collection.immutable.{AbstractSeq, LinearSeq}
import scala.xml.NodeSeq

object WeakestPrecondition {
  /**
   * Computes the '''weakest precondition (WP)''' for a given program (described by a characterizer) and
   * given postconditions. Each assertion occurring in the WP quantifies over only one state variable.
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
    val normalizedPost: Expr = desugarQuantifiers(post) // to correctly compute the WP, it is handy to have chains of single-variable quantifiers
    normalizedPost match {
      case Assertion("forall", assertVarDecls@List(AssertVarDecl(assertVar, StateType())), body) => {
        Assertion("forall", assertVarDecls,
          characterizer
            .map { case CharPath(pc, subst) => (substitutePathCondition(pc, assertVar), substituteExprPath(body, subst, assertVar)) }
            .map(x => ImpliesExpr(x._1, x._2))
            .reduceLeft[Expr]((acc, e) => BinaryExpr(acc, "&&", e))
        )
      }
      case Assertion("exists", assertVarDecls@List(AssertVarDecl(assertVar, StateType())), body) => {
        Assertion("exists", assertVarDecls,
          characterizer
            .map { case CharPath(pc, subst) => (substitutePathCondition(pc, assertVar), substituteExprPath(body, subst, assertVar)) }
            .map(x => BinaryExpr(x._1, "&&", x._2))
            .reduceLeft[Expr]((acc, e) => BinaryExpr(acc, "||", e))
        )
      }
      case Assertion(quantifier, assertVarDecls, body) => Assertion(quantifier, assertVarDecls, computeSinglePost(c, body)) // quantifier over non-state variable
      case BinaryExpr(e1, op, e2) => BinaryExpr(computeSinglePost(c, e1), op, computeSinglePost(c, e2))
      case UnaryExpr(op, e) => UnaryExpr(op, computeSinglePost(c, e))
      case ImpliesExpr(left, right) => ImpliesExpr(computeSinglePost(c, left), computeSinglePost(c, right))
      case LookupExpr(_, _) => sys.error("WeakestPrecondition: Unquantified LookupExpr found")
      case _ => post
    }
  }

  /**
   * Helper function substituting all variables in an assertion for a given path and a given assertion variable.
   * The substitution is only taking place if we encounter a [[LookupExpr]] for the `assertVar`.
   * Otherwise, the substitution will be (or has been) handled by another quantifier.
   */
  private def substituteExprPath(expr: Expr, map: Map[Id, Expr], assertVar: AssertVar)(implicit c: Characterizer): Expr = expr match {
    case Assertion(quantifier, assertVarDecls, body) => {
      val substitutedOuter = Assertion(quantifier, assertVarDecls, substituteExprPath(body, map, assertVar))
      computeSinglePost(c, substitutedOuter)
    }
    case BinaryExpr(e1, op, e2) => BinaryExpr(substituteExprPath(e1, map, assertVar), op, substituteExprPath(e2, map, assertVar))
    case UnaryExpr(op, e) => UnaryExpr(op, substituteExprPath(e, map, assertVar))
    case ImpliesExpr(left, right) => ImpliesExpr(substituteExprPath(left, map, assertVar), substituteExprPath(right, map, assertVar))
    case LookupExpr(id, index) if id == assertVar => LookupExpr(assertVar, Characterizer.applySubstitution(index, map)) // only perform substitution, if assertVar matches
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

  /**
   * Converts every multi-variable quantifier into an equivalent chain of single-variable quantifiers.
   * This normalization is later needed for computing the weakest precondition.
   */
  def desugarQuantifiers(e: Expr): Expr = e match {
    case Assertion(quantifier, x1 :: (x2 :: xs), ImpliesExpr(stateExists, realBody)) => { // if we have multiple state assert vars, we also want to separate StateExistsExpr
      val extracted = extractFirstFromNestedAnd(stateExists)
      Assertion(quantifier, List(x1), ImpliesExpr(extracted._1, desugarQuantifiers(Assertion(quantifier, (x2 :: xs), ImpliesExpr(extracted._2, realBody)))))
    }
    case Assertion(quantifier, assertVarDecls, body) => assertVarDecls match {
      case _ :: Nil => e // only one assertVar ==> already desugared, nothing more to do
      case x :: xs => Assertion(quantifier, List(x), desugarQuantifiers(Assertion(quantifier, xs, body))) // TODO: Support error states
    }
    case BinaryExpr(e1, op, e2) => BinaryExpr(desugarQuantifiers(e1), op, desugarQuantifiers(e2))
    case UnaryExpr(op, e) => UnaryExpr(op, desugarQuantifiers(e))
    case ImpliesExpr(left, right) => ImpliesExpr(desugarQuantifiers(left), desugarQuantifiers(right))
    case _ => e
  }

  /**
   * Helper function for [[desugarQuantifiers]] to extract the first element of a left-weighted
   * binary expression.
   *
   * @param e The binary expression to be split
   * @return A pair, where the first part is the extracted left-most expression, and the second part
   *         is the rest of the binary expression without the first element.
   */
  private def extractFirstFromNestedAnd(e: Expr): (Expr, Expr) = e match {
    case BinaryExpr(e1: BinaryExpr, "&&", e2) => {
      val res = extractFirstFromNestedAnd(e1)
      (res._1, BinaryExpr(res._2, "&&", e2))
    }
    case BinaryExpr(e1, "&&", e2) => (e1, e2)
  }
}
