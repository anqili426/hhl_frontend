package viper.HHLVerifier.syntactic

import viper.HHLVerifier.ast._
import PathBuilder._
import viper.HHLVerifier.typing.{StateType, IntType}

import scala.collection.immutable.{AbstractSeq, LinearSeq}
import scala.xml.NodeSeq

object WeakestPrecondition {

  /**
   * Computes the '''weakest precondition (WP)''' for a given program (described by a characterizer) and
   * given postconditions. Each assertion occurring in the WP quantifies over only one state variable.
   *
   * @param characterizer characterizer, characterizing all execution paths of a program.
   * @param post          non-empty sequence of postconditions.
   * @param wpPlus        boolean flag whether we want to compute extended WP for error states. The extended WP
   *                      has the purpose of propagating errors happening in triples before.
   * @return              an [[Expr]] that is the '''weakest precondition''' for the given
   *                      program and postconditions.
   * @throws java.lang.RuntimeException if `post` is empty.
   */
  def compute(characterizer: Characterizer, post: Seq[Expr], wpPlus: Boolean): Expr = post match {
    case Nil => sys.error("WeakestPrecondition: No postcondition given")
    case _ => post
      .map(x => computeSinglePost(characterizer, desugarQuantifiers(x))(wpPlus)) // to correctly compute the WP, it is handy to have chains of single-variable quantifiers
      .reduceLeft((acc,x) => BinaryExpr(acc, "&&", x))
  }

  /**
   * Helper function computing the '''weakest precondition (WP)''' for a given characterizer and
   * a ''single'' desugared postcondition.
   */
  private def computeSinglePost(characterizer: Characterizer, post: Expr)(implicit wpPlus: Boolean): Expr = {
    implicit val c: Characterizer = characterizer
    post match {
      // quantifiers over normal states
      case Assertion("forall", assertVarDecls@List(AssertVarDecl(assertVar, StateType())), ImpliesExpr(stateExists@StateExistsExpr(_, false), realBody)) => {
        Assertion("forall", assertVarDecls,
          ImpliesExpr(
            stateExists,
            addHavocQuantifiers(
              characterizer.paths
                .map { case CharPath(pc, subst) => (substitutePathCondition(pc, assertVar), substituteExprPath(realBody, subst, assertVar)(c, true)) }
                .map(x => ImpliesExpr(x._1, x._2))
                .reduceLeft[Expr]((acc, e) => BinaryExpr(acc, "&&", e)),
              characterizer.havocs, "forall", assertVar
            )
          )
        )
      }
      case Assertion("exists", assertVarDecls@List(AssertVarDecl(assertVar, StateType())), BinaryExpr(stateExists@StateExistsExpr(_, false), "&&", realBody)) => {
        Assertion("exists", assertVarDecls,
          BinaryExpr(
            stateExists, "&&",
            addHavocQuantifiers(
              characterizer.paths
                .map { case CharPath(pc, subst) => (substitutePathCondition(pc, assertVar), substituteExprPath(realBody, subst, assertVar)(c, true)) }
                .map(x => BinaryExpr(x._1, "&&", x._2))
                .reduceLeft[Expr]((acc, e) => BinaryExpr(acc, "||", e)),
              characterizer.havocs, "exists", assertVar
            )
          )
        )
      }
      // quantifiers over error states
      case Assertion("forall", assertVarDecls@List(AssertVarDecl(assertVar, StateType())), ImpliesExpr(stateExists@StateExistsExpr(specialId, true), realBody)) => {
        val classicWP = Assertion("forall", assertVarDecls,
          ImpliesExpr(
            StateExistsExpr(specialId, false), // error states get transformed to normal states
            addHavocQuantifiers(
              characterizer.asserts
                .map {
                  case (AssertStmt(e), paths) =>
                    paths.map {
                      case CharPath(pc, subst) => (
                        substitutePathCondition(pc, assertVar),
                        substitutePathCondition(applySubstitution(e, subst), assertVar),
                        substituteExprPath(realBody, subst, assertVar)(c, true)
                      )
                    }
                    .map(x => ImpliesExpr(BinaryExpr(x._1, "&&", UnaryExpr("!", x._2)), x._3))
                    .reduceLeft[Expr]((acc, e) => BinaryExpr(acc, "&&", e))
                }
                .foldLeft[Expr](BoolLit(true))((acc, e) => BinaryExpr(acc, "&&", e)),
              characterizer.havocs, "forall", assertVar
            )
          )
        )
        if (wpPlus) {
          BinaryExpr(
            classicWP, "&&",
            post
          )
        } else classicWP
      }
      case Assertion("exists", assertVarDecls@List(AssertVarDecl(assertVar, StateType())), BinaryExpr(stateExists@StateExistsExpr(specialId, true), "&&", realBody)) => {
        val classicWP = Assertion("exists", assertVarDecls,
          BinaryExpr(
            StateExistsExpr(specialId, false), "&&", // error states get transformed to normal states
            addHavocQuantifiers(
              characterizer.asserts
                .map {
                  case (AssertStmt(e), paths) =>
                    paths.map {
                        case CharPath(pc, subst) => (
                          substitutePathCondition(pc, assertVar),
                          substitutePathCondition(applySubstitution(e, subst), assertVar),
                          substituteExprPath(realBody, subst, assertVar)(c, true)
                        )
                      }
                      .map(x => BinaryExpr(BinaryExpr(x._1, "&&", UnaryExpr("!", x._2)), "&&", x._3))
                      .reduceLeft[Expr]((acc, e) => BinaryExpr(acc, "||", e))
                }
                .foldLeft[Expr](BoolLit(false))((acc, e) => BinaryExpr(acc, "||", e)),
              characterizer.havocs, "exists", assertVar
            )
          )
        )
        if (wpPlus) {
          BinaryExpr(
            classicWP, "||",
            post
          )
        } else classicWP
      }
      // quantifiers over non-state variables
      case Assertion(quantifier, assertVarDecls, body) => Assertion(quantifier, assertVarDecls, computeSinglePost(c, body))
      case BinaryExpr(e1, op, e2) => BinaryExpr(computeSinglePost(c, e1), op, computeSinglePost(c, e2))
      case UnaryExpr(op, e) => UnaryExpr(op, computeSinglePost(c, e))
      case ImpliesExpr(left, right) => ImpliesExpr(computeSinglePost(c, left), computeSinglePost(c, right))
      case _ => post
    }
  }

  /**
   * Helper function substituting all variables in an assertion for a given path and a given assertion variable.
   * The substitution is only taking place if we encounter a [[LookupExpr]] for the `assertVar`.
   * Otherwise, the substitution will be (or has been) handled by another quantifier.
   */
  private def substituteExprPath(expr: Expr, map: Map[Id, Expr], assertVar: AssertVar)(implicit c: Characterizer, deepRec: Boolean): Expr = expr match {
    case Assertion(quantifier, assertVarDecls@List(AssertVarDecl(_, StateType())), body) => {
      val substitutedOuter =
        Assertion(quantifier, assertVarDecls, substituteExprPath(body, map, assertVar)(c, false))
      if (deepRec) computeSinglePost(c, substitutedOuter)
      else substitutedOuter
    }
    case Assertion(quantifier, assertVarDecls, body) => Assertion(quantifier, assertVarDecls, substituteExprPath(body, map, assertVar))
    case BinaryExpr(e1, op, e2) => BinaryExpr(substituteExprPath(e1, map, assertVar), op, substituteExprPath(e2, map, assertVar))
    case UnaryExpr(op, e) => UnaryExpr(op, substituteExprPath(e, map, assertVar))
    case ImpliesExpr(left, right) => ImpliesExpr(substituteExprPath(left, map, assertVar), substituteExprPath(right, map, assertVar))
    case LookupExpr(id, index) if id == assertVar =>
      handleHavoc(applySubstitution(index, map))(id.asInstanceOf[AssertVar]) // only perform substitution, if assertVar matches
    case _ => expr
  }

  /**
   * Helper function substituting the path condition for a given state. In particular, identifiers are
   * substituted for a [[LookupExpr]] for the particular state. This is, because we need to make sure that
   * every variable reference in the path condition is bound to a state.
   */
  protected[syntactic] def substitutePathCondition(pc: Expr, state: AssertVar): Expr = pc match {
    case Id(_) => LookupExpr(state, pc)
    case HavocVar(name) => AssertVar(name + "_" + state.name)
    case Num(_) | BoolLit(_) | LookupExpr(_, _) | StateExistsExpr(_, _) => pc
    case BinaryExpr(e1, op, e2) => BinaryExpr(substitutePathCondition(e1, state), op, substitutePathCondition(e2, state))
    case UnaryExpr(op, e) => UnaryExpr(op, substitutePathCondition(e, state))
    case ImpliesExpr(left, right) => ImpliesExpr(substitutePathCondition(left, state), substitutePathCondition(right, state))
    case Assertion(quantifier, assertVarDecls, body) => Assertion(quantifier, assertVarDecls, substitutePathCondition(body, state)) // need to support assertions because of "hyperAssume" statements, which alter the path condition
    case _ => sys.error("WeakestPrecondition: Yet unsupported expression in path-condition substitution: " + pc.toString) // TODO: Check which other expressions could be assigned
  }

  /**
   * Converts every multi-variable quantifier into an equivalent chain of single-variable quantifiers.
   * This normalization is later needed for computing the weakest precondition.
   */
  protected[syntactic] def desugarQuantifiers(e: Expr): Expr = e match {
    case Assertion("forall", (x1@AssertVarDecl(_, StateType())) :: (x2@AssertVarDecl(_, StateType())) :: xs, ImpliesExpr(stateExists, realBody)) => { // if we have multiple state assert vars, we also want to separate StateExistsExpr
      val extracted = extractFirstFromNestedAnd(stateExists)
      Assertion("forall", List(x1), ImpliesExpr(extracted._1, desugarQuantifiers(Assertion("forall", (x2 :: xs), ImpliesExpr(extracted._2, realBody)))))
    }
    case Assertion("exists", (x1@AssertVarDecl(_, StateType())) :: (x2@AssertVarDecl(_, StateType())) :: xs, BinaryExpr(stateExists, "&&", realBody)) => { // if we have multiple state assert vars, we also want to separate StateExistsExpr
      val extracted = extractFirstFromNestedAnd(stateExists)
      Assertion("exists", List(x1), BinaryExpr(extracted._1, "&&", desugarQuantifiers(Assertion("exists", (x2 :: xs), BinaryExpr(extracted._2, "&&", realBody)))))
    }
    case Assertion(quantifier, assertVarDecls, body) => assertVarDecls match {
      case _ :: Nil => Assertion(quantifier, assertVarDecls, desugarQuantifiers(body)) // only one assertVar ==> already desugared, need to desugar body
      case x :: xs => Assertion(quantifier, List(x), desugarQuantifiers(Assertion(quantifier, xs, body))) // non-state quantifier
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

  /**
   * Helper function to introduce quantifiers for a set of havoc variables.
   *
   * Given an expression `e` (body of an assertion) and a set of havoc variables `q`,
   * this function wraps `e` in a chain of quantifiers, one for each havoc
   * variable. Each havoc variable is renamed to be specific to the given assertion state:
   * for a havoc variable `h` and state variable `s`, the bound assertion
   * variable is named `h_s`.
   */
  private def addHavocQuantifiers(e: Expr, q: Set[HavocVar], assertString: String, assertState: AssertVar): Expr = {
    q.toSeq
      .foldLeft(e) {
        case (acc, HavocVar(name)) => {
          val newName = name + "_" + assertState.name
          Assertion(assertString, List(AssertVarDecl(AssertVar(newName), IntType())), acc)
        }
      }
  }

  /**
   * Helper function to handle occurrences of [[HavocVar]] within an assertion body
   * (introduced by the [[Characterizer]]).
   *
   * This function replaces:
   *  - plain identifiers by a lookup into the current assertion state, and
   *  - [[HavocVar]] occurrences by state-specific assertion variables,
   *    naming them `h_s` for a havoc variable `h` and an implicit assertion
   *    state variable `s`.
   */
  private def handleHavoc(expr: viper.HHLVerifier.ast.Expr)(implicit assertVar: AssertVar): viper.HHLVerifier.ast.Expr = expr match {
    case Id(_) => LookupExpr(assertVar, expr)
    case HavocVar(name) => AssertVar(name + "_" + assertVar.name)
    case Num(_) | BoolLit(_) => expr
    case BinaryExpr(e1, op, e2) => BinaryExpr(handleHavoc(e1), op, handleHavoc(e2))
    case UnaryExpr(op, e) => UnaryExpr(op, handleHavoc(e))
    case ImpliesExpr(left, right) => ImpliesExpr(handleHavoc(left), handleHavoc(right))
    case _ => sys.error("WeakestPrecondition: Unexpected expression: " + expr.toString)
  }
}
