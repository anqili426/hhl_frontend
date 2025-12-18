package viper.HHLVerifier.syntactic.handler

import viper.HHLVerifier.ast._
import viper.HHLVerifier.typing.StateType

object LoopUtils {
  private var genSymCounter: Int = 0

  def box(expr: Expr): Expr = {
    val assertVar = AssertVar(genSym("_intState"))
    Assertion("forall", List(AssertVarDecl(assertVar, StateType())),
      ImpliesExpr(
        StateExistsExpr(assertVar, false),
        LookupExpr(assertVar, expr)))
  }

  def low(expr: Expr): Expr = {
    val assertVar1 = AssertVar(genSym("_intState"))
    val assertVar2 = AssertVar(genSym("_intState"))
    Assertion("forall", List(AssertVarDecl(assertVar1, StateType()), AssertVarDecl(assertVar2, StateType())),
      ImpliesExpr(
        BinaryExpr(StateExistsExpr(assertVar1, false), "&&", StateExistsExpr(assertVar2, false)),
        BinaryExpr(
          BinaryExpr(LookupExpr(assertVar1, expr), "&&", LookupExpr(assertVar2, expr)), "||",
          BinaryExpr(UnaryExpr("!", LookupExpr(assertVar1, expr)), "&&", UnaryExpr("!", LookupExpr(assertVar2, expr))))))
  }

  def genSym(s: String): String = {
    genSymCounter += 1
    s + "_" + genSymCounter
  }
}
