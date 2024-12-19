package viper.HHLVerifier

import viper.silver.ast.AnnotationInfo

/* Parameters:
   - expr: Expression causing the error (errors can only be caused by violated expressions in asserts or postconditions)
   - text: Description of the error
   - meta: Metadata describing the environment in which the error was generated
 */
sealed class ErrorMsg(name: String, text: String, expr: Expr, meta: Map[String, String]) {
  private def getExprStr: String = PrettyPrinter.formatExpr(expr)

  def getMsg: AnnotationInfo = {
    val formatted = new StringBuilder()

    formatted.append(f"[$name")
    if (meta.contains("LoopRule")) formatted.append(f", ${meta("LoopRule")} selected")
    if (meta.contains("QuantifiersRemoved") && meta("QuantifiersRemoved").toInt > 0) formatted.append(f", ${meta("QuantifiersRemoved")} quantifier(s) removed")
    formatted.append(f"] $text\n$getExprStr")

    AnnotationInfo(Map("msg" -> Seq(formatted.toString())))
  }
}

// General Errors
case class PostconditionErr(expr: Expr, meta: Map[String, String] = Map.empty) extends ErrorMsg(
  "Method", "The following post condition might not hold:", expr, meta
)

case class HyperAssertionErr(expr: Expr, meta: Map[String, String] = Map.empty) extends ErrorMsg(
  "HyperAssertion", "The following hyper assertion might not hold:", expr, meta
)

case class DeprecatedErr(expr: Expr, meta: Map[String, String] = Map.empty) extends ErrorMsg(
  "CRITICAL", "The following expression caused an error, but should be deprecated:", expr, meta
)

case class FrameErr(expr: Expr, meta: Map[String, String] = Map.empty) extends ErrorMsg(
  "Frame", "The following hyper assertion used in a frame might not hold:", expr, meta
)

case class MethodCallPreconditionErr(expr: Expr, meta: Map[String, String] = Map.empty) extends ErrorMsg(
  "MethodCall", "The following precondition of a custom method might be preserved:", expr, meta
)

case class LoopInvEntryErr(expr: Expr, meta: Map[String, String] = Map.empty) extends ErrorMsg(
  "WhileLoop", "The following loop invariant might not hold at entry point:", expr, meta
)

case class LoopSyncGuardErr(expr: Expr, meta: Map[String, String] = Map.empty) extends ErrorMsg(
  "WhileLoop", "The following loop guard might not be identical for all states, violating low(b):", expr, meta
)

case class LoopVariantErr(expr: Expr, meta: Map[String, String] = Map.empty) extends ErrorMsg(
  "WhileLoop", "The following variant might not decrease strictly:", expr, meta
)

case class LoopInvariantErr(expr: Expr, meta: Map[String, String] = Map.empty) extends ErrorMsg(
  "WhileLoop", "The following invariant might not hold:", expr, meta
)

case class LoopExistsRuleInvariantErr(expr: Expr, meta: Map[String, String] = Map.empty) extends ErrorMsg(
  "WhileLoop", "The following transformed invariant (stripped from its existential quantifier) with the automatically chosen loop rule does not result in a postcondition that entails the original invariant:", expr, meta
)