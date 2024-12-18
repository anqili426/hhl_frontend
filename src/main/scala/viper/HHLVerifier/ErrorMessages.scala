package viper.HHLVerifier

import viper.silver.ast.AnnotationInfo

/* Parameters:
   - expr: Expression causing the error (errors can only be caused by violated expressions in asserts or postconditions)
   - text: Description of the error
   - meta: Metadata describing the environment in which the error was generated
 */
sealed class ErrorMsg(expr: Expr, text: String, meta: Map[String, String]) {
  private def getExprStr: String = PrettyPrinter.formatExpr(expr)

  def getMsg: AnnotationInfo = {
    val formatted = new StringBuilder()

    formatted.append(text)
    formatted.append("\n")
    formatted.append(getExprStr)
    formatted.append("\n")
    if (meta.nonEmpty) {
      formatted.append("Metadata:")

      meta.foreach { case (key, value) =>
        formatted.append(s"\n- $key: $value")
      }
    }

    AnnotationInfo(Map("msg" -> Seq(formatted.toString())))
  }
}

// General Errors
case class PostconditionErr(expr: Expr, meta: Map[String, String] = Map.empty) extends ErrorMsg(
  expr,
  "[Method] The following post condition might not hold:",
  meta
)

case class HyperAssertionErr(expr: Expr, meta: Map[String, String] = Map.empty) extends ErrorMsg(
  expr,
  "[HyperAssertion] The following hyper assertion might not hold:",
  meta
)

case class DeprecatedErr(expr: Expr, meta: Map[String, String] = Map.empty) extends ErrorMsg(
  expr,
  "[CRITICAL] The following expression caused an error, but should be deprecated:",
  meta
)

case class FrameErr(expr: Expr, meta: Map[String, String] = Map.empty) extends ErrorMsg(
  expr,
  "[Frame] The following hyper assertion used in a frame might not hold:",
  meta
)

case class MethodCallPreconditionErr(expr: Expr, meta: Map[String, String] = Map.empty) extends ErrorMsg(
  expr,
  "[MethodCall] The following precondition of a custom method might not hold:",
  meta
)

// Loop Errors
case class LoopInvEntryErr(expr: Expr, meta: Map[String, String] = Map.empty) extends ErrorMsg(
  expr,
  "[WhileLoop] The following loop invariant might not hold at entry point:",
  meta
)

case class LoopSyncGuardErr(expr: Expr, meta: Map[String, String] = Map.empty) extends ErrorMsg(
  expr,
  "[WhileLoop] The following loop guard might not be identical for all states, violating low(b):",
  meta
)

case class LoopVariantErr(expr: Expr, meta: Map[String, String] = Map.empty) extends ErrorMsg(
  expr,
  "[WhileLoop] The following variant might not decrease strictly:",
  meta
)

case class LoopInvariantErr(expr: Expr, meta: Map[String, String] = Map.empty) extends ErrorMsg(
  expr,
  "[WhileLoop] The following invariant might not be preserved:",
  meta
)

case class LoopExistsRuleInvariantErr(expr: Expr, meta: Map[String, String] = Map.empty) extends ErrorMsg(
  expr,
  "[WhileLoop] The following transformed invariant (stripped from its existential quantifier) with the automatically chosen " +
    "loop rule does not result in a postcondition that entails the original invariant",
  meta
)