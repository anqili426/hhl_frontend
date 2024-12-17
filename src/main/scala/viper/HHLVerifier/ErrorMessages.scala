package viper.HHLVerifier

import viper.silver.ast.AnnotationInfo

abstract sealed class ErrorMsg(expr: Expr) {
  def text: String    // Description of the error message
  var depth: Int = 0  // Counts number of stripped quantifiers

  def setDepth(d: Int): ErrorMsg = {
    depth = d
    this
  }

  private def getExprStr: String = PrettyPrinter.formatExpr(expr)

  def getMsg: AnnotationInfo = AnnotationInfo(Map("msg" -> Seq(f"After stripping ${depth} quantifier(s):\n$text\n$getExprStr")))
}

case class PostconditionErr(expr: Expr) extends ErrorMsg(expr) {
  override def text: String = "[Method] The following post condition might not hold:"
}

case class HyperAssertionErr(expr: Expr) extends ErrorMsg(expr) {
  override def text: String = "[HyperAssertion] The following hyper assertion might not hold:"
}

case class DeprecatedErr(expr: Expr) extends ErrorMsg(expr) {
  override def text: String = "[CRITICAL] The following expression caused an error, but should be deprecated:"
}

case class FrameErr(expr: Expr) extends ErrorMsg(expr) {
  override def text: String = "[Frame] The following hyper assertion used in a frame might not hold:"
}

case class MethodCallPreconditionErr(expr: Expr) extends ErrorMsg(expr) {
  override def text: String = "[MethodCall] The following precondition of a custom method might be preserved:"
}

case class LoopEntryPointErr(expr: Expr) extends ErrorMsg(expr) {
  override def text: String = "[WhileLoop] The following loop invariant might not hold at entry point:"
}

case class LoopSyncGuardErr(expr: Expr) extends ErrorMsg(expr) {
  override def text: String = "[WhileLoop/WhileSync(-Tot)] The following loop guard might not be identical for all states, violating low(b):"
}

case class LoopVariantErr(expr: Expr) extends ErrorMsg(expr) {
  override def text: String = "[WhileLoop] The following variant might not decrease strictly:"
}

case class LoopInvariantErr(expr: Expr) extends ErrorMsg(expr) {
  override def text: String = "[WhileLoop] The following invariant might not hold:"
}

case class LoopExistsInvErr(expr: Expr) extends ErrorMsg(expr) {
  override def text: String = "[WhileLoop/Exists] The following invariant might not hold:"
}