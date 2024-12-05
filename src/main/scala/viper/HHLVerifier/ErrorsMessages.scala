package viper.HHLVerifier

import viper.silver.ast.AnnotationInfo

abstract sealed class ErrorMsg(expr: Expr) {
  def text: String

  private def getExprStr: String = PrettyPrinter.formatExpr(expr)
  def getMsg: AnnotationInfo = AnnotationInfo(Map("msg" -> Seq(f"${text}\n${getExprStr}")))
}

case class PostconditionErr(expr: Expr) extends ErrorMsg(expr) {
  override def text: String = "The following post condition might not hold:"
}

case class HyperAssertionErr(expr: Expr) extends ErrorMsg(expr) {
  override def text: String = "The following hyper assertion might not hold:"
}

case class DeprecatedErr(expr: Expr) extends ErrorMsg(expr) {
  override def text: String = "[CRITICAL] The following expression caused an error, but should be deprecated:"
}

case class MultiAssignErr(expr: Expr) extends ErrorMsg(expr) {
  override def text: String = "The following precondition may not hold when using MultiAssign:"
}

case class LoopEntryPointErr(expr: Expr) extends ErrorMsg(expr) {
  override def text: String = "The following loop invariant might not hold at entry point:"
}

case class FrameErr(expr: Expr) extends ErrorMsg(expr) {
  override def text: String = "The following hyper assertion (frame) might not hold:"
}

case class MethodCallPreconditionErr(expr: Expr) extends ErrorMsg(expr) {
  override def text: String = "The following precondition of a custom method might not hold:"
}

case class LoopSyncGuardErr(expr: Expr) extends ErrorMsg(expr) {
  override def text: String = "WhileSyncRule/WhileSyncTermRule:\nThe following loop guard might not be identical for all states, violating low(b):"
}

case class LoopVariantErr(expr: Expr) extends ErrorMsg(expr) {
  override def text: String = "The following variant might not strictly decrease:"
}