package viper.HHLVerifier

import viper.silver.ast.AnnotationInfo

class Locater(val program: String) {
  val lines = program.split("\n")

  def getPos(charPos: Int): (Int, Int) = {
    var currentCharCount = 0
    var lineNumber = 0

    for (i <- lines.indices) {
      currentCharCount += lines(i).length + 1

      if (currentCharCount > charPos) {
        lineNumber = i + 1
        return (lineNumber, charPos - currentCharCount + lines(i).length + 1)
      }
    }

    (lineNumber, charPos - currentCharCount)
  }
}

abstract sealed class ErrorMsg(expr: Expr, loc: Locater) {
  def text: String

  private def getExprStr: String = PrettyPrinter.formatExpr(expr)
  def getMsg: AnnotationInfo = {
    val (line, char) = loc.getPos(expr.pos)

    AnnotationInfo(Map("msg" -> Seq(f"${text}\n[$line:$char] ${getExprStr}")))
  }
}
case class PostconditionErr(expr: Expr, loc: Locater) extends ErrorMsg(expr, loc) {
  override def text: String = "[Method] The following post condition might not hold:"
}

case class HyperAssertionErr(expr: Expr, loc: Locater) extends ErrorMsg(expr, loc) {
  override def text: String = "[HyperAssertion] The following hyper assertion might not hold:"
}

case class DeprecatedErr(expr: Expr, loc: Locater) extends ErrorMsg(expr, loc) {
  override def text: String = "[CRITICAL] The following expression caused an error, but should be deprecated:"
}

case class MultiAssignErr(expr: Expr, loc: Locater) extends ErrorMsg(expr, loc) {
  override def text: String = "[MultiAssign] The following precondition may not hold:"
}

case class FrameErr(expr: Expr, loc: Locater) extends ErrorMsg(expr, loc) {
  override def text: String = "[Frame] The following hyper assertion (frame) might not hold:"
}

case class MethodCallPreconditionErr(expr: Expr, loc: Locater) extends ErrorMsg(expr, loc) {
  override def text: String = "[MethodCall] The following precondition of a custom method might not hold:"
}

case class LoopEntryPointErr(expr: Expr, loc: Locater) extends ErrorMsg(expr, loc) {
  override def text: String = "[WhileLoop] The following loop invariant might not hold at entry point:"
}

case class LoopSyncGuardErr(expr: Expr, loc: Locater) extends ErrorMsg(expr, loc) {
  override def text: String = "[WhileLoop/WhileSync(-Tot)] The following loop guard might not be identical for all states, violating low(b):"
}

case class LoopVariantErr(expr: Expr, loc: Locater) extends ErrorMsg(expr, loc) {
  override def text: String = "[WhileLoop] The following variant might not decrease strictly:"
}

case class LoopInvariantErr(expr: Expr, loc: Locater) extends ErrorMsg(expr, loc) {
  override def text: String = "[WhileLoop] The following invariant might not hold:"
}

case class LoopExistsInvErr(expr: Expr, loc: Locater) extends ErrorMsg(expr, loc) {
  override def text: String = "[WhileLoop/Exists] The following invariant might not hold:"
}