package viper.HHLVerifier.comm

import viper.HHLVerifier.Expr

case class ParserError(descr: String, pos: Int) extends CodeError {
  override def code: Int = 100
  override def name: String = "Parser Error"
  override val offsetLeft = pos;
  override val offsetRight = pos + 10;
}

case class SymbolCheckerError(descr: String, offsetLeft: Int, offsetRight: Int) extends CodeError {
  override def code: Int = 200
  override def name: String = "Symbol Checker Error"
}

case class TypeCheckerError(descr: String, offsetLeft: Int, offsetRight: Int) extends CodeError {
  override def code: Int = 300
  override def name: String = "Type Checker Error"
}

case class GeneratorError(descr: String, offsetLeft: Int, offsetRight: Int) extends CodeError {
  override def code: Int = 400
  override def name: String = "Generator Error"
}

case class VerificationError(descr: String, offsetLeft: Int, offsetRight: Int) extends CodeError {
  override def code: Int = 200
  override def name: String = "Verification Error"
}

object VerificationErrors {
  def Postcondition(expr: Expr) = f"The post condition ${expr.toString()} might not hold"
  def HyperAssertion(expr: Expr) = f"The hyper assertion ${expr.toString()} might not hold"
  def Deprecated(expr: Expr) = f"The expression ${expr.toString()} caused an error, but this should be deprecated"
  def MethodCall(expr: Expr) = f"The precondtion ${expr.toString()} might not hold"
  def LoopEntryPoint(expr: Expr, quantifiers: Int) = f"${ if (quantifiers > 0) f"($quantifiers stripped)" else "" }The loop invariant ${expr.toString()} might not hold at entry point"
  def LoopSyncGuard(expr: Expr) = f"The loop guard ${expr.toString()} might not be identical for all states"
  def LoopVariant(expr: Expr) = f"The variant ${expr.toString()} might not strictly decrease"
  def LoopInvariant(expr: Expr, quantifiers: Int) = f"${ if (quantifiers > 0) f"($quantifiers stripped)" else "" }The invariant ${expr.toString()} might not hold"
}