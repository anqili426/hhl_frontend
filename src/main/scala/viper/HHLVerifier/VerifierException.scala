package viper.HHLVerifier

abstract class VerifierException(msg: String) extends Exception {
  val errMsg = msg
}
case class DuplicateIdentifierException(msg: String) extends VerifierException(msg)
case class IdentifierNotFoundException(msg: String) extends VerifierException(msg)
case class IllegalAssignmentException(msg: String) extends VerifierException(msg)
case class UnknownException(msg: String) extends VerifierException(msg)
case class TypeException(msg: String) extends VerifierException(msg)
