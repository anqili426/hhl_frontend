package viper.HHLVerifier

object Normalizer {

  // This method removes all implications in e
  // e is expected to be a hyper-assertion that passes the typechecker
  // It is either a method precondition or a loop invariant
  // When negate = true, the returned expression is (not (normalized(e)))
  def normalize(e: Expr, negate: Boolean): Expr = {
    e match {
      case BoolLit(_) => if (negate) UnaryExpr("!", e) else e
      case StateExistsExpr(_) => if (negate) UnaryExpr("!", e) else e
      case UnaryExpr(op, e) =>
        if (op == "-") e
        else normalize(e, negate)
      case be@BinaryExpr(e1, op, e2) =>
        if (e1.typ.isInstanceOf[BoolType]) {
          val normalizedE1 = normalize(e1, negate)
          val normalizedE2 = normalize(e2, negate)
          if (negate) {
            val newOp = {
              op match {
                case "==" => "!="
                case "!=" => "=="
                case "||" => "&&"
                case "&&" => "||"
                case _ => throw UnknownException("Unexpected binary operator " + op)
              }
            }
            BinaryExpr(normalizedE1, newOp, normalizedE2)
          } else BinaryExpr(normalizedE1, op, normalizedE2)
        } else {
          if (negate) UnaryExpr("!", be)
          else be
        }
      case ImpliesExpr(left, right) =>
        if (negate) {
          // not (A => B) is equivalent to (A and (not B))
          val normalizedLeft = normalize(left, false)
          val normalizedRight = normalize(right, true)
          BinaryExpr(normalizedLeft, "&&", normalizedRight)
        } else {
          // A => B is equivalent to ((not A) or B)
          val normalizedLeft = normalize(left, true)
          val normalizedRight = normalize(right, false)
          BinaryExpr(normalizedLeft, "||", normalizedRight)
        }
      case Assertion(quantifier, assertVarDecls, body) =>
        val normalizedBody = normalize(body, negate)
        val newQuantifier = {
          if (negate && quantifier == "forall") "exists"
          else if (negate && quantifier == "exists") "forall"
          else quantifier
        }
        Assertion(newQuantifier, assertVarDecls, normalizedBody)
      case _ => throw UnknownException("Normalizer: expression " + e + " is not expected")
    }
  }
}
