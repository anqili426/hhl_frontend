package viper.HHLVerifier

object Normalizer {

  // This method removes all implications in e
  // e is expected to be a hyper-assertion that passes the type checker
  // It is either a method precondition or a loop invariant
  // When negate = true, the returned expression is (not (normalized(e)))
  def normalize(e: Expr, negate: Boolean): Expr = {
    e match {
      case BoolLit(value) => if (negate) BoolLit(!value) else e
      case StateExistsExpr(_, _) => if (negate) UnaryExpr("!", e) else e
      case Hint(_, _) => if (negate) UnaryExpr("!", e) else e
      case UnaryExpr(op, body) =>
        if (op == "-") throw UnknownException("Normalizer: expression " + e + " is not expected")
        else normalize(body, negate)
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

  // This method determines:
  // 1. Whether a forall quantifier is productive or not
  // 2. Whether an exists quantifier is top-level or not
  // 3. Ownership of a stateExistsExpr
  // 4. The useLimited value of each stateExistsExpr based on the shape of e
  // 5. Triggers of any assertion that universally quantifies over states
  // Input e is expected to be a normalized expression that passes the symbol checker and the type checker
  // Input underForAll is true means that e is part of an assertion that universally quantifiers over states
  // Output 1 represents whether e contains an assertion that existentially quantifiers over states
  // Output 2 is a sequence of all the stateExistsExpr (whose ownership is unknown) in e
  def detQuantifier(e: Expr, underForAll: Boolean) : (Boolean, Seq[StateExistsExpr]) = {
      e match {
        case a@Assertion(quantifier, vars, body) =>
          val assertVarIds = vars.map(v => v.vName.name)
          val quantifiesOverStates = vars.filter(v => v.vName.typ.isInstanceOf[StateType]).size > 0
          if (quantifier == "forall") {
            val res = detQuantifier(body, underForAll || quantifiesOverStates)
            a.proForAll = quantifiesOverStates && res._1
            a.topExists = false
            if (quantifiesOverStates) {
              var forAllTriggers: Seq[StateExistsExpr] = Seq.empty
              var existsTriggers: Seq[StateExistsExpr] = Seq.empty
              val ownedStateExistsExprs = res._2.filter(se => assertVarIds.contains(se.state.idName))
              if (ownedStateExistsExprs.size == 0) throw UnknownException("At least 1 assertion variable in an assertion is declared but never used")
              ownedStateExistsExprs.foreach(se => {
                se.useLimited = !a.proForAll
                val trigger1 = se.copy()
                val trigger2 = se.copy()
                trigger1.useForAll = true
                trigger1.useLimited = !a.proForAll
                trigger2.useForAll = false
                trigger2.useLimited = !a.proForAll
                forAllTriggers = forAllTriggers :+ trigger1
                existsTriggers = existsTriggers :+ trigger2
              })
              a.triggers = Seq(forAllTriggers, existsTriggers)
              (res._1, res._2.diff(ownedStateExistsExprs))
          } else {
              a.proForAll = false
              a.topExists = false
              (res._1, res._2)
            }
          } else { // quantifier == "exists", no triggers needed
            val res = detQuantifier(body, underForAll)
            if (quantifiesOverStates) {
              a.proForAll = false
              a.topExists = !underForAll
              val ownedStateExistsExprs = res._2.filter(se => assertVarIds.contains(se.state.idName))
              ownedStateExistsExprs.foreach(se => {
                se.useLimited = underForAll
              })
              (true, res._2.diff(ownedStateExistsExprs))
            } else {
              a.proForAll = false
              a.topExists = false
              (res._1, res._2)
            }
          }
        case UnaryExpr(op, exp) =>
          if (op == "!") {
            detQuantifier(exp, underForAll)
          } else (false, Seq.empty)
        case BinaryExpr(e1, op, e2) =>
          if (TypeChecker.boolOp.contains(op)) {
            val res1 = detQuantifier(e1, underForAll)
            val res2 = detQuantifier(e2, underForAll)
            (res1._1 || res2._1, res1._2 ++ res2._2)
          } else (false, Seq.empty)
        case ImpliesExpr(_, _) => throw UnknownException("Normalizer: unexpected implication")
        case se@StateExistsExpr(_, _) => (false, Seq(se))
        case _ => (false, Seq.empty)
      }
  }
}
