package viper.HHLVerifier.syntactic.handler

import viper.HHLVerifier.ast._
import viper.HHLVerifier.syntactic.smt.{ParallelRunner, SMTStatus}

object LoopRuleSelector {
  def select(loop: WhileLoopStmt): LoopRuleHandler = loop match {
    case WhileLoopStmt(_, _, _, _, rule) => rule match {
      case "syncRule" => SyncHandler
      case "syncTotRule" => SyncTotHandler
      case "forAllExistsRule" => ForallExistsHandler
      case "existsRule" => ExistsHandler
      case "desugaredRule" => sys.error("RuleSelector: \"desugaredRule\" is deprecated.")
      case "unspecified" => autoRuleInference(loop)
    }
  }

  private def autoRuleInference(loop: WhileLoopStmt): LoopRuleHandler = loop match {
    case WhileLoopStmt(cond, body, inv, decr, rule) => {
      val mappedInvariant = inv.map(_._2)
      val combinedInvariant = mappedInvariant.reduceLeft((acc, x) => BinaryExpr(acc, "&&", x))

      // check invariant I ⊨ low(b)
      val result = ParallelRunner.checkEntailment(combinedInvariant, LoopUtils.low(cond))

      if (result._1 == SMTStatus.Unsatisfiable) { // i.e. I ⊨ low(b) holds and we need a synchronized loop rule
        if (decr.isDefined && SyncTotHandler.checkTerminationLoops(body)) {
          SyncTotHandler
        } else {
          SyncHandler
        }
      }
      else { // i.e. I ⊨ low(b) doesn't hold and we need a non-synchronized loop rule
        if (decr.isDefined && ExistsHandler.extractFirstExists(mappedInvariant)._1.isDefined) {  // i.e. there is a decreases clause and the invariant contains a state exists assertion
          ExistsHandler
        } else {
          ForallExistsHandler
        }
      }
    }
  }
}
