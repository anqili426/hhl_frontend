package viper.HHLVerifier.syntactic

import com.microsoft.z3.Status
import viper.HHLVerifier.ast._
import viper.HHLVerifier.syntactic.SyntacticEngine.Triple
import viper.HHLVerifier.syntactic.WeakestPrecondition.substitutePathCondition
import viper.HHLVerifier.typing.StateType

sealed trait LoopRuleHandler {
  def handle(loop: WhileLoopStmt, before: CompositeStmt, after: CompositeStmt, pre: Seq[Expr], post: Seq[Expr], progVars: Seq[Id], name: String): Seq[Triple]
}

object LoopRuleHandler {
  def box(expr: Expr): Expr = {
    val assertVar = AssertVar("_intState")
    Assertion("forall", List(AssertVarDecl(assertVar, StateType())),
      ImpliesExpr(
        StateExistsExpr(assertVar, false),
        substitutePathCondition(expr, assertVar)))
  }

  def low(expr: Expr): Expr = {
    val assertVar1 = AssertVar("_intState1")
    val assertVar2 = AssertVar("_intState2")
    //Assertion("forall", List(AssertVarDecl(assertVar1, StateType()), AssertVarDecl(assertVar2, StateType())), BinaryExpr(LookupExpr(assertVar1, expr), "==", LookupExpr(assertVar2, expr))) // TODO: right now, == operator is only defined for integers
    Assertion("forall", List(AssertVarDecl(assertVar1, StateType()), AssertVarDecl(assertVar2, StateType())),
      ImpliesExpr(
        BinaryExpr(StateExistsExpr(assertVar1, false), "&&", StateExistsExpr(assertVar2, false)),
        BinaryExpr(
          BinaryExpr(LookupExpr(assertVar1, expr), "&&", LookupExpr(assertVar2, expr)), "||",
          BinaryExpr(UnaryExpr("!", LookupExpr(assertVar1, expr)), "&&", UnaryExpr("!", LookupExpr(assertVar2, expr))))))
  }
}

object ForallExistsHandler extends LoopRuleHandler {
  def handle(loop: WhileLoopStmt, before: CompositeStmt, after: CompositeStmt, pre: Seq[Expr], post: Seq[Expr], progVars: Seq[Id], name: String): Seq[Triple] = loop match {
    case WhileLoopStmt(cond, body, inv, decr, rule) => {
      println("\tVerifying loop using \"forallExistsRule\"")
      val mappedInvariant = inv.map(_._2)
      val loopPostcondition = computeLoopPost(mappedInvariant.reduceLeft((acc, x) => BinaryExpr(acc, "&&", x)))(cond)

      val triplePrefix = Triple(before, pre, inv.map(_._2), name + " > [P] prefix [I]")
      val tripleBody = Triple(IfElseStmt(cond, body, CompositeStmt(Nil)), mappedInvariant, mappedInvariant, name + " > [I] if (b) {body} [I]")
      val tripleSuffix = Triple(after, List(loopPostcondition), post, name + " > [Q_loop] suffix [Q]")
      List(triplePrefix, tripleBody, tripleSuffix)
    }
  }

  private def computeLoopPost(inv: viper.HHLVerifier.ast.Expr, noForallAfterExists: Boolean = true)(implicit loopCondition: viper.HHLVerifier.ast.Expr): viper.HHLVerifier.ast.Expr = inv match {
    case Assertion("exists", List(AssertVarDecl(vName, vType)), body) => Assertion("exists", List(AssertVarDecl(vName, vType)), BinaryExpr(computeLoopPost(body, false), "&&", ImpliesExpr(UnaryExpr("!", substitutePathCondition(loopCondition, vName)), StateExistsExpr(vName, false)))) // cf. Hypra paper, p. 19, bottom
    case Assertion("exists", _, _) => sys.error("ForallExistsHandler: Tried to apply \"forallExistsRule\", but found non-desugared quantifier.")
    case Assertion("forall", assertVarDecls@List(AssertVarDecl(_, vType)), body) =>
      if (!noForallAfterExists && vType.isInstanceOf[StateType]) sys.error("ForallExistsHandler: Tried to apply \"forallExistsRule\", but invariant \"no forall <_> after exists quantifier\" was violated.")
      else Assertion("forall", assertVarDecls, computeLoopPost(body, noForallAfterExists))
    case BinaryExpr(e1, op, e2) => BinaryExpr(computeLoopPost(e1, noForallAfterExists), op, computeLoopPost(e2, noForallAfterExists))
    case UnaryExpr(op, e) => UnaryExpr(op, computeLoopPost(e, noForallAfterExists))
    case ImpliesExpr(left, right) => ImpliesExpr(computeLoopPost(left, noForallAfterExists), computeLoopPost(right, noForallAfterExists))
    case _ => inv // TODO: Double-check which other Expr are possible
  }
}

object SyncHandler extends LoopRuleHandler {
  def handle(loop: WhileLoopStmt, before: CompositeStmt, after: CompositeStmt, pre: Seq[Expr], post: Seq[Expr], progVars: Seq[Id], name: String): Seq[Triple] = loop match {
    case WhileLoopStmt(cond, body, inv, decr, rule) => {
      println("\tVerifying loop using \"syncRule\"")
      val mappedInvariant = inv.map(_._2)
      val combinedInvariant = mappedInvariant.reduceLeft((acc, x) => BinaryExpr(acc, "&&", x))
      val loopPostcondition = BinaryExpr(BinaryExpr(combinedInvariant, "||", LoopRuleHandler.box(BoolLit(false))), "&&", LoopRuleHandler.box(UnaryExpr("!", cond)))

      // check invariant I ⊨ low(b)
      val encoder: LogicEncoderNew = new LogicEncoderNew
      val result = encoder.checkEntailment(combinedInvariant, LoopRuleHandler.low(cond), progVars)
      if (result._1 != Status.UNSATISFIABLE) sys.error("SyncHandler: Tried to apply \"syncRule\", but invariant \"I ⊨ low(b)\" was violated.")

      val triplePrefix = Triple(before, pre, inv.map(_._2), name + " > [P] prefix [I]")
      val tripleBody = Triple(body, List(BinaryExpr(combinedInvariant, "&&", LoopRuleHandler.box(cond))), mappedInvariant, name + " > [I ∧ □b] body [I]")
      val tripleSuffix = Triple(after, List(loopPostcondition), post, name + " > [Q_loop] suffix [Q]")
      List(triplePrefix, tripleBody, tripleSuffix)
    }
  }
}

object RuleSelector {
  def select(loop: WhileLoopStmt, progVars: Seq[Id]): LoopRuleHandler = loop match {
    case WhileLoopStmt(_, _, _, _, rule) => rule match {
      case "syncRule" => SyncHandler
      case "syncTotRule" => ???
      case "forAllExistsRule" => ForallExistsHandler
      case "existsRule" => ???
      case "desugaredRule" => ???
      case "unspecified" => autoRuleInference(loop, progVars)
    }
  }

  private def autoRuleInference(loop: WhileLoopStmt, progVars: Seq[Id]): LoopRuleHandler = loop match {
    case WhileLoopStmt(cond, body, inv, decr, rule) => {
      // TODO: Extend to support all loop rules
      val mappedInvariant = inv.map(_._2)
      val combinedInvariant = mappedInvariant.reduceLeft((acc, x) => BinaryExpr(acc, "&&", x))

      // check invariant I ⊨ low(b)
      val encoder: LogicEncoderNew = new LogicEncoderNew
      val result = encoder.checkEntailment(combinedInvariant, LoopRuleHandler.low(cond), progVars)
      if (result._1 == Status.UNSATISFIABLE) {
        SyncHandler
      }
      else {
        ForallExistsHandler
      }
    }
  }
}