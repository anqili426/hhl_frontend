package viper.HHLVerifier.syntactic

import com.microsoft.z3.Status
import viper.HHLVerifier.Main
import viper.HHLVerifier.ast._
import viper.HHLVerifier.syntactic.SyntacticEngine.Triple
import viper.HHLVerifier.typing.StateType
import viper.HHLVerifier.syntactic.WeakestPrecondition.desugarQuantifiers
import viper.HHLVerifier.syntactic.smt.{ParallelRunner, SMTStatus}

sealed trait LoopRuleHandler {
  def handle(loop: WhileLoopStmt, before: CompositeStmt, after: CompositeStmt, pre: Seq[Expr], post: Seq[Expr], name: String): Seq[Triple]
}

object LoopRuleHandler {
  private var genSymCounter: Int = 0

  def box(expr: Expr): Expr = {
    val assertVar = AssertVar(genSym("_intState"))
    Assertion("forall", List(AssertVarDecl(assertVar, StateType())),
      ImpliesExpr(
        StateExistsExpr(assertVar, false),
        LookupExpr(assertVar, expr)))
  }

  def low(expr: Expr): Expr = {
    val assertVar1 = AssertVar(genSym("_intState"))
    val assertVar2 = AssertVar(genSym("_intState"))
    //Assertion("forall", List(AssertVarDecl(assertVar1, StateType()), AssertVarDecl(assertVar2, StateType())), BinaryExpr(LookupExpr(assertVar1, expr), "==", LookupExpr(assertVar2, expr))) // TODO: right now, == operator is only defined for integers
    Assertion("forall", List(AssertVarDecl(assertVar1, StateType()), AssertVarDecl(assertVar2, StateType())),
      ImpliesExpr(
        BinaryExpr(StateExistsExpr(assertVar1, false), "&&", StateExistsExpr(assertVar2, false)),
        BinaryExpr(
          BinaryExpr(LookupExpr(assertVar1, expr), "&&", LookupExpr(assertVar2, expr)), "||",
          BinaryExpr(UnaryExpr("!", LookupExpr(assertVar1, expr)), "&&", UnaryExpr("!", LookupExpr(assertVar2, expr))))))
  }

  def genSym(s: String): String = {
    genSymCounter += 1
    s + "_" + genSymCounter
  }
}

object ForallExistsHandler extends LoopRuleHandler {
  def handle(loop: WhileLoopStmt, before: CompositeStmt, after: CompositeStmt, pre: Seq[Expr], post: Seq[Expr], name: String): Seq[Triple] = loop match {
    case WhileLoopStmt(cond, body, inv, decr, rule) => {
      if (Main.logsActive) println("\tVerifying loop using \"forallExistsRule\"")
      val mappedInvariant = inv.map(_._2)
      val loopPostcondition = BinaryExpr(computeLoopPost(mappedInvariant.reduceLeft((acc, x) => BinaryExpr(acc, "&&", x)))(cond), "&&", LoopRuleHandler.box(UnaryExpr("!", cond)))

      val triplePrefix = Triple(
        before,
        pre,
        mappedInvariant,
        name + " > [P] prefix [I]")

      val tripleBody = Triple(
        IfElseStmt(cond, body, CompositeStmt(Nil)),
        mappedInvariant,
        mappedInvariant,
        name + " > [I] if (b) {body} [I]")

      val tripleSuffix = Triple(
        after,
        List(loopPostcondition),
        post,
        name + " > [Q_loop] suffix [Q]")

      List(triplePrefix, tripleBody, tripleSuffix)
    }
  }

  private def computeLoopPost(inv: viper.HHLVerifier.ast.Expr, noForallAfterExists: Boolean = true)(implicit loopCondition: viper.HHLVerifier.ast.Expr): viper.HHLVerifier.ast.Expr = inv match {
    case Assertion("exists", List(AssertVarDecl(vName, vType)), BinaryExpr(stateExists@StateExistsExpr(_, false), "&&", realBody)) => // the substitution applies only to normal states
      Assertion("exists", List(AssertVarDecl(vName, vType)),
        BinaryExpr(computeLoopPost(realBody, false), "&&", ImpliesExpr(LookupExpr(vName, UnaryExpr("!", loopCondition)), stateExists))
      ) // cf. Hypra paper, p. 19, bottom
    case Assertion("exists", list@List(AssertVarDecl(_, StateType())), body@BinaryExpr(StateExistsExpr(_, true), "&&", _)) => Assertion("exists", list, computeLoopPost(body, false)) // no special treatment for exists over error states, still no forall <_> should come after
    case Assertion("exists", list@List(AssertVarDecl(_, StateType())), body) => Assertion("exists", list, computeLoopPost(body, noForallAfterExists)) // no special treatment for exists over integers
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
  def handle(loop: WhileLoopStmt, before: CompositeStmt, after: CompositeStmt, pre: Seq[Expr], post: Seq[Expr], name: String): Seq[Triple] = loop match {
    case WhileLoopStmt(cond, body, inv, decr, rule) => {
      if (Main.logsActive) println("\tVerifying loop using \"syncRule\"")
      val mappedInvariant = inv.map(_._2)
      val combinedInvariant = mappedInvariant.reduceLeft((acc, x) => BinaryExpr(acc, "&&", x))
      val loopPostcondition = BinaryExpr(BinaryExpr(combinedInvariant, "||", LoopRuleHandler.box(BoolLit(false))), "&&", LoopRuleHandler.box(UnaryExpr("!", cond)))

      // check invariant I ⊨ low(b)
      val result = ParallelRunner.checkEntailment(combinedInvariant, LoopRuleHandler.low(cond))
      if (result._1 != SMTStatus.Unsatisfiable) sys.error("SyncHandler: Tried to apply \"syncRule\", but invariant \"I ⊨ low(b)\" was violated.")

      val triplePrefix = Triple(
        before,
        pre,
        mappedInvariant,
        name + " > [P] prefix [I]")

      val tripleBody = Triple(
        body,
        List(BinaryExpr(combinedInvariant, "&&", LoopRuleHandler.box(cond))),
        mappedInvariant,
        name + " > [I ∧ □b] body [I]")

      val tripleSuffix = Triple(
        after,
        List(loopPostcondition),
        post,
        name + " > [Q_loop] suffix [Q]")

      List(triplePrefix, tripleBody, tripleSuffix)
    }
  }
}

object SyncTotHandler extends LoopRuleHandler {
  def handle(loop: WhileLoopStmt, before: CompositeStmt, after: CompositeStmt, pre: Seq[Expr], post: Seq[Expr], name: String): Seq[Triple] = loop match {
    case WhileLoopStmt(cond, body, inv, Some(decr), rule) => {
      if (Main.logsActive) println("\tVerifying loop using \"syncTotRule\"")
      val mappedInvariant = inv.map(_._2)
      val combinedInvariant = mappedInvariant.reduceLeft((acc, x) => BinaryExpr(acc, "&&", x))
      val loopPostcondition = BinaryExpr(combinedInvariant, "&&", LoopRuleHandler.box(UnaryExpr("!", cond)))

      // check invariant I ⊨ low(b)
      val result = ParallelRunner.checkEntailment(combinedInvariant, LoopRuleHandler.low(cond))
      if (result._1 != SMTStatus.Unsatisfiable) sys.error("SyncTotHandler: Tried to apply \"syncTotRule\", but invariant \"I ⊨ low(b)\" was violated.")

      // check termination property
      if (!checkTerminationLoops(body)) {
        sys.error("SyncTotHandler: Tried to apply \"syncTotRule\", but loop termination is not checked for all sub-loops.")
      }

      val triplePrefix = Triple(
        before,
        pre,
        mappedInvariant,
        name + " > [P] prefix [I]")

      val freshVar = Id(LoopRuleHandler.genSym("*t"))

      val tripleBody = Triple(
        body,
        List(BinaryExpr(combinedInvariant, "&&", LoopRuleHandler.box(
          BinaryExpr(cond, "&&", BinaryExpr(decr, "==", freshVar))
        ))),
        List(BinaryExpr(combinedInvariant, "&&", LoopRuleHandler.box(
          BinaryExpr(BinaryExpr(decr, ">=", Num(0)), "&&", BinaryExpr(decr, "<", freshVar))
        ))),
        name + " > [I ∧ □b] body [I]")

      val tripleSuffix = Triple(
        after,
        List(loopPostcondition),
        post,
        name + " > [Q_loop] suffix [Q]")

      List(triplePrefix, tripleBody, tripleSuffix)
    }
    case WhileLoopStmt(_, _, _, None, _) => sys.error("SyncTotHandler: Tried to apply \"syncTotRule\", but loop termination is not checked (no \"decreases\" clause in loop itself).")
  }

  def checkTerminationLoops(stmt: Stmt): Boolean = stmt match {
    case WhileLoopStmt(_, body, _, Some(_), _) => checkTerminationLoops(body)
    case WhileLoopStmt(_, _, _, None, _) => false
    case CompositeStmt(stmts) => stmts.forall(x => checkTerminationLoops(x))
    case IfElseStmt(_, ifStmt, elseStmt) => checkTerminationLoops(ifStmt) && checkTerminationLoops(elseStmt)
    case _ => true
  }
}

object ExistsHandler extends LoopRuleHandler {
  def handle(loop: WhileLoopStmt, before: CompositeStmt, after: CompositeStmt, pre: Seq[Expr], post: Seq[Expr], name: String): Seq[Triple] = loop match {
    case WhileLoopStmt(cond, body, inv, Some(decr), rule) => {
      if (Main.logsActive) println("\tVerifying loop using \"existsRule\"")
      val mappedInvariant = inv.map(_._2).map(desugarQuantifiers)
      val (existsPartOpt, restPart) = extractFirstExists(mappedInvariant)

      if (existsPartOpt.isEmpty) {
        sys.error("ExistsHandler: Tried to apply \"existsRule\", but no top-level part of invariant is an exists clause.")
      }

      val triplePrefix = Triple(
        before,
        pre,
        mappedInvariant,
        name + " > [P] prefix [I]")

      val freshVar = Id(LoopRuleHandler.genSym("*t"))
      val existsPart = existsPartOpt.get
      val existsPartAssertVar = existsPart.assertVarDecls.head.vName
      val existsPartBody = existsPart.body match {
        case BinaryExpr(StateExistsExpr(_, _), "&&", right) => right
      }

      val tripleBody = Triple(
        IfElseStmt(cond, body, CompositeStmt(Nil)),
        restPart.prepended(Assertion("exists", existsPart.assertVarDecls, ImpliesExpr(StateExistsExpr(existsPartAssertVar, false),
          BinaryExpr(BinaryExpr(existsPartBody, "&&", LookupExpr(existsPartAssertVar, cond)), "&&",
          BinaryExpr(LookupExpr(existsPartAssertVar, decr), "==", freshVar))
        ))),
        restPart.prepended(Assertion("exists", existsPart.assertVarDecls, ImpliesExpr(StateExistsExpr(existsPartAssertVar, false),
          BinaryExpr(existsPartBody, "&&", BinaryExpr(LookupExpr(existsPartAssertVar, decr), "<", freshVar))
        ))),
        name + " > [I ∧ b(σ) ∧ e(σ) = v] if (b) {body} [I ∧ e(σ) < v]")

      val tripleRecursion = Triple(
        WhileLoopStmt(cond, body, restPart.prepended(existsPartBody).map((None, _)), Some(decr)),
        restPart.prepended(existsPartBody),
        restPart.prepended(existsPartBody),
        name + " > [I (no exists)] while (b) {body} [I (no exists)]"
      )

      val tripleSuffix = Triple(
        after,
        mappedInvariant.appended(LoopRuleHandler.box(UnaryExpr("!", cond))),
        post,
        name + " > [I ∧ □(¬b)] suffix [Q]")

      List(triplePrefix, tripleRecursion, tripleBody, tripleSuffix)
    }
    case WhileLoopStmt(_, _, _, None, _) => sys.error("ExistsHandler: Tried to apply \"existsRule\", but loop termination is not checked (no \"decreases\" clause in loop itself).")
  }

  def extractFirstExists(inv: Seq[Expr]): (Option[Assertion], Seq[Expr]) = {
    val (prefix, suffix) = inv.span {
      case Assertion("exists", List(AssertVarDecl(_, StateType())), _) => false
      case _ => true
    }
    suffix match {
      case x :: xs => (Some(x.asInstanceOf[Assertion]), prefix ++ xs)
      case Nil => (None, inv)
    }
  }
}

object RuleSelector {
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
      val result = ParallelRunner.checkEntailment(combinedInvariant, LoopRuleHandler.low(cond))

      if (result._1 == SMTStatus.Unsatisfiable) { // i.e. I ⊨ low(b) holds and we need a synchronized loop rule
        if (decr.isDefined && SyncTotHandler.checkTerminationLoops(body)) {
          SyncTotHandler
        } else {
          SyncHandler
        }
      }
      else { // i.e. I ⊨ low(b) doesn't hold and we need a non-synchronized loop rule
        if (decr.isDefined && ExistsHandler.extractFirstExists(mappedInvariant)._1.isDefined) {  // i.e. there is a decreases clause and the invariant contains an state exists assertion
          ExistsHandler
        } else {
          ForallExistsHandler
        }
      }
    }
  }
}