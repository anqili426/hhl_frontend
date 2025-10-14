package viper.HHLVerifier.syntactic.handler

import viper.HHLVerifier.Main
import viper.HHLVerifier.ast._
import viper.HHLVerifier.syntactic.SyntacticEngine.Triple
import viper.HHLVerifier.syntactic.WeakestPrecondition.desugarQuantifiers
import viper.HHLVerifier.syntactic.smt.{ParallelRunner, SMTStatus}
import viper.HHLVerifier.typing.StateType

sealed trait LoopRuleHandler {
  /**
   * Processes a `while` loop into a sequence of verification triples based on the respective loop rule.
   * An overview over the different loop rules can be found in the Hypra paper, Fig. 8 (page 15).
   *
   * @param loop the loop statment to handle
   * @param before statements executed '''before''' the loop (prefix)
   * @param after statements executed '''after''' the loop (suffix)
   * @param pre precondition for the whole program `before | loop | after`
   * @param post postcondition for the whole program `before | loop | after`
   * @param name human-readable name used for logging/reporting.
   * @return independent verification triples for the prefix, the loop body, and the suffix. The exact shape of the
   *         triples depends on the applied loop rule.
   */
  def handle(loop: WhileLoopStmt, before: CompositeStmt, after: CompositeStmt, pre: Seq[Expr], post: Seq[Expr], name: String): Seq[Triple]
}

object ForallExistsHandler extends LoopRuleHandler {
  def handle(loop: WhileLoopStmt, before: CompositeStmt, after: CompositeStmt, pre: Seq[Expr], post: Seq[Expr], name: String): Seq[Triple] = loop match {
    case WhileLoopStmt(cond, body, inv, decr, rule) => {
      if (Main.logsActive) println("\tVerifying loop using \"forallExistsRule\"")
      val mappedInvariant = inv.map(_._2)
      val loopPostcondition = BinaryExpr(computeLoopPost(mappedInvariant.reduceLeft((acc, x) => BinaryExpr(acc, "&&", x)))(cond), "&&", LoopUtils.box(UnaryExpr("!", cond)))

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
      val loopPostcondition = BinaryExpr(BinaryExpr(combinedInvariant, "||", LoopUtils.box(BoolLit(false))), "&&", LoopUtils.box(UnaryExpr("!", cond)))

      // check invariant I ⊨ low(b)
      val result = ParallelRunner.checkEntailment(combinedInvariant, LoopUtils.low(cond))
      if (result._1 != SMTStatus.Unsatisfiable) sys.error("SyncHandler: Tried to apply \"syncRule\", but invariant \"I ⊨ low(b)\" was violated.")

      val triplePrefix = Triple(
        before,
        pre,
        mappedInvariant,
        name + " > [P] prefix [I]")

      val tripleBody = Triple(
        body,
        List(BinaryExpr(combinedInvariant, "&&", LoopUtils.box(cond))),
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
      val loopPostcondition = BinaryExpr(combinedInvariant, "&&", LoopUtils.box(UnaryExpr("!", cond)))

      // check invariant I ⊨ low(b)
      val result = ParallelRunner.checkEntailment(combinedInvariant, LoopUtils.low(cond))
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

      val freshVar = Id(LoopUtils.genSym("*t"))

      val tripleBody = Triple(
        body,
        List(BinaryExpr(combinedInvariant, "&&", LoopUtils.box(
          BinaryExpr(cond, "&&", BinaryExpr(decr, "==", freshVar))
        ))),
        List(BinaryExpr(combinedInvariant, "&&", LoopUtils.box(
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

      val freshVar = Id(LoopUtils.genSym("*t"))
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
        mappedInvariant.appended(LoopUtils.box(UnaryExpr("!", cond))),
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