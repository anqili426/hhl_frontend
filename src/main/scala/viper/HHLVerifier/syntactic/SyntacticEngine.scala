package viper.HHLVerifier.syntactic

import com.microsoft.z3._
import viper.HHLVerifier.ast._
import PathBuilder._
import viper.HHLVerifier.typing.StateType
import viper.HHLVerifier.Main
import viper.HHLVerifier.syntactic.handler._
import viper.HHLVerifier.syntactic.smt.{ParallelRunner, SMTStatus}

import java.nio.file.{Files, Paths}

object SyntacticEngine {

  /**
   * Global status code tracking the overall verification result. This variable
   * is mutated during verification.
   *
   * Values:
   *  - `0` if no methods were checked or the result is unknown,
   *  - `1` if at least one verification failed,
   *  - `2` if all verifications succeeded.
   */
  private var verificationResult: Int = 0

  /**
   * Buffer of Z3 boolean formulas collected during program analysis. If the corresponding flag is
   * set, these constraints are combined and exported to an `.smt2` file, typically for external processing
   * by an SMT solver
   */
  private var z3Constraints: Seq[BoolExpr] = Seq()

  var exportCtx = new Context()

  def addConstraint(expr: BoolExpr): Unit = {
    z3Constraints = z3Constraints.appended(expr)
  }

  def reset(): Unit = {
    exportCtx.close()
    exportCtx = new Context()
    z3Constraints = Seq()
    verificationResult = 0
  }

  /**
   * Represents a verification hyper-triple consisting of a program statement, a precondition
   * and a postcondition. It may optionally carry a name, used e.g. for diagnostic messages.
   *
   * @param stmt The program statement to be verified
   * @param pre A sequence of hyper-assertions forming the precondition.
   * @param post A sequence of hyper-assertions forming the postcondition.
   * @param name An optional descriptive name for the triple
   */
  case class Triple(
                     stmt: Stmt,
                     pre: Seq[viper.HHLVerifier.ast.Expr],
                     post: Seq[viper.HHLVerifier.ast.Expr],
                     name: String = ""
                   )

  /**
   * Verifies all methods in a given [[HHLProgram]].
   *
   * For each method, the corresponding hyper-triple is split into one or multiple
   * loop-free verification triples according to the HHL proof rules. Each hyper-triple is verified
   * by checking whether the precondition entails the syntactically derived ''weakest precondition (WP)''.
   *
   * @param program The HHL program to verify.
   * @return An integer result code corresponding to [[Main.verified]]:
   *         - `0` if no methods were checked or the result is unknown,
   *         - `1` if at least one verification failed,
   *         - `2` if all verifications succeeded.
   */
  def verify(program: HHLProgram): Int = {
    reset()

    program.methods.foreach { method =>
      if (Main.logsActive) println("----------")
      if (Main.logsActive) println("Method \"" + method.mName + "\"")

      val split = structuralSplit(Triple(method.body, method.pre, method.post, "top-level"))
      if (Main.debugLogsActive) println("Split: " + split)
      Main.numberOfTriples += split.length

      // Verifying all triples
      split match {
        case h +: t =>
          verifySplitFreeTriple(h, wpPlus = false)  // first triple without extended WP
          t.foreach(tr => verifySplitFreeTriple(tr, wpPlus = true))  // rest of the triples need extended WP
      }
    }
    if (Main.outputPath != "unspecified") exportToSMT()
    verificationResult
  }

  /**
   * Verifies a split-free hyper-triple by syntactically computing the weakest precondition
   * of the statement with respect to its postcondition and checking whether the precondition entails it.
   *
   * @param triple The hyper-triple consisting of a statement, preconditions, postconditions, and an optional name.
   * @param wpPlus boolean flag whether we want to compute extended WP for error states. The extended WP
   *               has the purpose of propagating errors happening in triples before. Should be true for all triples
   *               except the first one.
   * @return `true` if the triple is valid (precondition entails weakest precondition),
   *         `false` otherwise.
   * @note Updates the global variable [[verificationResult]] accordingly as a side effect.
   */
  private def verifySplitFreeTriple(triple: Triple, wpPlus: Boolean): Boolean = triple match {
    case Triple(body, pre, post, name) => {
      val trueAssertion = Assertion("forall", List(AssertVarDecl(AssertVar("_s"), StateType())), ImpliesExpr(StateExistsExpr(AssertVar("_s"), false), BoolLit(true)))
      if (pre.isEmpty) {
        verifySplitFreeTriple(Triple(body, List(trueAssertion), post, name), wpPlus)
      } else if (post.isEmpty) {
        verifySplitFreeTriple(Triple(body, pre, List(trueAssertion), name), wpPlus)
      } else {
        Main.timeStamps(0) = Main.timeStamps(0).appended(System.nanoTime()) // timestamp start of triple
        val characterizer: Characterizer = PathBuilder.characterizeStmt(body)
        Main.timeStamps(1) = Main.timeStamps(1).appended(System.nanoTime()) // timestamp after characterizer
        if (Main.debugLogsActive) println("Characterizer: " + characterizer)
        if (Main.debugLogsActive) println("#paths: " + characterizer.paths.length)

        val weakestPrecondition: viper.HHLVerifier.ast.Expr = WeakestPrecondition.compute(characterizer, post, wpPlus)
        Main.timeStamps(2) = Main.timeStamps(2).appended(System.nanoTime()) // timestamp after WP
        val combinedPrecondition: viper.HHLVerifier.ast.Expr = pre.reduceLeft((acc, x) => BinaryExpr(acc, "&&", x))
        if (Main.debugLogsActive) println("Pre: " + combinedPrecondition)
        if (Main.debugLogsActive) println("WP: " + weakestPrecondition)

        val result = ParallelRunner.checkEntailment(combinedPrecondition, weakestPrecondition, toBeExported = true)
        Main.timeStamps(4) = Main.timeStamps(4).appended(System.nanoTime()) // timestamp after SMT solving

        val detailedRuntimes = (
          (Main.timeStamps(1).last - Main.timeStamps(0).last) / 1E9,
          (Main.timeStamps(2).last - Main.timeStamps(1).last) / 1E9,
          (Main.timeStamps(3).last - Main.timeStamps(2).last) / 1E9,
          (Main.timeStamps(4).last - Main.timeStamps(3).last) / 1E9,
        )

        result._1 match {
          case SMTStatus.Satisfiable => {
            if (Main.logsActive) println(f"\t${result._2} > Invalid ($name): Counterexample found. $detailedRuntimes")
            verificationResult = 1
            false
          }
          case SMTStatus.Unsatisfiable => {
            if (Main.logsActive) println(f"\t${result._2} > Valid ($name): Precondition entails WP. $detailedRuntimes")
            if (verificationResult != 1) verificationResult = 2
            true
          }
          case SMTStatus.Unknown => {
            if (Main.logsActive) println(f"\t${result._2} > Unknown ($name): SMT solver couldn't determine the result. $detailedRuntimes")
            verificationResult = 1 // we handle "unknown" as invalid
            false
          }
        }
      }
    }
  }

  /**
   * Decide whether a statement must be split and in further consequence be accordingly transformed by a handler.
   *
   * @param stmt the statement on which the check should be performed
   * @return `true` iff a split is necessary for this statement
   */
  def hasStructuralSplit(s: Stmt): Boolean = s match {
    case CompositeStmt(xs) => xs.exists(hasStructuralSplit)
    case _: WhileLoopStmt => true
    case _: MethodCallStmt => true
    case _: MultiAssignStmt => true
    case IfElseStmt(_, ifStmt, elseStmt) => hasStructuralSplit(ifStmt) || hasStructuralSplit(elseStmt)
    case _ => false
  }

  /**
   * Splits a hyper-triple into multiple split-free hyper-triples according to the HHL proof rules.
   *
   * @param triple The hyper-triple to split.
   * @return A sequence of triples corresponding to the decomposed program. If no split-point is found,
   *         returns the original triple.
   */
  private def structuralSplit(triple: Triple): Seq[Triple] = triple match {
    case Triple(stmt, pre, post, name) => {
      stmt match {
        case CompositeStmt(stmts) => {
          val (before, targetAndAfter) = stmts.span(!hasStructuralSplit(_))
          targetAndAfter match {
            // Handle while loop according to the corresponding loop rule
            case (ws @ WhileLoopStmt(_, _, _, _, _)) :: after => {
              val ruleHandler = LoopRuleSelector.select(ws)
              ruleHandler
                .handle(ws, CompositeStmt(before), CompositeStmt(after), pre, post, name)
                .flatMap(structuralSplit)
            }
            // Handle a method call
            case (call @ (MethodCallStmt(_, _) | MultiAssignStmt(_, _))) :: after => {
              MethodCallHandler
                .handle(call, CompositeStmt(before), CompositeStmt(after), pre, post, name)
                .flatMap(structuralSplit)
            }
            // Handle an if-else statement
            case (ifs @ IfElseStmt(_, _, _)) :: after => {
              IfElseHandler
                .handle(ifs, CompositeStmt(before), CompositeStmt(after), pre, post, name)
                .flatMap(structuralSplit)
            }
            // No split point found in sequence, just return the original triple
            case _ => List(triple)
          }
        }
        case ifs @ IfElseStmt(_, _, _) => {
          if (hasStructuralSplit(ifs)) {
            IfElseHandler
              .handle(ifs, CompositeStmt(Nil), CompositeStmt(Nil), pre, post, name)
              .flatMap(structuralSplit)
          } else {
            List(triple)
          }
        }
        case MethodCallStmt(_, _) | MultiAssignStmt(_, _) => {
          MethodCallHandler
            .handle(stmt, CompositeStmt(Nil), CompositeStmt(Nil), pre, post, name)
            .flatMap(structuralSplit)
        }
        case ws @ WhileLoopStmt(_, _, _, _, _) => {
          val ruleHandler = LoopRuleSelector.select(ws)
          ruleHandler
            .handle(ws, CompositeStmt(Nil), CompositeStmt(Nil), pre, post, name)
            .flatMap(structuralSplit)
        }
        case _ => List(triple)
      }
    }
  }

  private def getAllProgVars(method: Method): Seq[Id] = {
    method.params ++ method.res ++ getAllProgVarsHelper(method.body).toSeq
  }

  private def getAllProgVarsHelper(stmt: Stmt): Set[Id] = stmt match {
    case CompositeStmt(x :: xs) => getAllProgVarsHelper(x) ++ getAllProgVarsHelper(CompositeStmt(xs))
    case IfElseStmt(_, ifStmt, elseStmt) => getAllProgVarsHelper(ifStmt) ++ getAllProgVarsHelper(elseStmt)
    case WhileLoopStmt(_, body, _, _, _) => getAllProgVarsHelper(body)
    case PVarDecl(vName, _) => Set(vName)
    case _ => Set.empty[Id]
  }

  private def exportToSMT(): Unit = {
    val s = exportCtx.mkSolver()
    if (z3Constraints.isEmpty) sys.error("SyntacticEngine: Nothing to export")

    val finalFormula = exportCtx.mkNot(exportCtx.mkAnd(z3Constraints: _*))
    s.add(finalFormula)

    val outputString = // "(set-logic AUFLIA)\n" +
        s.toString +
        "\n(check-sat)\n(exit)\n"

    Files.write(Paths.get(Main.outputPath), outputString.getBytes)
    if (Main.logsActive) println("The corresponding SMT file has been written to " + Paths.get(Main.outputPath))
  }
}

