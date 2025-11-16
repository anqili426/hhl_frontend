package viper.HHLVerifier.syntactic.smt

import viper.HHLVerifier.Main
import viper.HHLVerifier.ast._

import java.util.concurrent.{Callable, ExecutorCompletionService, Executors, Future, ThreadFactory, TimeUnit}
import scala.util.control.NonFatal

/**
 * Orchestrator for entailment checks across different SMT backends.
 *
 * [[ParallelRunner]] provides a single entry point, [[checkEntailment]], which:
 *  - delegates to a single backend (Z3, in-process CVC5, or external-process CVC5),
 *  - or runs a parallel "race" between two configured backends and returns
 *    the first decisive result.
 */
object ParallelRunner {
  private val timeout_ms: Long = 30000 // timeout in ms

  /**
   * Checks whether `pre ⊨ wp` using the configured SMT backend(s).
   *
   * This is the main entry point for entailment checks. It:
   *  - optionally adds the implication `pre ⇒ wp` to a global SMT pool for
   *    later export (via [[Z3Backend.addToGlobalSMTPool]]), and
   *  - then dispatches to the selected backend(s) according to `mode`:
   *    - [[BackendMode.Z3]]: uses [[Z3Backend]].
   *    - [[BackendMode.CVC5]]: uses in-process [[CVC5Backend]].
   *    - [[BackendMode.CVC5Proc]]: uses external-process [[CVC5ProcBackend]].
   *    - [[BackendMode.Both]]: runs a parallel race between two backends
   *      specified by [[Main.smtRaceModes]].
   *
   * The `toBeExported` flag is also passed down as the `usedForEval` flag to
   * the underlying backends, which may use it to record timing information for evaluation.
   *
   * @param pre The user-supplied precondition.
   * @param wp  The weakest precondition (usually computed by [[WeakestPrecondition.compute]]).
   * @param mode Which backend configuration to use (see above); defaults to [[Main.smtBackendMode]].
   * @param toBeExported If `true`, this entailment is (a) added to the global
   *                     SMT pool when exporting is enabled and (b) treated as
   *                     an evaluation run by the backends (enabling timing).
   * @return A pair `(status, backend)` where:
   *         - `status` is the [[SMTStatus]] returned by the backend(s),
   *         - `backend` is the [[BackendMode]] that produced the result
   *           (or [[BackendMode.Both]] if no single backend won decisively in the race mode,
   *           i.e., both backends report [[SMTStatus.Unknown]]).
   */
  def checkEntailment(pre: Expr, wp: Expr, mode: BackendMode = Main.smtBackendMode, toBeExported: Boolean = false): (SMTStatus, BackendMode) = {
    if (toBeExported && Main.outputPath != "unspecified") {
      val z3 = new Z3Backend
      z3.addToGlobalSMTPool(pre, wp)
    }
    mode match {
      case BackendMode.Z3 => {
        val z3 = new Z3Backend
        (z3.checkEntailment(pre, wp, toBeExported), BackendMode.Z3)
      }
      case BackendMode.CVC5 => {
        val cvc5 = new CVC5Backend
        (cvc5.checkEntailment(pre, wp, toBeExported), BackendMode.CVC5)
      }
      case BackendMode.CVC5Proc => {
        val cvc5proc = new CVC5ProcBackend
        (cvc5proc.checkEntailment(pre, wp, toBeExported), BackendMode.CVC5Proc)
      }
      case BackendMode.Both => {
        race(pre, wp, Main.smtRaceModes._1, Main.smtRaceModes._2, toBeExported)
      }
    }
  }

  /**
   * Runs a "race" between two SMT backends on the same entailment query.
   *
   * Both backends are started in parallel on daemon threads. The method:
   *  - waits up to [[timeout_ms]] (in total) for the first backend to finish,
   *  - if the first result is decisive (i.e., [[SMTStatus.Satisfiable]] or
   *    [[SMTStatus.Unsatisfiable]]), it tries to cancel the other backend and returns
   *    this result,
   *  - if the first result is [[SMTStatus.Unknown]], it waits (within the
   *    remaining time budget) for the second backend:
   *    - if the second returns a decisive (sat/unsat) result, that one wins,
   *    - if the second is also [[SMTStatus.Unknown]] or times out, the result
   *      is `(SMTStatus.Unknown, BackendMode.Both)`.
   *
   * If both backends time out or a non-fatal exception occurs, both tasks are
   * cancelled and `(SMTStatus.Unknown, BackendMode.Both)` is returned.
   *
   * @note: Each backend still enforces its own internal solver time limit
   *        (e.g. [[Main.smtSolverTimeLimitMs]]), and this race timeout acts as an
   *        additional global cap for the combined run.
   * @param pre The user-supplied precondition.
   * @param wp The weakest precondition (usually computed by [[WeakestPrecondition.compute]]).
   * @param mode1 First backend to race.
   * @param mode2 Second backend to race.
   * @param usedForEval Whether these entailments are used for evaluation/timing.
   * @return The first decisive result (sat/unsat) and the backend that produced it,
   *         or `(SMTStatus.Unknown, BackendMode.Both)` if there is no decisive winner.
   */
  private def race(pre: Expr, wp: Expr, mode1: BackendMode, mode2: BackendMode, usedForEval: Boolean = false): (SMTStatus, BackendMode) = {
    val daemonFactory = new ThreadFactory {
      private val d = Executors.defaultThreadFactory()
      override def newThread(r: Runnable): Thread = {
        val t = d.newThread(r)
        t.setDaemon(true)
        t.setName(s"SMT-${t.getId}")
        t
      }
    }
    val executor = Executors.newFixedThreadPool(2, daemonFactory)
    val executorService = new ExecutorCompletionService[(SMTStatus, BackendMode)](executor)
    var mode1Future: Future[(SMTStatus, BackendMode)] = null
    var mode2Future: Future[(SMTStatus, BackendMode)] = null

    val deadlineNs = System.nanoTime() + TimeUnit.MILLISECONDS.toNanos(timeout_ms)

    def remainingNs: Long = Math.max(0L, deadlineNs - System.nanoTime())

    try {
      mode1Future = executorService.submit(runOne(pre, wp, mode1, usedForEval))
      mode2Future = executorService.submit(runOne(pre, wp, mode2, usedForEval))

      // Get first completed result (could be unknown)
      val firstFuture = executorService.poll(remainingNs, TimeUnit.NANOSECONDS)

      if (firstFuture == null) {
        // Both futures timed out
        if (mode1Future != null) mode1Future.cancel(true)
        if (mode2Future != null) mode2Future.cancel(true)
        return (SMTStatus.Unknown, BackendMode.Both)
      }

      val first = firstFuture.get()
      first._1 match {
        case SMTStatus.Satisfiable | SMTStatus.Unsatisfiable => {
          // We have a clear result, cancel the other
          cancelOther(first._2, mode1, mode1Future, mode2, mode2Future)
          first
        }
        case SMTStatus.Unknown => {
          // Unclear result from the first, wait for the other
          val secondFuture = executorService.poll(remainingNs, TimeUnit.NANOSECONDS)

          // UNKNOWN from first, timeout from second
          if (secondFuture == null) return (SMTStatus.Unknown, BackendMode.Both)

          val second = secondFuture.get()
          second._1 match {
            case SMTStatus.Satisfiable | SMTStatus.Unsatisfiable => {
              // We have a clear result, cancel the other
              cancelOther(second._2, mode1, mode1Future, mode2, mode2Future)
              second
            }
            case SMTStatus.Unknown => (SMTStatus.Unknown, BackendMode.Both)
          }
        }
      }
    } catch {
      case NonFatal(_) =>
        if (mode1Future != null) mode1Future.cancel(true)
        if (mode2Future != null) mode2Future.cancel(true)
        (SMTStatus.Unknown, BackendMode.Both)
    } finally {
      executor.shutdownNow()
    }
  }

  /**
   * Helper function to create a [[Callable]] that runs a single backend on `pre ⊨ wp`.
   */
  private def runOne(pre: Expr, wp: Expr, mode: BackendMode, usedForEval: Boolean = false): Callable[(SMTStatus, BackendMode)] = {
    () => {
      val backend = mode match {
        case BackendMode.Z3 => new Z3Backend
        case BackendMode.CVC5 => new CVC5Backend
        case BackendMode.CVC5Proc => new CVC5ProcBackend
      }
      (backend.checkEntailment(pre, wp, usedForEval), mode)
    }
  }

  /**
   * Helper function to cancel the losing backend's future in a two-backend race.
   */
  private def cancelOther(winner: BackendMode,
                          mode1: BackendMode, mode1Future: Future[(SMTStatus, BackendMode)],
                          mode2: BackendMode, mode2Future: Future[(SMTStatus, BackendMode)]): Unit = {
    if (winner == mode1) {
      if (mode2Future != null) mode2Future.cancel(true)
    } else if (winner == mode2) {
      if (mode1Future != null) mode1Future.cancel(true)
    } else {
      // Shouldn't happen, but better safe than sorry
      if (mode1Future != null) mode1Future.cancel(true)
      if (mode2Future != null) mode2Future.cancel(true)
    }
  }

  /**
   * Helper function to resolve all plain identifiers in an expression into state lookups.
   */
  def resolveLookup(expr: Expr)(implicit assertVar: AssertVar): Expr = expr match {
    case Id(_) => LookupExpr(assertVar, expr)
    case Num(_) | BoolLit(_) => expr
    case BinaryExpr(e1, op, e2) => BinaryExpr(resolveLookup(e1), op, resolveLookup(e2))
    case UnaryExpr(op, e) => UnaryExpr(op, resolveLookup(e))
    case ImpliesExpr(left, right) => ImpliesExpr(resolveLookup(left), resolveLookup(right))
    case _ => sys.error("ParallelRunner: Unexpected expression in lookup expression: " + expr.toString)
  }
}
