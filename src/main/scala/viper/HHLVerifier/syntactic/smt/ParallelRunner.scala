package viper.HHLVerifier.syntactic.smt

import viper.HHLVerifier.Main
import viper.HHLVerifier.ast._

import java.util.concurrent.{Callable, ExecutorCompletionService, Executors, Future, ThreadFactory, TimeUnit}
import java.nio.file.{Files, Path}
import scala.sys.process._
import scala.util.control.NonFatal

object ParallelRunner {
  private val timeout_ms: Long = 30000 // timeout in ms

  def checkEntailment(pre: Expr, wp: Expr, mode: BackendMode = Main.smtBackendMode, toBeExported: Boolean = false): (SMTStatus, BackendMode) = {
    if (toBeExported && Main.outputPath != "unspecified") {
      val z3 = new Z3Backend
      z3.addToGlobalSMTPool(pre, wp)
    }
    mode match {
      case BackendMode.Z3 => {
        val z3 = new Z3Backend
        (z3.checkEntailment(pre, wp), BackendMode.Z3)
      }
      case BackendMode.CVC5 => {
        val cvc5 = new CVC5Backend
        (cvc5.checkEntailment(pre, wp), BackendMode.CVC5)
      }
      case BackendMode.CVC5Proc => {
        val cvc5proc = new CVC5ProcBackend
        (cvc5proc.checkEntailment(pre, wp), BackendMode.CVC5Proc)
      }
      case BackendMode.Both => {
        race(pre, wp, Main.smtRaceModes._1, Main.smtRaceModes._2)
      }
    }
  }

  private def race(pre: Expr, wp: Expr, mode1: BackendMode, mode2: BackendMode): (SMTStatus, BackendMode) = {
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
      mode1Future = executorService.submit(runOne(pre, wp, mode1))
      mode2Future = executorService.submit(runOne(pre, wp, mode2))

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
          cancelOther(first._2, mode1Future, mode2Future)
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
              cancelOther(second._2, mode1Future, mode2Future)
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

  private def runOne(pre: Expr, wp: Expr, mode: BackendMode): Callable[(SMTStatus, BackendMode)] = {
    () => {
      val backend = mode match {
        case BackendMode.Z3 => new Z3Backend
        case BackendMode.CVC5 => new CVC5Backend
        case BackendMode.CVC5Proc => new CVC5ProcBackend
      }
      (backend.checkEntailment(pre, wp), mode)
    }
  }

  private def cancelOther(winner: BackendMode, z3Future: Future[(SMTStatus, BackendMode)], cvc5Future: Future[(SMTStatus, BackendMode)]): Unit = winner match {
    case BackendMode.Z3 => if (cvc5Future != null) cvc5Future.cancel(true)
    case BackendMode.CVC5 => if (z3Future != null) z3Future.cancel(true)
  }

  def resolveLookup(expr: Expr)(implicit assertVar: AssertVar): Expr = expr match {
    case Id(_) => LookupExpr(assertVar, expr)
    case Num(_) | BoolLit(_) => expr
    case BinaryExpr(e1, op, e2) => BinaryExpr(resolveLookup(e1), op, resolveLookup(e2))
    case UnaryExpr(op, e) => UnaryExpr(op, resolveLookup(e))
    case ImpliesExpr(left, right) => ImpliesExpr(resolveLookup(left), resolveLookup(right))
    case _ => sys.error("ParallelRunner: Unexpected expression in lookup expression: " + expr.toString)
  }
}
