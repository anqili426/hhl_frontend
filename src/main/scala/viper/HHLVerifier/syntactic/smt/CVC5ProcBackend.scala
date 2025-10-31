package viper.HHLVerifier.syntactic.smt
import viper.HHLVerifier.Main
import viper.HHLVerifier.ast.Expr

import java.nio.file.{Files, Path}
import scala.sys.process._

class CVC5ProcBackend extends SMTBackend {
  def checkEntailment(pre: Expr, wp: Expr, usedForEval: Boolean = false): SMTStatus = {
    val z3 = new Z3Backend
    val smtEncoding = z3.generateSingleSMTEncoding(pre, wp)

    if (usedForEval) Main.timeStamps(3) = Main.timeStamps(3).appended(System.nanoTime()) // timestamp after SMT encoding

    val tmpPath: Path = Files.createTempFile("hhl-entailment-", ".smt2")
    Files.write(tmpPath, smtEncoding.getBytes)

    try {
      val cmd = Seq(
        Main.cvc5Path,
        "--lang", "smt2",
        "--tlimit=" + Main.smtSolverTimeLimitMs.toString,
        tmpPath.toString
      )

      val out = new StringBuilder
      val err = new StringBuilder

      cmd.!(ProcessLogger(o => out.append(o).append('\n'), e => err.append(e).append('\n')))

      val firstLine = out
        .toString
        .split("\\R")
        .iterator
        .map(_.trim)
        .find(_.nonEmpty)
        .getOrElse("")

      firstLine match {
        case "sat" => SMTStatus.Satisfiable
        case "unsat" => SMTStatus.Unsatisfiable
        case "unknown" => SMTStatus.Unknown
        case _ => SMTStatus.Unknown
      }
    } finally {
      if (!Main.keepSmtFiles) Files.deleteIfExists(tmpPath)
    }
  }
}
