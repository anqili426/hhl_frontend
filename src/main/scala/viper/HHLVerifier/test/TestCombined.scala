package viper.HHLVerifier.test

import au.com.bytecode.opencsv.CSVWriter
import viper.HHLVerifier.Main
import viper.HHLVerifier.parsing.Parser

import java.io.{BufferedWriter, File, FileWriter}
import scala.jdk.CollectionConverters._

object TestCombined {

  // ---------- LOC counting config ----------
  val specKeyword    = List("requires", "ensures")
  val proofKeyword   = List("use", "hyperAssert", "hyperAssume", "declare", "reuse", "let", "invariant", "frame")
  val otherKeyword   = List("assume", "assert", "while", "if", "else", "}", "{", "havoc")
  val commentKeyword = List("//", "/*") // block comments not supported by this heuristic
  val defaultNumOfRep = 1
  val sleepMsBetweenTests = 5000L

  // ---------- Run configurations ----------
  final case class RunConfig(engine: String, extraArgs: List[String], smtModeLabel: String) {
    def isBoth: Boolean = smtModeLabel == "both"
  }

  val configs: List[RunConfig] = List(
    RunConfig(engine = "semantic",  extraArgs = Nil, smtModeLabel = "---"),
    RunConfig(engine = "syntactic", extraArgs = List("--syntactic", "--smtmode", "z3"), smtModeLabel = "z3"),
    RunConfig(engine = "syntactic", extraArgs = List("--syntactic", "--smtmode", "cvc5-proc"), smtModeLabel = "cvc5-proc"),
    RunConfig(engine = "syntactic", extraArgs = List("--syntactic", "--smtmode", "both"), smtModeLabel = "both")
  )

  // Suites: (suiteName, dir, optionArgToMain)
  val suites: List[(String, String, String)] = List(
    ("forall", "src/test/evaluation/forall", "--forall"),
    ("exists", "src/test/evaluation/exists", ""),
    ("forall-exists","src/test/evaluation/forall-exists", ""),
    ("exists-forall","src/test/evaluation/exists-forall", ""),
    //("syntactic", "src/test/evaluation/syntactic", ""),
    //("errors", "src/test/evaluation/errors/hypra", ""),
    //("types", "src/test/evaluation/types/hypra", "")
  )

  // ---------- LOC logic ----------
  def partOfCurrStmt(lineInd: Int, allNonemptyLines: Array[String]): Boolean = {
    if (lineInd < 0 || lineInd >= allNonemptyLines.length) return false

    val line = allNonemptyLines(lineInd).trim
    val allKeywords = specKeyword ++ proofKeyword ++ otherKeyword ++ commentKeyword

    if (allKeywords.exists(k => line.startsWith(k))) return false

    val isVarDecl = fastparse.parse(line, Parser.varDecl(_))
    val isAssignment = fastparse.parse(line, Parser.assign(_))
    !(isVarDecl.isSuccess || isAssignment.isSuccess)
  }

  def getDataForTestCase(testPath: String): Array[Int] = {
    val programSource = scala.io.Source.fromFile(testPath)
    val program = try programSource.mkString finally programSource.close()

    val allLines = program.split("\n")
    val allNonemptyLines = allLines.filter(l => l.trim.nonEmpty)
    val havocCount = allNonemptyLines.count(_.trim.startsWith("havoc"))


    var commentLOC = 0
    var specLOC = 0
    var proofLOC = 0
    var i = 0

    while (i < allNonemptyLines.length) {
      val line = allNonemptyLines(i).trim

      if (specKeyword.exists(k => line.startsWith(k))) {
        specLOC += 1
        var nextLineInd = i + 1
        while (partOfCurrStmt(nextLineInd, allNonemptyLines)) {
          specLOC += 1
          nextLineInd += 1
        }
        i = nextLineInd

      } else if (proofKeyword.exists(k => line.startsWith(k)) ||
        (line.contains("invariant") && fastparse.parse(line, Parser.hintDecl(_)).isSuccess)) {

        proofLOC += 1
        var nextLineInd = i + 1
        while (partOfCurrStmt(nextLineInd, allNonemptyLines)) {
          proofLOC += 1
          nextLineInd += 1
        }
        i = nextLineInd

      } else {
        if (commentKeyword.exists(k => line.startsWith(k))) commentLOC += 1
        i += 1
      }
    }

    val actualLOC = allNonemptyLines.length - commentLOC - specLOC - proofLOC
    Array(actualLOC, specLOC, proofLOC, havocCount)
  }

  // ---------- File discovery ----------
  def getListOfFiles(dir: String): List[File] = {
    val d = new File(dir)
    if (d.exists && d.isDirectory) {
      val content = d.listFiles
      val files = content.filter(_.isFile).toList
      val subDir = content.filter(_.isDirectory).toList
      files ++ subDir.flatMap(subD => getListOfFiles(subD.getPath))
    } else Nil
  }

  // ---------- Timing helpers ----------
  private def avgDurationSeconds(ts1: List[Long], ts2: List[Long], isBoth: Boolean): String = {
    if (isBoth) return "---"
    if (ts1.isEmpty || ts2.isEmpty) return "NaN"
    if (ts1.length != ts2.length) return "NaN"

    val avgNano = ts1.zip(ts2).map { case (a, b) => (b - a).toDouble }.sum / ts1.length
    (avgNano / 1e9).toString
  }

  // ---------- Running ----------
  final case class Summary(total: Int, failed: Int, runtimeTotal: Double, failedPaths: List[String])

  def runSuite(cfg: RunConfig, suiteName: String, tests: List[File], option: String): (List[Array[String]], Summary) = {
    var rows: List[Array[String]] = Nil
    var totalNum = 0
    var totalRuntime = 0.0
    var failed: List[String] = Nil

    for (f <- tests) {
      totalNum += 1
      val loc = getDataForTestCase(f.getPath)

      print(s"[$suiteName][${cfg.engine}][${cfg.smtModeLabel}] $f")

      // reset per-test instrumentation (important when looping configs)
      Main.numberOfTriples = 0
      Main.timeStamps = Array.fill(5)(List.empty[Long])
      Main.test = true
      Main.logsActive = false

      val argsForMain = (List(f.getPath, option, "--auto") ++ cfg.extraArgs).toArray
      Main.main(argsForMain)
      totalRuntime += Main.runtime

      val ok =
        (!f.getName.endsWith("false.hhl") && Main.verified == 2) ||
          (f.getName.endsWith("false.hhl") && Main.verified == 1)

      val res = if (ok) "Passed" else "Failed"
      println(if (ok) " OK" else " Failed")
      if (!ok) failed :+= f.getPath

      val durChar = avgDurationSeconds(Main.timeStamps(0), Main.timeStamps(1), cfg.isBoth)
      val durWP   = avgDurationSeconds(Main.timeStamps(1), Main.timeStamps(2), cfg.isBoth)
      val durEnc  = avgDurationSeconds(Main.timeStamps(2), Main.timeStamps(3), cfg.isBoth)
      val durSolv = avgDurationSeconds(Main.timeStamps(3), Main.timeStamps(4), cfg.isBoth)

      val triples =
        if (cfg.engine == "syntactic") Main.numberOfTriples.toString
        else "---"

      rows :+= Array(
        f.getPath,
        suiteName,
        option,
        cfg.engine,
        cfg.smtModeLabel,
        triples,
        Main.runtime.toString,
        durChar,
        durWP,
        durEnc,
        durSolv,
        res
      ) ++ loc.map(_.toString)

      Thread.sleep(sleepMsBetweenTests)
    }

    (rows, Summary(totalNum, failed.length, totalRuntime, failed))
  }

  def main(args: Array[String]): Unit = {
    val numOfRep =
      if (args.isEmpty) {
        println(s"Number of repetitions not specified. Running $defaultNumOfRep time(s).")
        defaultNumOfRep
      } else {
        val rep = args(0).toInt
        println("Number of repetitions: " + rep)
        rep
      }

    // Pre-load test lists once (same order across configs)
    val suiteFiles: List[(String, List[File], String)] =
      suites.map { case (name, dir, opt) => (name, getListOfFiles(dir), opt) }

    for (rep <- 0 until numOfRep) {
      println(s"=== Evaluation No. $rep starts ===")

      var allRows: List[Array[String]] = Nil

      for (cfg <- configs) {
        println(s"\n--- Running config: engine=${cfg.engine}, smtMode=${cfg.smtModeLabel} ---")

        var cfgTotal = 0
        var cfgFailed = 0
        var cfgRuntime = 0.0
        var cfgFailedPaths: List[String] = Nil

        for ((suiteName, tests, option) <- suiteFiles) {
          val (rows, summary) = runSuite(cfg, suiteName, tests, option)
          allRows ++= rows
          cfgTotal += summary.total
          cfgFailed += summary.failed
          cfgRuntime += summary.runtimeTotal
          cfgFailedPaths ++= summary.failedPaths
        }

        println(s"\nSummary [${cfg.engine}][${cfg.smtModeLabel}]")
        println(s"Total:   $cfgTotal")
        println(s"Failed:  $cfgFailed")
        println(s"Runtime: $cfgRuntime s")
        if (cfgFailed > 0) {
          println("Failed test cases:")
          cfgFailedPaths.foreach(println)
        }
      }

      val outputFilePath = s"src/test/evaluation/output_all_$rep.csv"
      val out = new BufferedWriter(new FileWriter(outputFilePath))
      val csvWriter = new CSVWriter(out)

      val header = Array(
        "Test case name",
        "Suite",
        "Option",
        "Engine",
        "SMT mode",
        "Number of triples",
        "Runtime total (s)",
        "Runtime Characterizer avg (s)",
        "Runtime WP avg (s)",
        "Runtime SMT encoding avg (s)",
        "Runtime SMT solving avg (s)",
        "Test result",
        "Actual LOC",
        "Spec LOC",
        "Proof LOC",
        "Havoc statements"
      )

      csvWriter.writeAll((List(header) ++ allRows).map(_.toArray).asJava)
      out.close()

      println(s"\nCombined test data saved to: $outputFilePath")
      println("=== Evaluation ended ===\n")
    }
  }
}