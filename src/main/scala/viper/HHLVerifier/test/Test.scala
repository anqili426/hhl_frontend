package viper.HHLVerifier.test

import viper.HHLVerifier.{Main, Parser, ViperRunner}
import au.com.bytecode.opencsv.CSVWriter

import java.io.{BufferedWriter, File, FileWriter}
import scala.jdk.CollectionConverters._

object Test {

  var failedForAll: List[String] = List.empty
  var failedExists: List[String] = List.empty
  var failedOther: List[String] = List.empty
  var totalNum = 0
  var totalRuntime = 0.0

  val specKeyword = List("requires", "ensures")
  val proofKeyword = List("use", "hyperAssert", "hyperAssume", "declare", "reuse", "let", "invariant", "frame")
  val otherKeyword = List("assume", "assert", "while", "if", "else", "}", "{", "havoc")
  val commentKeyword = List("//", "/*") // The current implementation doesn't support the counting of block comments
  val defaultNumOfRep = 1

  def partOfCurrStmt(lineInd: Int, allNonemptyLines: Array[String]): Boolean = {

    val line = allNonemptyLines(lineInd).trim
    val allKeywords = specKeyword ++ proofKeyword ++ otherKeyword ++ commentKeyword

    if (allKeywords.exists(k => line.startsWith(k))) {
      return false
    }

    val isVarDecl = fastparse.parse(line, Parser.varDecl(_))
    val isAssignment = fastparse.parse(line, Parser.assign(_))
    if (isVarDecl.isSuccess || isAssignment.isSuccess) {
      return false
    }
    true
  }

  def getDataForTestCase(testPath: String): Array[Int] = {
    val programSource = scala.io.Source.fromFile(testPath)
    val program = programSource.mkString
    programSource.close()
    val allLines = program.split("\n")
    val allNonemptyLines = allLines.filter(l => l.trim.nonEmpty)

    var commentLOC = 0
    var specLOC = 0
    var proofLOC = 0
    var i = 0

    while (i < allNonemptyLines.length) {
      val line = allNonemptyLines(i).trim
      if (specKeyword.exists(k => line.startsWith(k))) {
        specLOC = specLOC + 1
        var nextLineInd = i + 1
        while (partOfCurrStmt(nextLineInd, allNonemptyLines)) {
          nextLineInd = nextLineInd + 1
          specLOC = specLOC + 1
        }
        i = nextLineInd
      } else if (proofKeyword.exists(k => line.startsWith(k)) || (line.contains("invariant") && fastparse.parse(line, Parser.hintDecl(_)).isSuccess)) {
        proofLOC = proofLOC + 1
        var nextLineInd = i + 1
        while (partOfCurrStmt(nextLineInd, allNonemptyLines)) {
          nextLineInd = nextLineInd + 1
          proofLOC = proofLOC + 1
        }
        i = nextLineInd
      } else {
        if (commentKeyword.exists(k => line.startsWith(k))) {
          commentLOC = commentLOC + 1
        }
        i = i + 1
      }
    }

    val actualLOC = allNonemptyLines.length - commentLOC - specLOC - proofLOC
    Array(actualLOC, specLOC, proofLOC)
  }

  def runTests(tests: List[File], option: String): List[Array[String]] = {
    var allData: List[Array[String]] = List.empty
    for (f <- tests) {
      totalNum = totalNum + 1
      val LOCData = getDataForTestCase(f.getPath)
      print(f)
      val argsForMain = Array(f.getPath, option, "--auto")
      Main.test = true
      Main.main(argsForMain)
      totalRuntime = totalRuntime + Main.runtime

      var res = "Failed"
      if ((!f.getName.endsWith("false.hhl") && Main.verified != 2) || (f.getName.endsWith("false.hhl") && Main.verified != 1)) {
        println(" Failed")
        println(Main.errMessages)
        if (option == "--forall") failedForAll = failedForAll :+ f.getPath
        else if (option == "--exists") failedExists = failedExists :+ f.getPath
        else failedOther = failedOther :+ f.getPath
      } else {
        println(" OK")
        res = "Passed"
      }

      val data = Array(f.getPath, option, Main.runtime.toString, res) ++ LOCData.map(i => i.toString)
      allData = allData :+ data
      Thread.sleep(5000)
    }
    allData
  }

  def main(args: Array[String]): Unit = {
    val numOfRep = if (args.length == 0) {
      println("Number of repetitions is not specified. Evaluation will be run for "+  defaultNumOfRep  + " time(s) by default. ")
      defaultNumOfRep
    } else {
      val rep = args(0).toInt
      println("Number of repetitions: " + rep)
      rep
    }

    val pathOfForAllTests = "src/test/evaluation/forall"
    val pathOfExistsTests = "src/test/evaluation/exists"
    val pathOfForAllExistsTests = "src/test/evaluation/forall-exists"
    val pathOfExistsForAllTests = "src/test/evaluation/exists-forall"

    val forAllTests = getListOfFiles(pathOfForAllTests)
    val existsTests = getListOfFiles(pathOfExistsTests)
    val forAllExistsTests = getListOfFiles(pathOfForAllExistsTests)
    val existsForAllTests = getListOfFiles(pathOfExistsForAllTests)

    var i = 0
    for (i <- 0 to numOfRep - 1) {
      println("Evaluation No. " + i + " starts")

      var allTestData: List[Array[String]] = List.empty
      allTestData = allTestData ++ runTests(forAllTests, "--forall")
      allTestData = allTestData ++ runTests(existsTests, "")
      allTestData = allTestData ++ runTests(forAllExistsTests, "")
      allTestData = allTestData ++ runTests(existsForAllTests, "")
      val failedNum = failedForAll.length + failedExists.length + failedOther.length

      println("---------------------")
      println("Total: " + totalNum)
      println("Failed: " + failedNum)
      if (failedNum > 0) {
        println("Failed forall tests: " + failedForAll.length)
        failedForAll.foreach(t => println(t))
        println("Failed exists tests: " + failedExists.length)
        failedExists.foreach(t => println(t))
        println("Failed forall-exists and exists-forall tests: " + failedOther.length)
        failedOther.foreach(t => println(t))
      }
      println("Runtime: " + totalRuntime + " s")

      val outputFilePath = "src/test/evaluation/output" + i + ".csv"
      val outputFile = new BufferedWriter(new FileWriter(outputFilePath))
      val csvWriter = new CSVWriter(outputFile)
      val schema = Array("Test case name", "Option", "Runtime (s)", "Test result", "Actual LOC", "Spec LOC", "Proof LOC")
      val dataToWrite = List(schema) ++ allTestData
      csvWriter.writeAll(dataToWrite.map(_.toArray).asJava)
      outputFile.close()
      println("Test data is saved to: " + outputFilePath)

      // Reset
      failedForAll = List.empty
      failedExists = List.empty
      failedOther = List.empty
      totalNum = 0
      totalRuntime = 0.0
      if (numOfRep > 1) println("*********************")
    }
    println("Evaluation has ended. ")
  }

  def getListOfFiles(dir: String): List[File] = {
    val d = new File(dir)
    if (d.exists && d.isDirectory) {
      val content = d.listFiles
      val files = content.filter(_.isFile).toList
      val subDir = content.filter(_.isDirectory).toList
      files ++ subDir.flatMap(subD => getListOfFiles(subD.getPath))
    } else {
      List[File]()
    }
  }
}
