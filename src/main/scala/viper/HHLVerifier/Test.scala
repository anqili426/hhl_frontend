package viper.HHLVerifier
import java.io.File

object Test {

  var failedForAll: List[String] = List.empty
  var failedExists: List[String] = List.empty
  var totalRuntime = 0.0

  def runTests(tests: List[File], option: String): Unit = {
    for (f <- tests) {
      print(f)
      val argsForMain = Array(f.getPath, "--" + option)
      Main.test = true
      Main.main(argsForMain)
      totalRuntime = totalRuntime + Main.runtime
      if ((!f.getName.endsWith("false.txt") && !Main.verified) || (f.getName.endsWith("false.txt") && Main.verified)) {
        println(" Failed")
        if (option == "forall") failedForAll = failedForAll :+ f.getPath
        else if (option == "exists") failedExists = failedExists :+ f.getPath
      } else println(" OK")
    }
  }

  def main(args: Array[String]): Unit = {
    val pathOfForAllTests = "src/test/evaluation/forall"
    val pathOfExistsTests = "src/test/evaluation/exists"

    val forAllTests = getListOfFiles(pathOfForAllTests)
    val existsTests = getListOfFiles(pathOfExistsTests)
    val totalNum = forAllTests.length + existsTests.length

    println("Evaluation starts")
    // runTests(forAllTests, "forall")
    runTests(existsTests, "exists")

    val failedNum = failedForAll.length + failedExists.length
    println("---------------------")
    println("Total: " + totalNum)
    println("Failed: " + failedNum)
    if (failedNum > 0) {
      println("Failed forall tests: " + failedForAll.length)
      failedForAll.foreach(t => println(t))
      println("Failed exists tests: " + failedExists.length)
      failedExists.foreach(t => println(t))
    }
    println("Runtime: " + totalRuntime + " ns")
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
