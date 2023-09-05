package viper.HHLVerifier
import java.io.File

object Test {

  def main(args: Array[String]): Unit = {
    val pathOfForAllTests = "src/test/evaluation/forall/test"
    val pathOfExistsTests = "src/test/evaluation/exists"

    val forAllTests = getListOfFiles(pathOfForAllTests)
    val existsTests = getListOfFiles(pathOfExistsTests)
    val totalNum = forAllTests.length + existsTests.length

    var failedForAll: List[String] = List.empty
    var failedExists: List[String] = List.empty
    var totalRuntime = 0

    println("Evaluation starts")
    for (f <- forAllTests) {
      println(f)
      val argsForMain = Array(f.getPath,"--forall")
      Main.main(argsForMain)
      // Get result
      // Get runtime
      // Check if result is expected
    }

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
    println("Runtime: " + totalRuntime)
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
