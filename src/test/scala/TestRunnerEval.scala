import org.scalatest.concurrent.TimeLimits.cancelAfter
import org.scalatest.funsuite.AnyFunSuite
import org.scalatest.time.SpanSugar._
import viper.HHLVerifier.generation.Generator
import viper.HHLVerifier.symbols.SymbolChecker
import viper.HHLVerifier.typing.TypeChecker

import java.nio.file.{Files, Path, Paths}
import scala.jdk.CollectionConverters._

class TestRunnerEval extends AnyFunSuite {

  // Location of test programs
  private val programDir: Path = Paths.get(getClass.getResource("/eval-tests").toURI)

  // Arguments we want to run the verifier with on the test programs
  private val args = Array("--auto", "--syntactic")

  Files.list(programDir).iterator().asScala
    .filter(Files.isRegularFile(_)) // skip directories
    .filter(_.getFileName.toString.toLowerCase.endsWith(".hhl")) // only .hhl files
    .foreach { file =>
      val expected = !file.getFileName.toString.endsWith("false.hhl")

      test(file.getFileName.toString) {
        cancelAfter(15.seconds) {
          SymbolChecker.reset()
          TypeChecker.reset()
          Generator.reset()
          viper.HHLVerifier.Main.logsActive = false
          viper.HHLVerifier.Main.verified = 0
          viper.HHLVerifier.Main.main(Array(file.toString) ++ args)

          val observed = viper.HHLVerifier.Main.verified
          val boolObserved = observed == 2

          assert(
            boolObserved == expected,
            s"expected VALID: $expected, but actual output was $boolObserved"
          )
        }
      }
    }
}
