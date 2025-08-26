import org.scalatest.funsuite.AnyFunSuite
import org.scalatest.concurrent.TimeLimits.{cancelAfter, failAfter}
import org.scalatest.time.SpanSugar._
import viper.HHLVerifier.generation.Generator
import viper.HHLVerifier.symbols.SymbolChecker
import viper.HHLVerifier.syntactic.SyntacticEngine
import viper.HHLVerifier.typing.TypeChecker

import scala.jdk.CollectionConverters._
import java.nio.file.{Files, Path, Paths}

class TestRunner extends AnyFunSuite {

  // Location of test programs
  private val programDir: Path = Paths.get(getClass.getResource("/hypra-tests").toURI)

  // Arguments we want to run the verifier with on the test programs
  private val args = Array("--auto", "--syntactic")

  // Regex for checking "// VALID: <bool>" annotation at beginning of .hhl file
  private val ValidTag = """(?i)//\s*valid\s*:\s*(true|false)\s*""".r

  Files.list(programDir).iterator().asScala
    .filter(Files.isRegularFile(_)) // skip directories
    .filter(_.getFileName.toString.toLowerCase.endsWith(".hhl")) // only .hhl files
    .foreach { file =>
      val lines = Files.readAllLines(file).asScala
      val expected = lines.headOption.flatMap {
        case ValidTag(flag) => Some(flag.toBoolean)
        case _ => None
      }.getOrElse(
        throw new IllegalArgumentException(s"$file is missing the // VALID: <bool> header")
      )

      test(file.getFileName.toString) {
        cancelAfter(15.seconds) {
          SymbolChecker.reset()
          TypeChecker.reset()
          Generator.reset()
          SyntacticEngine.reset()
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
