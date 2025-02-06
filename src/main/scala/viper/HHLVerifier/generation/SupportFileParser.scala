package viper.HHLVerifier.generation

import viper.silver.frontend.{SilFrontend, ViperAstProvider}
import viper.silver.reporter.NoopReporter
import viper.silver.{ast => vpr}

import java.nio.file.{Files, NoSuchFileException, Paths}

case object SupportFileParser {
  private val frontend: SilFrontend = new ViperAstProvider(NoopReporter, disablePlugins = true)

  def parseFile(vpr_file_path: String): vpr.Program = {
    val path = Paths.get(vpr_file_path)
    if (!Files.exists(path)) {
      throw new NoSuchFileException(vpr_file_path)
    }

    frontend.execute(Seq(vpr_file_path))
    println(frontend.appExitCode)
    if (!frontend.errors.isEmpty || frontend.program.isEmpty) {
      throw new UnknownError(f"Failed to parse Viper's support file with path $vpr_file_path!")
    }


    frontend.translationResult
  }
}
