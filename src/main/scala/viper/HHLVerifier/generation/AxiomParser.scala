package viper.HHLVerifier.generation

import viper.HHLVerifier.Logger
import viper.silver.frontend.SilFrontend
import viper.silver.frontend.ViperAstProvider
import viper.silver.reporter.NoopReporter
import viper.silver.{ast => vpr}

import java.io.FileNotFoundException
import java.nio.file.{Files, Path, StandardCopyOption}

case object AxiomParser {
  private val frontend: SilFrontend = new ViperAstProvider(NoopReporter, disablePlugins = true)

  def parseAxioms(name: String): vpr.Program = {
    val inpStream = getClass().getResourceAsStream(f"/axioms/$name.vpr")
    if (inpStream == null)
      throw new FileNotFoundException(f"Axioms $name not found.")

    val tempFile = Files.createTempFile(name, ".vpr")
    tempFile.toFile().deleteOnExit()
    Files.copy(inpStream, tempFile, StandardCopyOption.REPLACE_EXISTING)

    new Logger(f"Parsing axioms $name.").log()

    frontend.execute(Seq(tempFile.toString()))
    if (!frontend.errors.isEmpty || frontend.program.isEmpty)
      throw new UnknownError(f"Failed to parse custom axioms $name!")

    frontend.translationResult
  }
}
