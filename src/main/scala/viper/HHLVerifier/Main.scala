package viper.HHLVerifier

import fastparse.Parsed
import viper.HHLVerifier.ast.HHLProgram
import viper.HHLVerifier.generation.Generator
import viper.HHLVerifier.management._
import viper.HHLVerifier.parsing.Parser
import viper.HHLVerifier.symbols.SymbolChecker
import viper.HHLVerifier.typing.TypeChecker

import java.io.FileWriter
import viper.silver.verifier.{Failure => ResFailure, Success => ResSuccess}

/** Main Method */
object Main {

  // [DOC] Variables
  var verified = 0  // 0: unknown, 1: failure, 2: success
  var runtime = 0.0
  var test = false
  var testWithLogs = false
  var errMessages: Seq[String] = Seq("")

  def main(args: Array[String]): Unit = {
    errMessages = Seq.empty
    verified = 0

    // [DOC] Read Files
    if (args.length == 0) {
      new Logger("Please provide the program to verify.", Logger.ERR).addTitle("Invalid Arguments").log()
      sys.exit(1)
    }

    val programAbsPath = args(0)
    Logger.setFilePath(programAbsPath)
    val programSource = scala.io.Source.fromFile(programAbsPath)
    val program = programSource.mkString
    Logger.setSourceCode(program)
    programSource.close()

    // [DOC] Handle command line arguments
    val outputPath = if (args.contains("--output")) args(args.indexOf("--output") + 1) else "unspecified"
    if (args.contains("--noframe")) Generator.forAllFrame = false
    if (args.contains("--ext")) Logger.setExtensionToTrue()
    if (args.contains("--existsframe")) {
      Generator.existsFrame = true
      new Logger("Turning on existential framing might cause non-termination.", Logger.WARN).addTitle("ExistsFrame").log()
    }
    if (args.contains("--inline")) Generator.inline = true
    if (args.contains("--auto")) Generator.autoSelectRules = true
    if (args.contains("--forall") && !args.contains("--exists")) Generator.verifierOption = 0
    else if (args.contains("--exists") && !args.contains("--forall")) Generator.verifierOption = 1
    else Generator.verifierOption = 2 // Both forall & exists encodings will be emitted

    new Logger(f"The input program is read from $programAbsPath.").log()

    try {
      // [DOC] parse program
      val t0 = System.nanoTime()
      val res = fastparse.parse(program, Parser.program(_))

      if (res.isSuccess) {
        new Logger("Parsing successful.").log()

        val parsedProgram: HHLProgram = res.get.value

        // Symbol table
        SymbolChecker.checkSymbolsProg(parsedProgram)
        new Logger("Symbol checking successful.").log()

        // Type checking
        TypeChecker.typeCheckProg(parsedProgram)
        new Logger("Type checking successful.").log()

        // Generate the Viper program
        val viperProgram = Generator.generate(parsedProgram, program)
        SymbolChecker.reset()
        TypeChecker.reset()
        Generator.reset()
        // Optionally save the Viper program to some provided file
        if (outputPath != "unspecified") {
          val fw = new FileWriter(outputPath, false)
          new Logger(f"The translated program is written to $outputPath.").log()
          try {
            fw.write(viperProgram.toString())
          } catch {
            case e: Exception =>
              System.err.println(e.toString())
              new Logger("Failed to write Viper encoding file.").log()
          } finally fw.close()
        }

        val consistencyErrors = viperProgram.checkTransitively
        //We check whether the program is well-defined (i.e., has no consistency errors such as ill-typed expressions)
        if (consistencyErrors.nonEmpty) {
          verified = 1
          consistencyErrors.foreach(err => new Logger(err.readableMessage, Logger.ERR).addTitle("Consistency Error").log())
        } else {
          new Logger("Translated program is being verified by Viper.").log()
          val result = ViperRunner.runSiliconAndCarbon(viperProgram)
          val t1 = System.nanoTime()
          runtime = (t1 - t0) / 1E9
          result match {
            case ResSuccess =>
              verified = 2
              new Logger(f"Verification succeeded in ${runtime}s").log()
            case ResFailure(err) =>
              verified = 1
              new Logger(f"The provided program could not be verified. Runtime: ${runtime}s", Logger.ERR).addTitle("Verification failed").log()
              err.foreach(e => println(e)) // AnnotationInfos are already correctly formatted, they just need to be printed
          }
        }
      } else {
        val Parsed.Failure(expc, pos, extra) = res
        println(extra.trace().longMsg)
        new Logger(extra.trace().msg, Logger.ERR).addTitle("Parser Error").addOffset((pos, pos+10)).log()
      }
    } catch {
      case e: VerifierException =>
        verified = 1
        println(e.errMsg)
      case e: Logger =>
        e.log()
      case e: Exception =>
        verified = 1
        new Logger(e.getMessage, Logger.ERR).addTitle("Unkown Exception").log()
    }
  }
}