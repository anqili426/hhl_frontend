package viper.HHLVerifier

import fastparse.Parsed
import viper.HHLVerifier.ast.{BinaryExpr, Expr, HHLProgram}
import viper.HHLVerifier.generation.Generator
import viper.HHLVerifier.management._
import viper.HHLVerifier.parsing.Parser
import viper.HHLVerifier.symbols.SymbolChecker
import viper.HHLVerifier.typing.TypeChecker
import viper.HHLVerifier.syntactic.SyntacticEngine
import viper.HHLVerifier.syntactic.smt.BackendMode

import java.io.FileWriter
import viper.silver.verifier.{Failure => ResFailure, Success => ResSuccess}

/** Main Method */
object Main {

  // [DOC] Variables
  var verified = 0  // 0: unknown, 1: failure, 2: success
  var runtime = 0.0
  var timeStamps: Array[List[Long]] = Array.fill(5)(List.empty[Long]) // timestamps to compute the duration of each syntactic step in evaluation
  var test = false
  var testWithLogs = false
  var errMessages: Seq[String] = Seq("")
  var logsActive = true
  var debugLogsActive = false // extensive logs for debugging in syntactic mode
  var syntactic = false
  var outputPath = "unspecified"
  var smtBackendMode: BackendMode = BackendMode.Both // standard SMT solver mode that is used in syntactic mode (if the argument "--smtmode" is set, this will be overridden)
  val smtRaceModes: (BackendMode, BackendMode) = (BackendMode.Z3, BackendMode.CVC5Proc) // SMT modes that are being run in parallel, if smt mode "Both" is set
  val smtSolverTimeLimitMs = 20000
  val cvc5Path: String = "cvc5" // executable path of local cvc5 installation (usually just "cvc5") ==> needed for smt mode "CVC5Proc"
  val keepSmtFiles: Boolean = false // only relevant for CVC5Proc smt mode, where temp files are created

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
    outputPath = if (args.contains("--output")) args(args.indexOf("--output") + 1) else "unspecified"
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
    if (args.contains("--syntactic")) syntactic = true
    if (args.contains("--debug")) debugLogsActive = true
    if (args.contains("--smtmode")) {
      args(args.indexOf("--smtmode") + 1) match {
        case "z3" | "Z3" => smtBackendMode = BackendMode.Z3
        case "cvc5" | "CVC5" => smtBackendMode = BackendMode.CVC5
        case "both" => smtBackendMode = BackendMode.Both
        case "cvc5-proc" | "CVC5-proc" => smtBackendMode = BackendMode.CVC5Proc
        case _ => throw new Logger("Unknown SMT backend mode, choose either \"z3\", \"cvc5\", \"cvc5-proc\" or \"both\" (default).", Logger.ERR)
      }
    }

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

        // Syntactic evaluation mode
        if (syntactic) {
          if (logsActive) println("Verifying file: " + programAbsPath.split("/").last)
          verified = SyntacticEngine.verify(parsedProgram)
          val t1 = System.nanoTime()
          runtime = (t1 - t0) / 1E9

          if (logsActive) println("----------")

          if (logsActive && verified == 2) println(f"SUCCESS: Verification succeeded in ${runtime}s")
          if (logsActive && verified == 1) println(f"ERROR: The provided program could not be verified. Runtime: ${runtime}s")

          SymbolChecker.reset()
          TypeChecker.reset()
          return
        }

        // Generate the Viper program
        val viperProgram = Generator.generate(parsedProgram)
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
              if (logsActive) err.foreach(e => println(e)) // AnnotationInfos are already correctly formatted, they just need to be printed
          }
        }
      } else {
        val Parsed.Failure(expc, pos, extra) = res
        System.err.println("Error Trace: " + extra.trace().longMsg)
        new Logger(extra.trace().msg, Logger.ERR).addTitle("Parser Error").addOffset((pos, pos+10)).log()
      }
    } catch {
      case e: VerifierException =>
        verified = 1
        new Logger(e.getMessage, Logger.ERR).addTitle("Verifier Exception").log()
        e.printStackTrace(System.err)
      case e: Logger =>
        e.log()
      case e: Exception =>
        verified = 1
        new Logger(e.getMessage, Logger.ERR).addTitle("Unkown Exception").log()
        e.printStackTrace(System.err)
    }
  }
}