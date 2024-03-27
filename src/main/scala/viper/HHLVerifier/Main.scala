package viper.HHLVerifier

import fastparse.Parsed
import viper.silicon.Silicon
import viper.silver.reporter.NoopReporter
import viper.silver.verifier.{Failure, Success}

import java.io.FileWriter

object Main {

  var verified = 0  // 0: unknown, 1: failure, 2: success
  var runtime = 0.0
  var test = false

  def main(args: Array[String]): Unit = {

    verified = 0
    if (args.length == 0) {
      println("Please provide the program to verify. ")
      sys.exit(1)
    }

    val programAbsPath = args(0)
    val programSource = scala.io.Source.fromFile(programAbsPath)
    val program = programSource.mkString
    programSource.close()

    val outputPath = if (args.contains("--output")) args(args.indexOf("--output") + 1) else "unspecified"
    if (args.contains("--noframe")) Generator.forAllFrame = false
    if (args.contains("--existsframe")) {
      Generator.existsFrame = true
      println("Warning: turning on existential framing might cause non-termination.")
    }
    if (args.contains("--iterframe")) Generator.iterFrame = true
    if (args.contains("--inline")) Generator.inline = true
    if (args.contains("--auto")) Generator.autoSelectRules = true
    if (args.contains("--forall") && !args.contains("--exists")) Generator.verifierOption = 0
    else if (args.contains("--exists") && !args.contains("--forall")) Generator.verifierOption = 1
    else Generator.verifierOption = 2 // Both forall & exists encodings will be emitted

    printMsg("The input program is read from " + programAbsPath)

    try {
      val t0 = System.nanoTime()
      val res = fastparse.parse(program, Parser.program(_))
      if (res.isSuccess) {
        printMsg("Parsing successful. ")
        val parsedProgram: HHLProgram = res.get.value

        // Symbol table
        SymbolChecker.checkSymbolsProg(parsedProgram)

        // Type checking
        TypeChecker.typeCheckProg(parsedProgram)
        printMsg("Type checking successful. ")
        
        // Generate the Viper program
        val viperProgram = Generator.generate(parsedProgram)
        SymbolChecker.reset()
        TypeChecker.reset()
        Generator.reset()
        // Optionally save the Viper program to some provided file
        if (outputPath != "unspecified") {
          val fw = new FileWriter(outputPath, false)
          printMsg("The translated program is written to " + outputPath)
          try fw.write(viperProgram.toString())
          finally fw.close()
        }

        val consistencyErrors = viperProgram.checkTransitively
        //We check whether the program is well-defined (i.e., has no consistency errors such as ill-typed expressions)
        if (consistencyErrors.nonEmpty) {
          verified = 1
          consistencyErrors.foreach(err => printMsg(err.readableMessage))
        } else {
          printMsg("Translated program is being verified by Viper. ")
          val silicon = Silicon.fromPartialCommandLineArguments(Seq.empty, NoopReporter)
          silicon.start()
          val verifyRes = silicon.verify(viperProgram)
          silicon.stop()
          val t1 = System.nanoTime()
          runtime = (t1 - t0) / 1E9

          verifyRes match {
            case Success =>
              verified = 2
              printMsg("Verification succeeded")
            case Failure(err) =>
              verified = 1
              printMsg("Verification failed")
              err.foreach(e => printMsg(e.readableMessage))

          }
          printMsg("Runtime: " + runtime)
        }
      } else {
        val Parsed.Failure(_, _, extra) = res
        printMsg(extra.trace().longAggregateMsg)
      }
    } catch {
      case e: VerifierException =>
        verified = 1
        printMsg(e.errMsg)
    }
  }

  def printMsg(msg: String): Unit = {
    if (!test) println(msg)
  }

}
