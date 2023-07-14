package viper.HHLVerifier

import fastparse.Parsed
import viper.silicon.Silicon
import viper.silver.reporter.NoopReporter
import viper.silver.verifier.{Failure, Success}

import java.io.FileWriter

object Main {

  def main(args: Array[String]): Unit = {

    if (args.length == 0) {
      println("Please provide the program to verify. ")
      sys.exit(1)
    }

    val programAbsPath = args(0)
    val programSource = scala.io.Source.fromFile(programAbsPath)
    val program = programSource.mkString
    programSource.close()

    val outputPath = if (args.length <= 1) "unspecified" else args(1)
    if (args.contains("--inline")) Generator.inline = true
    if (args.contains("--forall") && !args.contains("--exists")) Generator.verifierOption = 0
    else if (args.contains("--exists") && !args.contains("--forall")) Generator.verifierOption = 1
    // TODO: This still needs to be implemented
    else Generator.verifierOption = 2 // Both forall & exists encodings will be emitted

    println("The input program is read from " + programAbsPath)
    println("The translated program is written to " + outputPath)

    try {
      val res = fastparse.parse(program, Parser.program(_))
      if (res.isSuccess) {
        println("Parsing successful. ")
        val parsedProgram: HHLProgram = res.get.value

        // Symbol table
        SymbolChecker.checkSymbolsProg(parsedProgram)

        // Type checking
        TypeChecker.typeCheckProg(parsedProgram)
        println("Type checking successful. ")
        
        // Generate the Viper program
        val viperProgram = Generator.generate(parsedProgram)
        // Optionally save the Viper program to some provided file
        if (args.length > 1) {
          val fw = new FileWriter(outputPath, false)
          try fw.write(viperProgram.toString())
          finally fw.close()
        }

        val consistencyErrors = viperProgram.checkTransitively
        //We check whether the program is well-defined (i.e., has no consistency errors such as ill-typed expressions)
        if (consistencyErrors.nonEmpty) {
          consistencyErrors.foreach(err => println(err.readableMessage))
          sys.exit(1)
        }

        println("Translated program is being verified by Viper. ")
        val silicon = Silicon.fromPartialCommandLineArguments(Seq.empty, NoopReporter)
        silicon.start()
        val verifyRes = silicon.verify(viperProgram)
        silicon.stop()

        verifyRes match {
          case Success =>
            println("Verification succeeded")
          case Failure(err) =>
            println("Verification failed")
            err.foreach(e => println(e.readableMessage))
        }
      } else {
        val Parsed.Failure(_, _, extra) = res
        println(extra.trace().longAggregateMsg)
      }
    } catch {
      case e: VerifierException => println(e.errMsg)
    }
  }

}
