package viper.HHLVerifier

import fastparse.Parsed
import viper.silicon.Silicon
import viper.silver.reporter.NoopReporter
import viper.silver.verifier.{Failure, Success}

object Main {

  def main(args: Array[String]): Unit = {

    if (args.length == 0) {
      println("Please provide the program to verify. ")
      sys.exit(1)
    }
    val programAbsPath = args(0)
    val program = scala.io.Source.fromFile(programAbsPath).mkString
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
        sys.exit(0)

        // Generate the Viper program
        val viperProgram = Generator.generate(parsedProgram)
        println(viperProgram)

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
            // TODO: fix later
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
