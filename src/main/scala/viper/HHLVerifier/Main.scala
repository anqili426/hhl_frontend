package viper.HHLVerifier

import fastparse.Parsed
import viper.silicon.Silicon
import viper.silver.reporter.NoopReporter
import viper.silver.verifier.{Failure, Success}

object Main {

  def main(args: Array[String]): Unit = {

    val programAbsPath = "/Users/anqili/Desktop/thesis/hhl_frontend/src/main/scala/viper/HHLVerifier/program.txt"
    val program = scala.io.Source.fromFile(programAbsPath).mkString
    try {
      val res = fastparse.parse(program, Parser.program(_))
      if (res.isSuccess) {
        println("Parsing successful. ")
        val parsedProgram: HHLProgram = res.get.value
        println(parsedProgram)

        // Symbol table
        SymbolChecker.checkSymbolsProg(parsedProgram)

        // TODO: Type checking

        // Generate the Viper program
        val viperProgram = Generator.generate(parsedProgram)
        println(viperProgram)

        val consistencyErrors = viperProgram.checkTransitively
        //We check whether the program is well-defined (i.e., has no consistency errors such as ill-typed expressions)
        if (consistencyErrors.nonEmpty) {
          consistencyErrors.foreach(err => println(err.readableMessage))
          sys.exit(1)
        }

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
