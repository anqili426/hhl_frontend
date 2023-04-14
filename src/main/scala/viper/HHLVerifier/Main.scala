package viper.HHLVerifier

import viper.silicon.Silicon //this is the Silicon verifier
import viper.silver.{ast => vpr} //this creates an alias to the Viper AST package
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
        println(res)
      }
    } catch {
      case e: DuplicateIdentifierException => println(e.msg)
      case e: IdentifierNotFoundException => println(e.msg)
    }
  }

}
