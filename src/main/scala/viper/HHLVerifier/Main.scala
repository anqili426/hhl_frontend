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
        // Get the parse tree
        val parsedProgram: HHLProgram = res.get.value

        // Generate the Viper program
        val viperProgram = Generator.generate(parsedProgram)

        val consistencyErrors = viperProgram.checkTransitively

        println(viperProgram)

        //We check whether the program is well-defined (i.e., has no consistency errors such as ill-typed expressions)
        if (consistencyErrors.nonEmpty) {
          consistencyErrors.foreach(err => println(err.readableMessage))
          sys.exit(1)
        }

        // Not working at the moment
//        val silicon = Silicon.fromPartialCommandLineArguments(Seq.empty, NoopReporter)
//        silicon.start()
//        val verifyRes = silicon.verify(viperProgram)
//        silicon.stop()
//
//        verifyRes match {
//          case Success =>
//            println("Verification succeeded")
//          case Failure(err) =>
//            println("Verification failed")
//            err.foreach(e => e.readableMessage)
//        }
      } else {
        println(res)
      }
    } catch {
      case e: DuplicateIdentifierException => println(e.msg)
      case e: IdentifierNotFoundException => println(e.msg)
    }
//    val b = vpr.LocalVarDecl("x", vpr.Bool)()
//
//    //a trivial Viper program
//    val p = vpr.Program(
//      Seq.empty,  // domains
//      Seq.empty,  // fields
//      Seq.empty,  // functions
//      Seq.empty,  // predicates
//      Seq(vpr.Method( //list methods here
//        "foo", //method name
//        Seq(b), //method args
//        Seq.empty, //method returns
//        Seq.empty, //precondition
//        Seq.empty, //postcondition
//        //method body
//        /* Note that there are many empty parentheses, this is because we are not giving any positional information here (i.e., line numbers.
//           Moreover, we would provide special information into the Assert nodes so that we could map errors back from Viper to the front-end.
//         */
//        Some(vpr.Seqn(Seq(vpr.If(b.localVar, vpr.Seqn(Seq(vpr.Assert(b.localVar)()), Seq.empty)(), vpr.Seqn(Seq.empty, Seq.empty)())()), Seq.empty)())
//      )()),
//      Seq.empty, // extensions
//    )()
  }

}
