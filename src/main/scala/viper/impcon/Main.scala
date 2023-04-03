package viper.impcon

import viper.silicon.Silicon //this is the Silicon verifier
import viper.silver.{ast => vpr} //this creates an alias to the Viper AST package
import viper.silver.reporter.NoopReporter
import viper.silver.verifier.{Failure, Success}


object Main {

  def main(args: Array[String]): Unit = {
    val b = vpr.LocalVarDecl("x", vpr.Bool)()

    //a trivial Viper program
    val p = vpr.Program(
      Seq.empty,
      Seq.empty,
      Seq.empty,
      Seq.empty,
      Seq(vpr.Method( //list methods here
        "foo", //method name
        Seq(b), //method args
        Seq.empty, //method returns
        Seq.empty, //precondition
        Seq.empty, //postcondition
        //method body
        /* Note that there are many empty parentheses, this is because we are not giving any positional information here (i.e., line numbers.
           Moreover, we would provide special information into the Assert nodes so that we could map errors back from Viper to the front-end.
         */
        Some(vpr.Seqn(Seq(vpr.If(b.localVar, vpr.Seqn(Seq(vpr.Assert(b.localVar)()), Seq.empty)(), vpr.Seqn(Seq.empty, Seq.empty)())()), Seq.empty)())
      )()),
      Seq.empty,
    )()

    //we know invoke Silicon in order to verify the program
    val silicon = Silicon.fromPartialCommandLineArguments(Seq.empty, NoopReporter)
    silicon.start()
    val res = silicon.verify(p)
    silicon.stop()

    print(res)

    res match {
      case Success =>
        println("Verification succeeded")
      case Failure(err) =>
        println("Verification failed")
        err.foreach(e => e.readableMessage)
    }
  }

}
