package viper.HHLVerifier

import fastparse.Parsed

import java.io.FileWriter
import viper.silicon.Silicon
import viper.silver.reporter.NoopReporter
import viper.silver.verifier.VerificationResult
import viper.silver.verifier.{Failure => ResFailure, Success => ResSuccess}
import viper.carbon.CarbonVerifier

import scala.concurrent.ExecutionContext.Implicits.global
import scala.concurrent.duration.Duration
import scala.concurrent.{Await, Future, Promise}
import scala.util.{Failure, Success}


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
          val carbon = CarbonVerifier(NoopReporter)
          val silicon = Silicon.fromPartialCommandLineArguments(Seq.empty, NoopReporter)
          carbon.start()
          silicon.start()

          val carbonRes = Future[VerificationResult]{
            println("Carbon has been started. ")
            carbon.verify(viperProgram)
          }

          val siliconRes = Future[VerificationResult] {
            println("Silicon has been started. ")
            silicon.verify(viperProgram)
          }

          val resPromise = Promise[VerificationResult]()

          var carbonVerified = 0  // 0: unknown 1: failure 2: success
          var siliconVerified = 0 // 0: unknown 1: failure 2: success

          carbonRes.onComplete {
            case Success(result) =>
              result match {
                case ResSuccess =>
                  carbonVerified = 2
                  resPromise.trySuccess(result)
                case ResFailure(err) =>
                  if (!resPromise.isCompleted) {
                    carbonVerified = 1
                    println("Carbon: ")
                    err.foreach(e => printMsg(e.readableMessage))
                    while (siliconVerified == 0) {} // Wait for silicon to terminate
                    if (siliconVerified == 1) resPromise.trySuccess(result)
                    // if siliconVerified == 2, it would have returned
                  }
              }
              resPromise.trySuccess(result)
            case Failure(_) =>
          }

          siliconRes.onComplete {
            case Success(result) =>
              result match {
                case ResSuccess =>
                  siliconVerified = 2
                  resPromise.trySuccess(result)
                case ResFailure(err) =>
                  if (!resPromise.isCompleted) {
                    siliconVerified = 1
                    println("Silicon: ")
                    err.foreach(e => printMsg(e.readableMessage))
                    while (carbonVerified == 0) {} // Wait for carbon to terminate
                    if (carbonVerified == 1) resPromise.trySuccess(result)
                    // if carbonVerified == 2, it would have returned
                  }
              }
            case Failure(_) =>
          }

          val resultFuture = resPromise.future
          val result = Await.result(resultFuture, Duration.Inf)
          val t1 = System.nanoTime()
          carbon.stop()
          silicon.stop()
          result match {
            case ResSuccess =>
              verified = 2
              printMsg("Verification succeeded")
            case ResFailure(err) =>
              verified = 1
              printMsg("Verification failed")
              err.foreach(e => printMsg(e.readableMessage))
          }
          runtime = (t1 - t0) / 1E9
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
