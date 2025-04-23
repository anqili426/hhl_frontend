package viper.HHLVerifier.management

import viper.HHLVerifier.Main.logsActive
import viper.carbon.CarbonVerifier
import viper.silicon.Silicon
import viper.silver.ast.Program
import viper.silver.reporter.NoopReporter
import viper.silver.verifier.{TimeoutOccurred, VerificationResult, Failure => ResFailure, Success => ResSuccess}

import scala.concurrent.ExecutionContext.Implicits.global
import scala.concurrent.duration.DurationInt
import scala.concurrent.{Await, Future, Promise}
import scala.util.{Failure, Success}

object ViperRunner {
  def runSilicon(program: Program): VerificationResult = {
    val consistencyErrors = program.checkTransitively
    if (consistencyErrors.nonEmpty) {
      consistencyErrors.foreach(err => new Logger(err.readableMessage, Logger.ERR).addTitle("Consistency Error").log())
      sys.exit(1)
    } else {
      val silicon = Silicon.fromPartialCommandLineArguments(Seq.empty, NoopReporter)
      silicon.start()
      val res = silicon.verify(program)
      silicon.stop()
      res
    }
  }

  def runCarbon(program: Program): VerificationResult = {
    val consistencyErrors = program.checkTransitively
    if (consistencyErrors.nonEmpty) {
      consistencyErrors.foreach(err => new Logger(err.readableMessage, Logger.ERR).addTitle("Consistency Error").log())
      sys.exit(1)
    } else {
      val carbon = CarbonVerifier(NoopReporter)
      carbon.start()
      val res = carbon.verify(program)
      carbon.stop()
      res
    }
  }

  def runSiliconAndCarbon(program: Program, singleTimeout: Int = 500, overallTimeout: Int = 800, checkSideCondition: Boolean = false) = {
    // println(program)

    val consistencyErrors = program.checkTransitively
    if (consistencyErrors.nonEmpty) {
      consistencyErrors.foreach(err => new Logger(err.readableMessage, Logger.ERR).addTitle("Consistency Error").log())
      sys.exit(1)
    } else{
      val carbon = CarbonVerifier(NoopReporter)
      val silicon = Silicon.fromPartialCommandLineArguments(Seq.empty, NoopReporter)

      try {
        val carbonRes = Future[VerificationResult] {
          if (checkSideCondition) new Logger("Carbon has been started to check a side condition.").log()
          else new Logger("Carbon has been started to verify the program.").log()
          carbon.start()
          val res = carbon.verify(program)
          carbon.stop()
          res
        }

        val siliconRes = Future[VerificationResult] {
          if (checkSideCondition) new Logger("Silicon has been started to check a side condition.").log()
          else new Logger("Silicon has been started to verify the program.").log()
          silicon.start()
          val res = silicon.verify(program)
          silicon.stop()
          res
        }

        val resPromise = Promise[VerificationResult]()

        carbonRes.onComplete {
          case Success(result) =>
            result match {
              case ResSuccess =>
                // If carbon verifies successfully, can terminate with success
                if (!resPromise.isCompleted) {
                  if (checkSideCondition) new Logger("Carbon succeeded in verifying the side condition.").log()
                  else new Logger("Carbon succeeded in verifying the program.").log()
                  resPromise.trySuccess(result)
                }
              case ResFailure(err) =>
                // If carbon fails to verify, then
                //   1. If silicon verifies successfully (i.e. resPromise.isCompleted), then do nothing
                //   2. If silicon's result is not available yet, wait for at most 180 seconds
                //   2.1  If silicon verifies successfully eventually, then silicon would have completed resPromise, so we do nothing
                //   2.2  If silicon fails to verify eventually, or if silicon still has no result after timeout,
                //        then we complete resPromise with a verification failure
                if (!resPromise.isCompleted) {
                  if (!checkSideCondition) {
                    new Logger("Carbon failed to verify the program.").log()
//                    if (logsActive) err.foreach(e => println(e.readableMessage))
                  }
                  if (!siliconRes.isCompleted) {
                    try {
                      Await.result(siliconRes, singleTimeout.seconds)
                    } catch {
                      case _: java.util.concurrent.TimeoutException => resPromise.trySuccess(result)
                    }
                  } // Wait for silicon to terminate
                  siliconRes.onComplete {
                    case Success(siliconResult) =>
                      val siliconVerified = interpretResult(siliconResult)
                      if (!siliconVerified) resPromise.trySuccess(result)
                    case Failure(_) => resPromise.trySuccess(result)
                  }
                }
            }
          case Failure(_) =>
        }

        siliconRes.onComplete {
          case Success(result) =>
            result match {
              case ResSuccess =>
                if (!resPromise.isCompleted) {
                  if (checkSideCondition) new Logger("Silicon succeeded in verifying the side condition.").log()
                  else new Logger("Silicon succeeded in verifying the program").log()
                  resPromise.trySuccess(result)
                }
              case ResFailure(err) =>
                if (!resPromise.isCompleted) {
                  if (!checkSideCondition) {
                    new Logger("Silicon failed to verify the program.").log()
//                    if (logsActive) err.foreach(e => println(e.readableMessage))
                  }
                  if (!carbonRes.isCompleted) {
                    try {
                      Await.result(carbonRes, singleTimeout.seconds)
                    } catch {
                      case _: java.util.concurrent.TimeoutException => resPromise.trySuccess(result)
                    }
                  } // Wait for carbon to terminate
                  carbonRes.onComplete {
                    case Success(carbonResult) =>
                      val carbonVerified = interpretResult(carbonResult)
                      if (!carbonVerified) resPromise.trySuccess(result)
                    case Failure(_) => resPromise.trySuccess(result)
                  }
                }
            }
          case Failure(_) =>
        }
        val resultFuture = resPromise.future
        val result = Await.result(resultFuture, overallTimeout.seconds)
        result
      } catch {
          case _: java.util.concurrent.TimeoutException => ResFailure(Seq(TimeoutOccurred(overallTimeout, "seconds")))
      }
    }
  }

  def interpretResult(res: VerificationResult): Boolean = {
    res match {
      case ResSuccess => true
      case ResFailure(_) => false
      case _ => false
    }
  }
}
