package viper.HHLVerifier

import requests.TimeoutException
import viper.carbon.CarbonVerifier
import viper.silicon.Silicon
import viper.silver.ast.Program
import viper.silver.reporter.NoopReporter
import viper.silver.verifier.{TimeoutOccurred, VerificationResult, Failure => ResFailure, Success => ResSuccess}

import scala.concurrent.ExecutionContext.Implicits.global
import scala.concurrent.duration.{Duration, DurationInt}
import scala.concurrent.{Await, Future, Promise}
import scala.util.{Failure, Success}

object ViperRunner {


  def runSilicon(program: Program) = {
    val consistencyErrors = program.checkTransitively
    if (consistencyErrors.nonEmpty) {
      consistencyErrors.foreach(err => printMsg(err.readableMessage))
      sys.exit(1)
    } else {
      val silicon = Silicon.fromPartialCommandLineArguments(Seq.empty, NoopReporter)
      silicon.start()
      val res = silicon.verify(program)
      silicon.stop()
      res
    }
  }

  def runCarbon(program: Program) = {
    val consistencyErrors = program.checkTransitively
    if (consistencyErrors.nonEmpty) {
      consistencyErrors.foreach(err => printMsg(err.readableMessage))
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
    val consistencyErrors = program.checkTransitively
    if (consistencyErrors.nonEmpty) {
      consistencyErrors.foreach(err => printMsg(err.readableMessage))
      sys.exit(1)
    } else{
      val carbon = CarbonVerifier(NoopReporter)
      val silicon = Silicon.fromPartialCommandLineArguments(Seq.empty, NoopReporter)

      try {
        val carbonRes = Future[VerificationResult] {
          if (checkSideCondition) printMsg("Carbon has been started to check a side condition. ")
          else printMsg("Carbon has been started to verify the program. ")
          carbon.start()
          val res = carbon.verify(program)
          carbon.stop()
          res
        }

        val siliconRes = Future[VerificationResult] {
          if (checkSideCondition) printMsg("Silicon has been started to check a side condition. ")
          else printMsg("Silicon has been started to verify the program. ")
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
                  if (checkSideCondition) printMsg("Carbon succeeded in verifying the side condition")
                  else printMsg("Carbon succeeded in verifying the program")
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
                    printMsg("Carbon failed to verify the program: ")
                    err.foreach(e => printMsg(e.readableMessage))
                  }
                  if (!siliconRes.isCompleted) Await.result(siliconRes, singleTimeout.seconds) // Wait for silicon to terminate
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
                  if (checkSideCondition) printMsg("Silicon succeeded in verifying the side condition")
                  else printMsg("Silicon succeeded in verifying the program")
                  resPromise.trySuccess(result)
                }
              case ResFailure(err) =>
                if (!resPromise.isCompleted) {
                  if (!checkSideCondition) {
                    printMsg("Silicon failed to verify the program: ")
                    err.foreach(e => printMsg(e.readableMessage))
                  }
                  if (!carbonRes.isCompleted) Await.result(carbonRes, singleTimeout.seconds) // Wait for carbon to terminate
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
          case e: TimeoutException => ResFailure(Seq(TimeoutOccurred(overallTimeout, "seconds")))
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

  private def printMsg(msg: String): Unit = {
    Main.printMsg(msg)
  }

}
