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
  val carbon = CarbonVerifier(NoopReporter)
  val silicon = Silicon.fromPartialCommandLineArguments(Seq.empty, NoopReporter)

  def start(): Unit = {
    carbon.start()
    silicon.start()
  }

  def stop(): Unit = {
    carbon.stop()
    silicon.stop()
  }

  def runSilicon(program: Program) = {
    val consistencyErrors = program.checkTransitively
    if (consistencyErrors.nonEmpty) {
      consistencyErrors.foreach(err => printMsg(err.readableMessage))
      sys.exit(1)
    } else {
      val res = silicon.verify(program)
      res
    }
  }

  def runCarbon(program: Program) = {
    val consistencyErrors = program.checkTransitively
    if (consistencyErrors.nonEmpty) {
      consistencyErrors.foreach(err => printMsg(err.readableMessage))
      sys.exit(1)
    } else {
      val res = carbon.verify(program)
      res
    }
  }

  def runSiliconAndCarbon(program: Program, singleTimeout: Int = 180, overallTimeout: Int = 200, checkSideCondition: Boolean = false) = {
    val consistencyErrors = program.checkTransitively
    if (consistencyErrors.nonEmpty) {
      consistencyErrors.foreach(err => printMsg(err.readableMessage))
      sys.exit(1)
    } else{
      try {
        val carbonRes = Future[VerificationResult] {
          if (checkSideCondition) printMsg("Carbon has been started to check a side condition. ")
          else printMsg("Carbon has been started to verify the program. ")
          carbon.verify(program)
        }

        val siliconRes = Future[VerificationResult] {
          if (checkSideCondition) printMsg("Silicon has been started to check a side condition. ")
          else printMsg("Silicon has been started to verify the program. ")
          silicon.verify(program)
        }

        val resPromise = Promise[VerificationResult]()

        var carbonVerified = 0 // 0: unknown 1: failure 2: success
        var siliconVerified = 0 // 0: unknown 1: failure 2: success

        carbonRes.onComplete {
          case Success(result) =>
            result match {
              case ResSuccess =>
                // If carbon verifies successfully, can terminate with success
                carbonVerified = 2
                resPromise.trySuccess(result)
              case ResFailure(err) =>
                // If carbon fails to verify, then
                //   1. If silicon verifies successfully (i.e. resPromise.isCompleted), then do nothing
                //   2. If silicon's result is not available yet, wait for at most 180 seconds
                //   2.1  If silicon verifies successfully eventually, then silicon would have completed resPromise, so we do nothing
                //   2.2  If silicon fails to verify eventually, or if silicon still has no result after timeout,
                //        then we complete resPromise with a verification failure
                if (!resPromise.isCompleted) {
                  carbonVerified = 1
                  if (!checkSideCondition) {
                    printMsg("Carbon: ")
                    err.foreach(e => printMsg(e.readableMessage))
                  }
                  if (!siliconRes.isCompleted) Await.result(siliconRes, singleTimeout.seconds) // Wait for silicon to terminate
                  if (siliconVerified != 2) resPromise.trySuccess(result)
                }
            }
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
                  if (!checkSideCondition) {
                    printMsg("Silicon: ")
                    err.foreach(e => printMsg(e.readableMessage))
                  }
                  if (!carbonRes.isCompleted) Await.result(carbonRes, singleTimeout.seconds) // Wait for carbon to terminate
                  if (carbonVerified != 2) resPromise.trySuccess(result)
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
