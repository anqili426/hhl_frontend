package viper.HHLVerifier.comm

import play.api.libs.json.{JsValue, Json}
import viper.HHLVerifier.Logger
import viper.silver.ast.AnnotationInfo

trait CommElement extends Throwable {
  def toJson: JsValue
  def lvl:    String

  def send(): Unit = {
    val parsedPkt = Json.stringify(toJson)
    if (lvl == CommLevel.info) println(f"JSON-$lvl-$parsedPkt")
    else System.err.println(f"JSON-$lvl-$parsedPkt")
  }

  def annotationInfo(): AnnotationInfo = {
    if (Logger.inExtension) {
      val parsedPkt = Json.stringify(toJson)
      AnnotationInfo(Map("msg" -> Seq(f"JSON-$lvl-$parsedPkt")))
    } else AnnotationInfo(Map("msg" -> Seq("UNIMPLEMENTED")))
  }
}

object CommLevel {
  val setupErr  = "ERS"
  val codeErr   = "ERC"
  val warn      = "WRN"
  val info      = "IFN"
}

case class Info(descr: String) extends CommElement {
  override def toJson: JsValue = Json.obj(
    "descr" -> descr,
  )
  override def lvl: String = CommLevel.info
}

case class Warning(name: String, descr: String) extends CommElement {
  override def toJson: JsValue = Json.obj(
    "name"  -> name,
    "descr" -> descr,
  )
  override def lvl: String = CommLevel.warn
}

// Setup errors result in a exit code != 0
case class SetupError(name: String, descr: String) extends CommElement {
  override def toJson: JsValue = Json.obj(
    "name"  -> name,
    "descr" -> descr,
  )
  override def lvl: String = CommLevel.setupErr
}

// Code errors result in exit code == 0
trait CodeError extends CommElement {
  def code: Int
  def name: String
  def descr: String
  def offsetLeft: Int
  def offsetRight: Int

  def toJson: JsValue = Json.obj(
    "code" -> code,
    "name" -> name,
    "descr" -> descr,
    "offsetLeft" -> offsetLeft,
    "offsetRight" -> offsetRight
  )
  def lvl: String = CommLevel.codeErr
}