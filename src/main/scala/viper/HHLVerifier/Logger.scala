package viper.HHLVerifier

import play.api.libs.json._
import viper.silver.ast.AnnotationInfo

import java.time.LocalDateTime
import java.time.format.DateTimeFormatter

class Logger(val message: String, val level: String = Logger.INFO) extends Throwable {
  var timestamp: LocalDateTime = LocalDateTime.now()
  var extra: Map[String, Any] = Map.empty

  if (Logger.filePath != "") {
    extra += ("filePath" -> Logger.filePath)
  }

  def addOffset(offsets: (Int, Int)): Logger = {
    extra += ("offsetLeft" -> offsets._1, "offsetRight" -> offsets._2)
    this
  }

  def addTitle(title: String): Logger = {
    extra += ("title" -> title)
    this
  }

  def log(): Unit = { println(Logger.format(this)) }
  def toAnnotationInfo(): AnnotationInfo = AnnotationInfo(Map("msg" -> Seq(Logger.format(this))))

  def toJson: JsValue = {
    Json.obj(
      "message" -> message,
      "level" -> level,
      "timestamp" -> timestamp.format(DateTimeFormatter.ISO_LOCAL_DATE_TIME),
      "extra" -> extra.mapValues {
        case v: String => JsString(v)
        case v: Int => JsNumber(v)
        case v: Double => JsNumber(v)
        case v: Boolean => JsBoolean(v)
        case v =>
          new Logger("Extra contains information which cannot be serialized: " + v.toString()).addTitle("Logger error").log()
          JsNull
      }
    )
  }
}

object Logger {
  private var isVSCodeExtension = false
  private var filePath = ""
  private var sourceCode = ""
  def setExtensionToTrue(): Unit = { isVSCodeExtension = true }
  def setFilePath(path: String): Unit = { filePath = path }
  def setSourceCode(source: String): Unit = { sourceCode = source }

  val INFO = "INF"
  val WARN = "WRN"
  val ERR = "ERR"

  // convert logger entry to string
  def format(entry: Logger): String = if (isVSCodeExtension) {
    entry.toJson.toString()
  } else {
    val time = DateTimeFormatter.ofPattern("yyyy-MM-dd_HH:mm").format(entry.timestamp)
    val level = Logger.translateLevel(entry.level)

    var out = f"[$time] [$level]"
    if (entry.extra.contains("offsetLeft")) {
      val (line, offset) = getLineAndOffset(entry.extra.get("offsetLeft").get.toString().toInt)
      out += f" in $filePath:$line:$offset"
    }
    if (entry.extra.contains("title")) out += " " + entry.extra.get("title").get + ":"
    out += " " + entry.message
    out
  }

  def getLineAndOffset(offset: Int): (Int, Int) = {
    val lines = sourceCode.split("\n", -1) // Keep empty lines
    var currentOffset = 0

    for ((line, index) <- lines.zipWithIndex) {
      val lineLength = line.length + 1 // +1 for the newline character
      if (offset < currentOffset + lineLength) {
        return (index + 1, offset - currentOffset) // Line numbers start from 1
      }
      currentOffset += lineLength
    }

    (lines.length, 0)
  }

  def translateLevel(level: String): String = level match {
    case Logger.INFO => "INFO"
    case Logger.WARN => "WARN"
    case Logger.ERR => "ERROR"
  }
}

// Typical Verification Errors
object VerificationErrors {
  def Postcondition(expr: Expr) = f"The post condition ${expr.toString()} might not hold"
  def HyperAssertion(expr: Expr) = f"The hyper assertion ${expr.toString()} might not hold"
  // def Deprecated(expr: Expr) = f"The expression ${expr.toString()} caused an error, but this should be deprecated"
  def MethodCall(expr: Expr) = f"The precondtion ${expr.toString()} might not hold"
  def LoopEntryPoint(expr: Expr) = f"The loop invariant ${expr.toString()} might not hold at entry point"
  def LoopSyncGuard(expr: Expr) = f"The loop guard ${expr.toString()} might not be identical for all states"
  def LoopVariant(expr: Expr) = f"The variant ${expr.toString()} might not strictly decrease"
  def LoopInvariant(expr: Expr, quantifiers: Int) = f"${ if (quantifiers > 0) f"($quantifiers stripped)" else "" }The invariant ${expr.toString()} might not hold"
}