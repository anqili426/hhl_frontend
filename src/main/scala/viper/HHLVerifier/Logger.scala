package viper.HHLVerifier

import viper.HHLVerifier.comm.{CodeError, Info, SetupError, Warning}

object Logger {
  var inExtension = false

  def info(descr: String): Unit = {
    if (inExtension) Info(descr).send()
    else println(f"[INFO] $descr")
  }

  def warn(name: String, descr: String): Unit = {
    if (inExtension) Warning(name, descr).send()
    else println(f"[WARN] $name: $descr")
  }

  def error(name: String, descr: String): Unit = {
    if (inExtension) SetupError(name, descr).send()
    else println(f"[ERROR] $name: $descr")
  }

  def error(err: CodeError): Unit = {
    if (inExtension) err.send()
    else println(f"[ERROR] ${err.name} (CODE: ${err.code}) at pos ${err.offsetLeft}: ${err.descr}")
  }
}
