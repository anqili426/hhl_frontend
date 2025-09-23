import scala.sys.process.Process
import scala.util.Try

ThisBuild / version := "0.1.0-SNAPSHOT"

ThisBuild / scalaVersion := "2.13.10"

val fastParse = "com.lihaoyi" %% "fastparse" % "2.2.2"
val csvWriter = "au.com.bytecode" % "opencsv" % "2.4"
val play = "com.typesafe.play" %% "play-json" % "2.10.0"
val z3 = "tools.aqua" % "z3-turnkey" % "4.14.1"
val cvc5 = "tools.aqua" % "cvc5-turnkey" % "1.2.0"
val scalatest = "org.scalatest" %% "scalatest" % "3.2.18" % Test

lazy val silicon = (project in file("silicon"))
  .settings(assembly / mainClass := None)
lazy val carbon = (project in file("carbon"))
  .settings(assembly / mainClass := None)

lazy val impcon_frontend = (project in file("."))
  .dependsOn(carbon % "compile->compile;test->test")
  .dependsOn(silicon % "compile->compile;test->test")
  .settings(
    // General settings
    name := "hhl_verifier",
    organization := "viper",
    version := "1.0-SNAPSHOT",

    libraryDependencies += fastParse,
    libraryDependencies += csvWriter,
    libraryDependencies += play,
    libraryDependencies += z3,
    libraryDependencies += cvc5,
    libraryDependencies += scalatest,

    Test / testOptions += Tests.Argument(TestFrameworks.ScalaTest, "-u", "target/test-reports", "-oD"),

    // Assembly settings
    assembly / assemblyJarName := "hhl.jar",             // JAR filename
    assembly / mainClass := Some("viper.HHLVerifier.Main"),    // Define JAR's entry point
    assembly / test := {},                                  // Prevent testing before packaging
    assembly / assemblyMergeStrategy := {
      case PathList("META-INF", _*) => MergeStrategy.discard
      case _                        => MergeStrategy.first
    },
    // Compile / resourceDirectory := baseDirectory.value / "src" / "main" / "resources",
    fork := true //if forking is not set to true, there are classloader issues in Silver
  )
  .enablePlugins(BuildInfoPlugin)
