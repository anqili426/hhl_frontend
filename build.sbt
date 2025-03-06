import scala.sys.process.Process
import scala.util.Try

ThisBuild / version := "0.1.0-SNAPSHOT"

ThisBuild / scalaVersion := "2.13.10"

val fastParse = "com.lihaoyi" %% "fastparse" % "2.2.2"
val csvWriter = "au.com.bytecode" % "opencsv" % "2.4"
val play = "com.typesafe.play" %% "play-json" % "2.10.0"

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
