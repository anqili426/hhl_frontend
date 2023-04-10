import scala.sys.process.Process
import scala.util.Try

ThisBuild / version := "0.1.0-SNAPSHOT"

ThisBuild / scalaVersion := "2.13.10"

val fastParse = "com.lihaoyi" %% "fastparse" % "3.0.1"
lazy val silicon = project in file("silicon")
//lazy val carbon = project in file("carbon")

lazy val impcon_frontend = (project in file("."))
  //.dependsOn(carbon % "compile->compile;test->test")
  .dependsOn(silicon % "compile->compile;test->test")
    .settings(
        // General settings
        name := "hhl_verifier",
        organization := "viper",
        version := "1.0-SNAPSHOT",

        libraryDependencies += fastParse,

        Test / testOptions += Tests.Argument(TestFrameworks.ScalaTest, "-u", "target/test-reports", "-oD"),

        // Assembly settings
        assembly / assemblyJarName := "hhl.jar",             // JAR filename
        assembly / mainClass := Some("hhl.Main"),    // Define JAR's entry point
        assembly / test := {},                                  // Prevent testing before packaging
        fork := true //if forking is not set to true, there are classloader issues in Silver
    )
  .enablePlugins(BuildInfoPlugin)