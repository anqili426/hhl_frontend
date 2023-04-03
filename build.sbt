import scala.sys.process.Process
import scala.util.Try

ThisBuild / version := "0.1.0-SNAPSHOT"

ThisBuild / scalaVersion := "2.13.10"

lazy val silicon = project in file("silicon")
//lazy val carbon = project in file("carbon")

lazy val impcon_frontend = (project in file("."))
  //.dependsOn(carbon % "compile->compile;test->test")
  .dependsOn(silicon % "compile->compile;test->test")
    .settings(
        // General settings
        name := "frontend_demo",
        organization := "viper",
        version := "1.0-SNAPSHOT",

        Test / testOptions += Tests.Argument(TestFrameworks.ScalaTest, "-u", "target/test-reports", "-oD"),

        // Assembly settings
        assembly / assemblyJarName := "impcon.jar",             // JAR filename
        assembly / mainClass := Some("impcon.Main"),    // Define JAR's entry point
        assembly / test := {},                                  // Prevent testing before packaging
    )
  .enablePlugins(BuildInfoPlugin)