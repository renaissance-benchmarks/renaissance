lazy val renaissanceCore = RootProject(uri("../renaissance-core"))

val renaissanceScalaVersion = "2.12.8"

lazy val renaissanceHarness = (project in file("."))
  .settings(
    name := "renaissance-harness",
    version := "0.1",
    organization := "org.renaissance",
    scalaVersion := renaissanceScalaVersion,
    libraryDependencies ++= Seq(
      "commons-io" % "commons-io" % "2.6",
      "com.github.scopt" %% "scopt" % "4.0.0-RC2"
    ),
    scalafmtConfig := Some(file(".scalafmt.conf"))
  )
  .dependsOn(
    renaissanceCore
  )
