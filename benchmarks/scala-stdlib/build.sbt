lazy val renaissanceCore = RootProject(uri("../../renaissance-core"))

lazy val scalaStdlib = (project in file("."))
  .settings(
    name := "scala-stdlib",
    organization := "org.renaissance",
    version := "0.1.0",
    scalafmtConfig := Some(file(".scalafmt.conf")),
    scalaVersion := "2.12.8"
  )
  .dependsOn(
    renaissanceCore
  )
