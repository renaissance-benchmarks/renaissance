lazy val renaissanceCore = RootProject(uri("../../renaissance-core"))

lazy val scalaStdlib = (project in file("."))
  .settings(
    name := "scala-stdlib",
    version := (version in renaissanceCore).value,
    organization := (organization in renaissanceCore).value,
    scalafmtConfig := Some(file(".scalafmt.conf")),
    scalaVersion := "2.12.8"
  )
  .dependsOn(
    renaissanceCore
  )
