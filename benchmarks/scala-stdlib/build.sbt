lazy val renaissanceCore = RootProject(uri("../../renaissance-core"))

lazy val scalaStdlib = (project in file("."))
  .settings(
    name := "scala-stdlib",
    version := (version in renaissanceCore).value,
    organization := (organization in renaissanceCore).value,
    scalaVersion := "2.13.5"
  )
  .dependsOn(
    renaissanceCore
  )
