lazy val renaissanceCore = RootProject(uri("../../renaissance-core"))

lazy val scalaStmLibrary = RootProject(uri("scala-stm-library"))

lazy val scalaStm = (project in file("."))
  .settings(
    name := "scala-stm",
    version := (version in renaissanceCore).value,
    organization := (organization in renaissanceCore).value,
    scalaVersion := "2.12.13"
  )
  .dependsOn(
    renaissanceCore,
    scalaStmLibrary % "compile->compile;compile->test"
  )
  .aggregate(
    scalaStmLibrary
  )
