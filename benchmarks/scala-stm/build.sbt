lazy val renaissanceCore = RootProject(uri("../../renaissance-core"))

lazy val scalaStmLibrary = RootProject(uri("scala-stm-library"))

lazy val scalaStm = (project in file("."))
  .settings(
    name := "scala-stm",
    version := (renaissanceCore / version).value,
    organization := (renaissanceCore / organization).value,
    scalaVersion := "2.12.13"
  )
  .dependsOn(
    renaissanceCore,
    scalaStmLibrary % "compile->compile;compile->test"
  )
  .aggregate(
    scalaStmLibrary
  )
