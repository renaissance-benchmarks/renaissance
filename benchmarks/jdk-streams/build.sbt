lazy val renaissanceCore = RootProject(uri("../../renaissance-core"))

lazy val jdkStreams = (project in file("."))
  .settings(
    name := "jdk-streams",
    version := (renaissanceCore / version).value,
    organization := (renaissanceCore / organization).value,
    scalaVersion := "2.13.6"
  )
  .dependsOn(
    renaissanceCore
  )
