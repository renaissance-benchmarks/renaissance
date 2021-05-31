lazy val renaissanceCore = RootProject(uri("../../renaissance-core"))

lazy val dummy = (project in file("."))
  .settings(
    name := "dummy",
    version := (renaissanceCore / version).value,
    organization := (renaissanceCore / organization).value,
    crossPaths := false,
    autoScalaLibrary := false
  )
  .dependsOn(
    renaissanceCore
  )
