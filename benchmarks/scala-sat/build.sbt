lazy val renaissanceCore = RootProject(uri("../../renaissance-core"))

lazy val scalaSMTLib = RootProject(uri("scala-smtlib"))

lazy val scalaCafeSAT = RootProject(uri("cafesat"))

lazy val scalaSAT = (project in file("."))
  .settings(
    name := "scala-sat",
    version := (renaissanceCore / version).value,
    organization := (renaissanceCore / organization).value,
    scalaVersion := "2.13.6"
  )
  .dependsOn(
    renaissanceCore,
    scalaSMTLib,
    scalaCafeSAT
  )
