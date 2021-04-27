lazy val renaissanceCore = RootProject(uri("../../renaissance-core"))

lazy val scalaSMTLib = RootProject(uri("scala-smtlib"))

lazy val scalaCafeSAT = RootProject(uri("cafesat"))

lazy val scalaSAT = (project in file("."))
  .settings(
    name := "scala-sat",
    version := (version in renaissanceCore).value,
    organization := (organization in renaissanceCore).value,
    scalaVersion := "2.13.5"
  )
  .dependsOn(
    renaissanceCore,
    scalaSMTLib,
    scalaCafeSAT
  )
