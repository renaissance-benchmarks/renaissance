lazy val renaissanceCore = RootProject(uri("../../renaissance-core"))

lazy val scalaSMTLib = RootProject(uri("scala-smtlib"))

lazy val scalaCafeSAT = RootProject(uri("cafesat"))

lazy val scalaSat = (project in file("."))
  .settings(
    name := "scala-sat",
    version := (version in renaissanceCore).value,
    organization := (organization in renaissanceCore).value,
    scalafmtConfig := Some(file(".scalafmt.conf")),
    scalaVersion := "2.11.7"
  )
  .dependsOn(
    renaissanceCore,
    scalaSMTLib % "compile->compile;compile->test",
    scalaCafeSAT % "compile->compile;compile->test"
  )
  .aggregate(
    scalaSMTLib,
    scalaCafeSAT
  )
