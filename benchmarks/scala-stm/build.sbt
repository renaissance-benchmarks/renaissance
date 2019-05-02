lazy val renaissanceCore = RootProject(uri("../../renaissance-core"))

lazy val scalaStmLibrary = RootProject(uri("scala-stm-library"))

lazy val scalaStm = (project in file("."))
  .settings(
    name := "scala-stm",
    organization := "org.renaissance",
    version := "0.1.0",
    scalaVersion := "2.12.3",
    scalafmtConfig := Some(file(".scalafmt.conf")),
    checkstyleConfigLocation := CheckstyleConfigLocation.File("java-checkstyle.xml")
  )
  .dependsOn(
    renaissanceCore,
    scalaStmLibrary % "compile->compile;compile->test"
  )
  .aggregate(
    scalaStmLibrary
  )
