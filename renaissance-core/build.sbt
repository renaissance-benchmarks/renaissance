val renaissanceVersion = "0.1"

val renaissanceScalaVersion = "2.12.8"

lazy val renaissanceCore = (project in file("."))
  .settings(
    name := "renaissance-core",
    version := renaissanceVersion,
    organization := "org.renaissance",
    scalaVersion := renaissanceScalaVersion,
    libraryDependencies ++= Seq(
      ),
    scalafmtConfig := Some(file(".scalafmt.conf")),
    crossPaths := false,
    autoScalaLibrary := false
  )
