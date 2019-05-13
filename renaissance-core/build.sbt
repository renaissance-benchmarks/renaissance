lazy val renaissanceCore = (project in file("."))
  .settings(
    name := "renaissance-core",
    organization := "org.renaissance",
    crossPaths := false,
    autoScalaLibrary := false,
    scalafmtConfig := Some(file(".scalafmt.conf"))
  )
