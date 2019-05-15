lazy val renaissanceCore = RootProject(uri("../../renaissance-core"))

lazy val dummy = (project in file("."))
  .settings(
    name := "dummy",
    version := (version in renaissanceCore).value,
    organization := (organization in renaissanceCore).value,
    scalafmtConfig := Some(file(".scalafmt.conf"))
  )
  .dependsOn(
    renaissanceCore
  )
