

lazy val renaissanceCore = RootProject(uri("../../renaissance-core"))


lazy val scalaStdlib = (project in file("."))
  .settings(
    name := "scala-stdlib",
    organization := "org.renaissance"
  ).dependsOn(
    renaissanceCore
  )
