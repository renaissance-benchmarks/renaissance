lazy val renaissanceCore = RootProject(uri("../../renaissance-core"))

lazy val jdkConcurrent = (project in file("."))
  .settings(
    name := "jdk-concurrent",
    version := (renaissanceCore / version).value,
    organization := (renaissanceCore / organization).value,
    scalaVersion := "2.13.6",
    libraryDependencies ++= Seq(
      "io.jenetics" % "jenetics" % "4.4.0"
    )
  )
  .dependsOn(
    renaissanceCore
  )
