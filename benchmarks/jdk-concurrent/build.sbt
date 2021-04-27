lazy val renaissanceCore = RootProject(uri("../../renaissance-core"))

lazy val jdkConcurrent = (project in file("."))
  .settings(
    name := "jdk-concurrent",
    version := (version in renaissanceCore).value,
    organization := (organization in renaissanceCore).value,
    scalaVersion := "2.13.5",
    libraryDependencies ++= Seq(
      "io.jenetics" % "jenetics" % "4.4.0"
    )
  )
  .dependsOn(
    renaissanceCore
  )
