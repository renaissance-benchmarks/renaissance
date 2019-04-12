lazy val renaissanceCore = RootProject(uri("../../renaissance-core"))

lazy val jdkConcurrent = (project in file("."))
  .settings(
    name := "jdk-concurrent",
    organization := "org.renaissance",
    version := "0.1.0",
    scalafmtConfig := Some(file(".scalafmt.conf")),
    scalaVersion := "2.12.8",
    libraryDependencies ++= Seq(
      "io.jenetics" % "jenetics" % "4.4.0",
    )
  )
  .dependsOn(
    renaissanceCore
  )
