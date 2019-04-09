lazy val renaissanceCore = RootProject(uri("../../renaissance-core"))

lazy val jdkStreams = (project in file("."))
  .settings(
    name := "jdk-streams",
    organization := "org.renaissance",
    version := "0.1.0",
    scalafmtConfig := Some(file(".scalafmt.conf")),
    scalaVersion := "2.12.8",
    libraryDependencies ++= Seq(
      "commons-io" % "commons-io" % "2.6"
    )
  )
  .dependsOn(
    renaissanceCore
  )
