lazy val renaissanceCore = RootProject(uri("../../renaissance-core"))

lazy val jdkStreams = (project in file("."))
  .settings(
    name := "jdk-streams",
    version := (version in renaissanceCore).value,
    organization := (organization in renaissanceCore).value,
    scalaVersion := "2.13.5",
    libraryDependencies ++= Seq(
      "commons-io" % "commons-io" % "2.6"
    )
  )
  .dependsOn(
    renaissanceCore
  )
