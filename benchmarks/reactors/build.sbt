lazy val renaissanceCore = RootProject(uri("../../renaissance-core"))

lazy val actors = (project in file("."))
  .settings(
    name := "reactors",
    organization := "org.renaissance",
    version := "0.1.0",
    scalaVersion := "2.11.8",
    libraryDependencies ++= Seq(
      "io.reactors" %% "reactors-core" % "0.7"
    ),
    scalafmtConfig := Some(file(".scalafmt.conf"))
  )
  .dependsOn(
    renaissanceCore
  )
