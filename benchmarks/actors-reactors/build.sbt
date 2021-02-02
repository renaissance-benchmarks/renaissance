lazy val renaissanceCore = RootProject(uri("../../renaissance-core"))

lazy val actorsReactors = (project in file("."))
  .settings(
    name := "actors-reactors",
    version := (version in renaissanceCore).value,
    organization := (organization in renaissanceCore).value,
    scalaVersion := "2.11.12",
    libraryDependencies ++= Seq(
      // reactors-core 0.8 is the latest stable version
      // reactors-core 0.8 does not support Scala 2.12
      "io.reactors" %% "reactors-core" % "0.7"
    )
  )
  .dependsOn(
    renaissanceCore
  )
