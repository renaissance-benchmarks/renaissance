lazy val renaissanceCore = RootProject(uri("../../renaissance-core"))

lazy val actors = (project in file("."))
  .settings(
    name := "actors",
    version := (version in renaissanceCore).value,
    organization := (organization in renaissanceCore).value,
    scalaVersion := "2.11.12",
    libraryDependencies ++= Seq(
      // akka-actor 2.3.16 supports Scala 2.10, 2.11 (latest 2.3.x)
      // akka-actor 2.5.31 supports Scala 2.11, 2.12, 2.13
      // akka-actor 2.6.9 supports Scala 2.12, 2.13
      "com.typesafe.akka" %% "akka-actor" % "2.3.11",
      // reactors-core 0.8 is the latest stable version
      // reactors-core 0.8 does not support Scala 2.12
      "io.reactors" %% "reactors-core" % "0.7"
    )
  )
  .dependsOn(
    renaissanceCore
  )
