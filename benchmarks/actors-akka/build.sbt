lazy val renaissanceCore = RootProject(uri("../../renaissance-core"))

lazy val actorsAkka = (project in file("."))
  .settings(
    name := "actors-akka",
    version := (renaissanceCore / version).value,
    organization := (renaissanceCore / organization).value,
    scalaVersion := "2.13.6",
    libraryDependencies ++= Seq(
      // akka-actor 2.6.x supports Scala 2.12, 2.13
      "com.typesafe.akka" %% "akka-actor" % "2.6.12"
    )
  )
  .dependsOn(
    renaissanceCore
  )
