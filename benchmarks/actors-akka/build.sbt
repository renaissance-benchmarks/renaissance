lazy val renaissanceCore = RootProject(uri("../../renaissance-core"))

lazy val actorsAkka = (project in file("."))
  .settings(
    name := "actors-akka",
    version := (version in renaissanceCore).value,
    organization := (organization in renaissanceCore).value,
    scalaVersion := "2.13.5",
    libraryDependencies ++= Seq(
      // akka-actor 2.6.x supports Scala 2.12, 2.13
      "com.typesafe.akka" %% "akka-actor" % "2.6.12"
    )
  )
  .dependsOn(
    renaissanceCore
  )
