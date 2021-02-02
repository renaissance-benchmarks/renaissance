lazy val renaissanceCore = RootProject(uri("../../renaissance-core"))

lazy val actorsAkka = (project in file("."))
  .settings(
    name := "actors-akka",
    version := (version in renaissanceCore).value,
    organization := (organization in renaissanceCore).value,
    scalaVersion := "2.11.12",
    libraryDependencies ++= Seq(
      // akka-actor 2.3.16 supports Scala 2.11, 2.12 (latest 2.3.x)
      // akka-actor 2.5.32 supports Scala 2.11, 2.12, 2.13
      // akka-actor 2.6.12 supports Scala 2.12, 2.13
      "com.typesafe.akka" %% "akka-actor" % "2.3.11"
    )
  )
  .dependsOn(
    renaissanceCore
  )
