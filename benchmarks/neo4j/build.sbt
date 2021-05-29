lazy val renaissanceCore = RootProject(uri("../../renaissance-core"))

lazy val neo4j = (project in file("."))
  .settings(
    name := "neo4j",
    version := (renaissanceCore / version).value,
    organization := (renaissanceCore / organization).value,
    scalaVersion := "2.12.13",
    scalacOptions += "-target:jvm-1.8",
    libraryDependencies ++= Seq(
      // neo4j 4.2 does not support 2.13
      "org.neo4j" % "neo4j" % "4.2.4",
      "net.liftweb" %% "lift-json" % "3.4.3"
    )
  )
  .dependsOn(
    renaissanceCore
  )
