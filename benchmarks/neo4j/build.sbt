lazy val renaissanceCore = RootProject(uri("../../renaissance-core"))

lazy val neo4j = (project in file("."))
  .settings(
    name := "neo4j",
    version := (version in renaissanceCore).value,
    organization := (organization in renaissanceCore).value,
    scalafmtConfig := Some(file(".scalafmt.conf")),
    scalaVersion := "2.11.4",
    libraryDependencies ++= Seq(
      "commons-io" % "commons-io" % "2.6",
      "org.neo4j" % "neo4j" % "3.3.4",
      "net.liftweb" %% "lift-json" % "3.2.0"
    )
  )
  .dependsOn(
    renaissanceCore
  )
