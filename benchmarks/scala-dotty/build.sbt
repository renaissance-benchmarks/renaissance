lazy val renaissanceCore = RootProject(uri("../../renaissance-core"))

lazy val scalaDotty = (project in file("."))
  .settings(
    name := "scala-dotty",
    version := (version in renaissanceCore).value,
    organization := (organization in renaissanceCore).value,
    scalafmtConfig := Some(file(".scalafmt.conf")),
    scalaVersion := "2.12.8",
    libraryDependencies ++= Seq(
      "commons-io" % "commons-io" % "2.6",
      "ch.epfl.lamp" % "dotty-compiler_0.12" % "0.12.0"
    )
  )
  .dependsOn(
    renaissanceCore
  )
