lazy val renaissanceCore = RootProject(uri("../../renaissance-core"))

lazy val scalaDotty = (project in file("."))
  .settings(
    name := "scala-dotty",
    version := (version in renaissanceCore).value,
    organization := (organization in renaissanceCore).value,
    // Scala 2.12.8 is the last version able to link to dotty-compiler 0.12.0
    // Scala 2.12.9 and later need a Java bridge to call dotc.Main methods
    scalaVersion := "2.12.12",
    libraryDependencies ++= Seq(
      "commons-io" % "commons-io" % "2.6",
      // dotty-compiler 0.12.0-0.17.0 does not run with Scala 2.13.3
      // dotty-compiler 0.18.1 is the first to run with Scala 2.13.3
      // dotty-compiler 0.13 to 0.26 dislike the input sources
      "ch.epfl.lamp" % "dotty-compiler_0.12" % "0.12.0"
    )
  )
  .dependsOn(
    renaissanceCore
  )
