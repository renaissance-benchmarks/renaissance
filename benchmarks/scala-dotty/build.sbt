lazy val renaissanceCore = RootProject(uri("../../renaissance-core"))

lazy val scalaDotty = (project in file("."))
  .settings(
    name := "scala-dotty",
    version := (renaissanceCore / version).value,
    organization := (renaissanceCore / organization).value,
    scalaVersion := "2.13.6",
    scalacOptions += "-Ytasty-reader",
    libraryDependencies ++= Seq(
      "org.scala-lang" % "scala3-compiler_3" % "3.0.0",
      // The following is required to compile the workload sources.
      "org.scala-lang" % "scala-compiler" % scalaVersion.value
    )
  )
  .dependsOn(
    renaissanceCore % "provided"
  )
