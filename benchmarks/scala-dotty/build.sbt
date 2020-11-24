lazy val renaissanceCore = RootProject(uri("../../renaissance-core"))

lazy val scalaDotty = (project in file("."))
  .settings(
    name := "scala-dotty",
    version := (version in renaissanceCore).value,
    organization := (organization in renaissanceCore).value,
    scalaVersion := "2.13.4",
    scalacOptions += "-Ytasty-reader",
    libraryDependencies ++= Seq(
      "commons-io" % "commons-io" % "2.6",
      "org.scala-lang" % "scala3-compiler_3.0.0-M1" % "3.0.0-M1"
    )
  )
  .dependsOn(
    renaissanceCore
  )
