lazy val renaissanceCore = RootProject(uri("../renaissance-core"))

lazy val renaissanceHarness = (project in file("."))
  .settings(
    name := "renaissance-harness",
    version := (renaissanceCore / version).value,
    organization := (renaissanceCore / organization).value,
    scalaVersion := "2.13.6",
    javacOptions ++= Seq("-source", "1.8", "-target", "1.8"),
    libraryDependencies ++= Seq(
      "com.github.scopt" %% "scopt" % "4.0.0-RC2",
      "io.spray" %% "spray-json" % "1.3.5"
    )
  )
  .dependsOn(
    renaissanceCore
  )
