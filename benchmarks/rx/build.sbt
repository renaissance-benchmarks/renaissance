lazy val renaissanceCore = RootProject(uri("../../renaissance-core"))

lazy val rx = (project in file("."))
  .settings(
    name := "rx",
    version := (renaissanceCore / version).value,
    organization := (renaissanceCore / organization).value,
    scalaVersion := "2.13.6",
    libraryDependencies ++= Seq(
      "io.reactivex" % "rxjava" % "1.3.7"
    )
  )
  .dependsOn(
    renaissanceCore
  )
