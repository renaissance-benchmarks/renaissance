lazy val renaissanceCore = RootProject(uri("../../renaissance-core"))

lazy val rx = (project in file("."))
  .settings(
    name := "rx",
    version := (version in renaissanceCore).value,
    organization := (organization in renaissanceCore).value,
    scalaVersion := "2.13.5",
    libraryDependencies ++= Seq(
      "io.reactivex" % "rxjava" % "1.3.7",
      "commons-io" % "commons-io" % "2.6"
    )
  )
  .dependsOn(
    renaissanceCore
  )
