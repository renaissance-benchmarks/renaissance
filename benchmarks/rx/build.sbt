lazy val renaissanceCore = RootProject(uri("../../renaissance-core"))

lazy val scalaStdlib = (project in file("."))
  .settings(
    name := "rx",
    version := (version in renaissanceCore).value,
    organization := (organization in renaissanceCore).value,
    scalafmtConfig := Some(file(".scalafmt.conf")),
    scalaVersion := "2.11.8",
    libraryDependencies ++= Seq(
      "io.reactivex" % "rxjava" % "1.3.7",
      "commons-io" % "commons-io" % "2.6"
    )
  )
  .dependsOn(
    renaissanceCore
  )
