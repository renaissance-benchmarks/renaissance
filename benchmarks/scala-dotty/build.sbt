lazy val renaissanceCore = RootProject(uri("../../renaissance-core"))

lazy val scalaDotty = (project in file("."))
  .settings(
    name := "scala-dotty",
    organization := "org.renaissance",
    version := "0.1.0",
    scalafmtConfig := Some(file(".scalafmt.conf")),
    checkstyleConfigLocation := CheckstyleConfigLocation.File("java-checkstyle.xml"),
    scalaVersion := "2.12.8",
    libraryDependencies ++= Seq(
      "commons-io" % "commons-io" % "2.6",
      "ch.epfl.lamp" % "dotty-compiler_0.12" % "0.12.0"
    )
  )
  .dependsOn(
    renaissanceCore
  )
