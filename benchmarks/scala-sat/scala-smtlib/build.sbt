lazy val parentProject = ProjectRef(uri("../../.."), "scalaSatBenchmarks")

lazy val scalaSMTLib = (project in file("."))
  .settings(
    name := "scala-smtlib",
    organization := "com.regblanc",
    scalaVersion := (parentProject / scalaVersion).value,
    scalacOptions := (parentProject / scalacOptions).value ++ Seq("-unchecked", "-feature"),
    scalacOptions += "-Wconf:origin=smtlib[.].*[.]InteractiveMode:s",
    libraryDependencies += "org.scalatest" %% "scalatest" % "3.1.4" % "test",
    licenses := Seq("MIT-style" -> url("https://opensource.org/licenses/MIT")),
    Test / parallelExecution := true
  )
