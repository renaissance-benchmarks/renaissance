lazy val scalaSAT = RootProject(uri("../."))

lazy val scalaSMTLib = (project in file("."))
  .settings(
    name := "scala-smtlib",
    organization := "com.regblanc",
    scalaVersion := (scalaSAT / scalaVersion).value,
    scalacOptions := Seq("-unchecked", "-deprecation", "-feature"),
    scalacOptions += "-Wconf:origin=smtlib[.].*[.]InteractiveMode:s",
    libraryDependencies += "org.scalatest" %% "scalatest" % "3.1.4" % "test",
    licenses := Seq("MIT-style" -> url("https://opensource.org/licenses/MIT")),
    Test / parallelExecution := true
  )
