lazy val scalaSAT = RootProject(uri("../."))

lazy val scalaSMTLib = RootProject(uri("../scala-smtlib"))

lazy val scalaCafeSAT = (project in file("."))
  .settings(
    name := "CafeSat",
    organization := "com.regblanc",
    version := "0.01",
    scalaVersion := (scalaSAT / scalaVersion).value,
    scalacOptions ++= Seq("-unchecked", "-deprecation", "-feature"),
    libraryDependencies += "org.scalatest" %% "scalatest" % "3.1.4" % "test",
    exportJars := true,
    Test / parallelExecution := true,
  )
  .dependsOn(scalaSMTLib % "compile->compile; compile->test")
  .aggregate(scalaSMTLib)
