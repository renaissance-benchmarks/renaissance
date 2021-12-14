lazy val parentProject = ProjectRef(uri("../../.."), "scalaSatBenchmarks")

lazy val scalaCafeSAT = (project in file("."))
  .settings(
    name := "CafeSat",
    organization := "com.regblanc",
    scalaVersion := (parentProject / scalaVersion).value,
    scalacOptions ++= Seq("-unchecked", "-deprecation", "-feature"),
    libraryDependencies += "org.scalatest" %% "scalatest" % "3.1.4" % "test",
    Test / parallelExecution := true,
  )
