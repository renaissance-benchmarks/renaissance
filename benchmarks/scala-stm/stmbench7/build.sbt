lazy val parentProject = ProjectRef(uri("../../.."), "scalaStmBenchmarks")

lazy val stmBench7 = (project in file("."))
  .settings(
    name := "stmbench7",
    organization := "ch.epfl.dcl",
    version := "1.0-20110215-nodeuce",
    crossPaths := false,
    autoScalaLibrary := false,
    javacOptions := (parentProject / javacOptions).value,
    exportJars := true
  )
