lazy val parentProject = ProjectRef(uri("../../.."), "scalaStmBenchmarks")

name := "scala-stm-library"

organization := "org.scala-stm"

version := "0.8-SNAPSHOT"

scalaVersion := (parentProject / scalaVersion).value

libraryDependencies += ("org.scalatest" %% "scalatest" % "3.0.4" % "test")

libraryDependencies += ("junit" % "junit" % "4.12" % "test")

// skip exhaustive tests
testOptions += Tests.Argument("-l", "slow")

// test of TxnExecutor.transformDefault must be run by itself
Test / parallelExecution := false

exportJars := true

