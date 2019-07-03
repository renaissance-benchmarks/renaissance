name := "Scala SMT-LIB"

version := "0.1"

scalaVersion := "2.12.8"

crossScalaVersions := Seq("2.10.4", "2.11.2")

scalacOptions ++= Seq("-unchecked", "-deprecation", "-feature")

libraryDependencies += "org.scalatest" % "scalatest_2.11" % "2.2.1" % "test"

exportJars := true
