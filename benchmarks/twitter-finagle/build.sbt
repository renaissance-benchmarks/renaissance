lazy val renaissanceCore = RootProject(uri("../../renaissance-core"))

val finagleVersion = "21.10.0"

lazy val twitterFinagle = (project in file("."))
  .settings(
    name := "twitter-finagle",
    version := (renaissanceCore / version).value,
    organization := (renaissanceCore / organization).value,
    scalaVersion := "2.13.7",
    scalacOptions ++= Seq("-deprecation", "-feature"),
    libraryDependencies := Seq(
      "com.twitter" %% "finagle-http" % finagleVersion,
      "com.twitter" %% "finagle-stats" % finagleVersion,
      "com.twitter" %% "finagle-core" % finagleVersion,
      "com.twitter" %% "util-core" % finagleVersion,
      "com.google.guava" % "guava" % "19.0",
      "org.scala-lang.modules" %% "scala-parallel-collections" % "1.0.4",
      // Add simple binding to silence SLF4J warnings.
      "org.slf4j" % "slf4j-simple" % "1.7.32"
    )
  )
  .dependsOn(
    renaissanceCore % "provided"
  )
