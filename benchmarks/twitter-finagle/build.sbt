lazy val renaissanceCore = RootProject(uri("../../renaissance-core"))

lazy val twitterFinagle = (project in file("."))
  .settings(
    name := "twitter-finagle",
    version := (version in renaissanceCore).value,
    organization := (organization in renaissanceCore).value,
    scalaVersion := "2.12.13",
    libraryDependencies := Seq(
      "com.twitter" %% "finagle-http" % "19.4.0",
      "com.twitter" %% "finagle-stats" % "19.4.0",
      "com.twitter" %% "finagle-core" % "19.4.0",
      "com.twitter" %% "util-core" % "19.4.0",
      "com.google.guava" % "guava" % "19.0"
    )
  )
  .dependsOn(
    renaissanceCore
  )
