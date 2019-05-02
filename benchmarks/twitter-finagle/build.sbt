lazy val renaissanceCore = RootProject(uri("../../renaissance-core"))

lazy val twitterFinagle = (project in file("."))
  .settings(
    name := "twitter-finagle",
    organization := "org.renaissance",
    version := "0.1.0",
    scalaVersion := "2.11.8",
    libraryDependencies := Seq(
      "com.twitter" %% "finagle-http" % "19.4.0",
      "com.twitter" %% "finagle-stats" % "19.4.0",
      "com.twitter" %% "finagle-core" % "19.4.0",
      "com.twitter" %% "twitter-server" % "19.4.0",
      "com.twitter.common" % "metrics" % "0.0.39",
      "com.twitter.common" % "io" % "0.0.69",
      "com.twitter" %% "util-core" % "19.4.0",
      "com.twitter" %% "util-events" % "7.0.0"
    ),
    scalafmtConfig := Some(file(".scalafmt.conf")),
    checkstyleConfigLocation := CheckstyleConfigLocation.File("java-checkstyle.xml")
  )
  .dependsOn(
    renaissanceCore
  )
