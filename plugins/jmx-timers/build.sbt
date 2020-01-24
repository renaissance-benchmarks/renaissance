lazy val renaissanceCore = RootProject(uri("../../renaissance-core"))

lazy val pluginJMXTimers = (project in file("."))
  .settings(
    name := "plugin-jmxtimers",
    version := "0.0.2",
    crossPaths := false,
    autoScalaLibrary := false,
    organization := (organization in renaissanceCore).value,
    assemblyMergeStrategy in assembly := {
      case PathList("META-INF", "MANIFEST.MF") => MergeStrategy.discard
      case PathList("org", "renaissance", "plugins", _*) => MergeStrategy.first
      case PathList("org", "renaissance", _*) => MergeStrategy.discard
      case _ => MergeStrategy.singleOrError
    },
  )
  .dependsOn(
    renaissanceCore
  )
