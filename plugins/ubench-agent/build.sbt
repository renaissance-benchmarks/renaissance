lazy val renaissanceCore = RootProject(uri("../../renaissance-core"))

lazy val pluginUbenchAgent = (project in file("."))
  .settings(
    name := "plugin-ubenchagent",
    version := "0.0.1",
    crossPaths := false,
    autoScalaLibrary := false,
    organization := (renaissanceCore / organization).value,
    assembly / assemblyMergeStrategy := {
      case PathList("META-INF", "MANIFEST.MF") => MergeStrategy.discard
      case PathList("org", "renaissance", "plugins", _*) => MergeStrategy.first
      case PathList("org", "renaissance", _*) => MergeStrategy.discard
      case _ => MergeStrategy.singleOrError
    },
  )
  .dependsOn(
    renaissanceCore
  )
