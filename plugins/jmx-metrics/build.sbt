lazy val renaissanceCore = RootProject(uri("../../renaissance-core"))

lazy val pluginJMXMetrics = (project in file("."))
  .settings(
    name := "plugin-jmxmetrics",
    version := "0.9.0",
    crossPaths := false,
    autoScalaLibrary := false,
    organization := "org.renaissance",
    assembly / assemblyMergeStrategy := {
      case PathList("META-INF", "MANIFEST.MF") => MergeStrategy.discard
      case PathList("org", "renaissance", "plugins", _*) => MergeStrategy.first
      case PathList("org", "renaissance", _*) => MergeStrategy.discard
      case _ => MergeStrategy.singleOrError
    },
    javacOptions ++= Seq("--release", "11", "-Xlint:unchecked"),
    packageOptions += sbt.Package.ManifestAttributes(
      ("Renaissance-Plugin", "org.renaissance.plugins.jmxmetrics.Main"),
      ("Git-Head-Commit", git.gitHeadCommit.value.getOrElse("unknown")),
      ("Git-Head-Commit-Date", git.gitHeadCommitDate.value.getOrElse("unknown")),
      ("Git-Uncommitted-Changes", git.gitUncommittedChanges.value.toString)
    ),
    libraryDependencies ++= Seq(
      "org.junit.jupiter" % "junit-jupiter" % "5.14.1" % Test,
      "com.github.sbt.junit" % "jupiter-interface" % JupiterKeys.jupiterVersion.value % Test
    ),
  )
  .dependsOn(renaissanceCore % "provided")
