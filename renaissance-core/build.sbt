enablePlugins(GitVersioning)
git.useGitDescribe := true

lazy val renaissanceCore = (project in file("."))
  .settings(
    name := "renaissance-core",
    organization := "org.renaissance",
    crossPaths := false,
    autoScalaLibrary := false,
    javacOptions ++= Seq("-source", "1.8", "-target", "1.8")
  )
