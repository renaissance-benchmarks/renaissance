// Minimal configuration to build reactors-common and reactors-core
// needed by Renaissance (without cross-builds and tests).

lazy val reactors = (project in file("."))
lazy val parentProject = ProjectRef(uri("../../.."), "actorsReactorsBenchmarks")


def projectSettings(suffix: String) = {
  Seq(
    name := s"reactors$suffix",
    organization := "io.reactors",
    version := (reactors / version).value,
    scalaVersion := (parentProject / scalaVersion).value,
    scalacOptions := (parentProject / scalacOptions).value ++ Seq(
      "-feature", "-no-specialization"
    ),
    javacOptions := (parentProject / javacOptions).value,
    Compile / unmanagedSourceDirectories := Seq(
      baseDirectory.value / "jvm" / "src" / "main" / "java",
      baseDirectory.value / "jvm" / "src" / "main" / "scala",
      baseDirectory.value / "shared" / "src" / "main" / "scala"
    )
  )
}


lazy val reactorsCommonJVM = (project in file("reactors-common"))
  .settings(projectSettings("-common"))


lazy val reactorsCoreJVM = (project in file("reactors-core"))
  .settings(
    projectSettings("-core") ++ Seq(
      libraryDependencies += "com.typesafe" % "config" % "1.4.2"
    )
  )
  .dependsOn(reactorsCommonJVM)
