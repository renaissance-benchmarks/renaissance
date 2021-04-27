lazy val renaissanceCore = RootProject(uri("../../renaissance-core"))

lazy val reactorsCore = ProjectRef(uri("reactors"), "reactorsCoreJVM")
lazy val reactorsCommon = ProjectRef(uri("reactors"), "reactorsCommonJVM")

lazy val actorsReactors = (project in file("."))
  .settings(
    name := "actors-reactors",
    version := (version in renaissanceCore).value,
    organization := (organization in renaissanceCore).value,
    scalaVersion := "2.12.13"
  )
  .dependsOn(
    renaissanceCore,
    reactorsCommon,
    reactorsCore
  )
