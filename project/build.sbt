lazy val renaissanceCore = RootProject(uri("../renaissance-core"))

lazy val renaissanceBuild = (project in file("."))
  .settings(
    name := "renaissance-build"
  )
  .dependsOn(
    renaissanceCore
  )
