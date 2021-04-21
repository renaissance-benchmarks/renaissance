lazy val renaissanceCore = RootProject(uri("../../renaissance-core"))

lazy val scalaDotty = (project in file("."))
  .settings(
    name := "scala-dotty",
    version := (version in renaissanceCore).value,
    organization := (organization in renaissanceCore).value,
    scalaVersion := "2.13.5",
    scalacOptions += "-Ytasty-reader",
    libraryDependencies ++= Seq(
      "org.scala-lang.modules" %% "scala-collection-compat" % "2.4.2",
      // 3.0.0-RC1 is as far as we can go with Tasty reader in 2.13.5
      "org.scala-lang" % "scala3-compiler_3.0.0-RC1" % "3.0.0-RC1"
    )
  )
  .dependsOn(
    renaissanceCore
  )
