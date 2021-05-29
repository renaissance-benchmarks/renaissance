lazy val renaissanceCore = RootProject(uri("../../renaissance-core"))

val sparkVersion = "3.1.1"

lazy val apacheSpark = (project in file("."))
  .settings(
    name := "apache-spark",
    version := (renaissanceCore / version).value,
    organization := (renaissanceCore / organization).value,
    scalaVersion := "2.12.13",
    libraryDependencies ++= Seq(
      "org.apache.spark" %% "spark-core" % sparkVersion,
      "org.apache.spark" %% "spark-sql" % sparkVersion,
      "org.apache.spark" %% "spark-mllib" % sparkVersion,
      // Not directly required, forces the use of newer version
      "commons-io" % "commons-io" % "2.7"
    )
  )
  .dependsOn(
    renaissanceCore
  )
