lazy val renaissanceCore = RootProject(uri("../../renaissance-core"))

// Note: these versions should not be changed here.
// If we want to target a different Spark version, we should instead clone this subproject.
// That way, we make it convenient to run the old versions,
// and avoid the benchmarking of a moving target.
val sparkScalaVersion = "2.11.8"

val sparkVersion = "2.0.0"

lazy val apacheSpark = (project in file("."))
  .settings(
    name := "apache-spark",
    organization := "org.renaissance",
    scalaVersion := sparkScalaVersion,
    libraryDependencies := Seq(
      "org.apache.spark" %% "spark-core" % sparkVersion,
      "org.apache.spark" %% "spark-sql" % sparkVersion,
      "org.apache.spark" %% "spark-mllib" % sparkVersion
    ),
    scalafmtConfig := Some(file(".scalafmt.conf"))
  )
  .dependsOn(
    renaissanceCore
  )