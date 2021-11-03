lazy val renaissanceCore = RootProject(uri("../../renaissance-core"))

val sparkVersion = "3.2.0"

lazy val apacheSpark = (project in file("."))
  .settings(
    name := "apache-spark",
    version := (renaissanceCore / version).value,
    organization := (renaissanceCore / organization).value,
    scalaVersion := "2.13.7",
    scalacOptions ++= Seq("-deprecation"),
    libraryDependencies ++= Seq(
      "org.apache.spark" %% "spark-core" % sparkVersion,
      "org.apache.spark" %% "spark-sql" % sparkVersion,
      "org.apache.spark" %% "spark-mllib" % sparkVersion
    )
  )
  .dependsOn(
    renaissanceCore % "provided"
  )
