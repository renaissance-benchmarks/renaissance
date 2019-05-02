val renaissanceVersion = "0.1"

lazy val renaissanceCore = (project in file("."))
  .settings(
    name := "renaissance-core",
    version := renaissanceVersion,
    organization := "org.renaissance",
    crossPaths := false,
    autoScalaLibrary := false,
    checkstyleConfigLocation := CheckstyleConfigLocation.File("java-checkstyle.xml")
  )

