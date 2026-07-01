//
// Make sure to compile the core classes so that Renaissance
// root project can use them in utility code.
//
dependsOn(RootProject(uri("../renaissance-core")))

//
// The following classes are needed for the JAR patcher.
//
libraryDependencies ++= Seq(
  "org.scala-lang.modules" %% "scala-collection-compat" % "2.13.0"
)
