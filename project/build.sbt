//
// Make sure to compile the core classes so that Renaissance
// root project can use them in utility code.
//
dependsOn(RootProject(uri("../renaissance-core")))

//
// The following classes are needed for the Hadoop Client API patcher.
//
libraryDependencies ++= Seq(
  "org.ow2.asm" % "asm" % "9.7",
  "org.scala-lang.modules" %% "scala-collection-compat" % "2.11.0"
)
