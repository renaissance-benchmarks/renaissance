import sbtcrossproject.CrossPlugin.autoImport.{crossProject, CrossType}

lazy val actorsReactors = RootProject(uri(".."))

val scalaTestVersion = "3.1.4"
val scalaCheckVersion = "1.13.4"
val akkaVersion = "2.6.12"
val scalaMeterVersion = "0.19"
val json4sJacksonVersion = "3.5.5"
val rapidoidVersion = "5.3.5"
val commonsTextVersion = "1.9"

// BrowserTest configuration is meant for browser-based tests.
lazy val BrowserTest = config("browser") extend (Test)

def scalaCheckArgument() =
  Tests.Argument(
      TestFrameworks.ScalaCheck,
      "-minSuccessfulTests", "200",
      "-workers", "1",
      "-verbosity", "2"
  )

def projectSettings(suffix: String) = {
  Seq(
    name := s"reactors$suffix",
    organization := "io.reactors",
    scalaVersion := (actorsReactors / scalaVersion).value,
    logBuffered := false,
    scalacOptions ++= Seq(
      "-deprecation", "-feature", "-no-specialization"
    ),
    Compile / doc / scalacOptions ++= Seq(
      "-implicits"
    ),

    Test / fork := true,
    Test / parallelExecution := false,
    Test / testOptions += scalaCheckArgument(),
    Test / publishArtifact := false,

    Global / concurrentRestrictions += Tags.limit(Tags.Test, 1),
    Global / cancelable := true,

    resolvers ++= Seq(
      "Sonatype OSS Snapshots" at "https://oss.sonatype.org/content/repositories/snapshots",
      "Sonatype OSS Releases" at "https://oss.sonatype.org/content/repositories/releases",
      "Typesafe Repository" at "https://repo.typesafe.com/typesafe/releases/"
    ),

    ThisBuild / parallelExecution := false
  )
}


def jvmProjectSettings(suffix: String) =
  Seq(
    Test / javaOptions ++= Seq(
      "-Xmx3G",
      "-agentlib:jdwp=transport=dt_socket,server=y,suspend=n,address=5005"
    ),
  )


// Produces reactorsCommonJVM

lazy val reactorsCommon = crossProject(JVMPlatform)
  .crossType(CrossType.Full)
  .in(file("reactors-common"))
  .settings(
    projectSettings("-common") ++ Seq(
      libraryDependencies ++= Seq(
        "org.scalatest" %%% "scalatest" % scalaTestVersion % "test",
        "org.scalacheck" %%% "scalacheck" % scalaCheckVersion % "test"
      ),
      unmanagedSourceDirectories in Compile +=
        baseDirectory.value.getParentFile / "shared" / "src" / "main" / "scala",
      unmanagedSourceDirectories in Test +=
        baseDirectory.value.getParentFile / "shared" / "src" / "test" / "scala"
    ): _*
  )
  .jvmSettings(
    jvmProjectSettings("-common") ++ Seq(
      libraryDependencies ++= Seq(
        "com.typesafe.akka" %% "akka-actor" % akkaVersion % "test",
        "com.storm-enroute" %% "scalameter" % scalaMeterVersion % "test"
      )
    ): _*
  )


// Produces reactorsCoreJVM 

lazy val reactorsCore = crossProject(JVMPlatform)
  .crossType(CrossType.Full)
  .in(file("reactors-core"))
  .settings(
    projectSettings("-core") ++ Seq(
      libraryDependencies ++= Seq(
        "org.scalatest" %%% "scalatest" % scalaTestVersion % "test",
        "org.scalacheck" %%% "scalacheck" % scalaCheckVersion % "test"
      ),
      Compile / unmanagedSourceDirectories +=
        baseDirectory.value.getParentFile / "shared" / "src" / "main" / "scala",
      Test / unmanagedSourceDirectories +=
        baseDirectory.value.getParentFile / "shared" / "src" / "test" / "scala"
    ): _*
  )
  .jvmSettings(
    jvmProjectSettings("-core") ++ Seq(
      libraryDependencies ++= Seq(
        "com.typesafe" % "config" % "1.4.1",
        "com.typesafe.akka" %% "akka-actor" % akkaVersion % "test",
        "com.storm-enroute" %% "scalameter" % scalaMeterVersion % "test"
      )
    ): _*
  )
  .dependsOn(reactorsCommon % "compile->compile;test->test")


// Produces reactorsContainerJVM

lazy val reactorsContainer = crossProject(JVMPlatform)
  .crossType(CrossType.Full)
  .in(file("reactors-container"))
  .settings(
    projectSettings("-container") ++ Seq(
      libraryDependencies ++= Seq(
        "org.scalatest" %%% "scalatest" % scalaTestVersion % "test",
        "org.scalacheck" %%% "scalacheck" % scalaCheckVersion % "test"
      ),
      unmanagedSourceDirectories in Compile +=
        baseDirectory.value.getParentFile / "shared" / "src" / "main" / "scala",
      unmanagedSourceDirectories in Test +=
        baseDirectory.value.getParentFile / "shared" / "src" / "test" / "scala"
    ): _*
  )
  .jvmSettings(
    jvmProjectSettings("-container") ++ Seq(
      libraryDependencies ++= Seq(
        "com.storm-enroute" %% "scalameter" % scalaMeterVersion % "test"
      )
    ): _*
  )
  .dependsOn(
    reactorsCore % "compile->compile;test->test"
  )


// Produces reactorsProtocolJVM

lazy val reactorsProtocol = crossProject(JVMPlatform)
  .crossType(CrossType.Full)
  .in(file("reactors-protocol"))
  .settings(
    projectSettings("-protocol") ++ Seq(
      libraryDependencies ++= Seq(
        "org.scalatest" %%% "scalatest" % scalaTestVersion % "test",
        "org.scalacheck" %%% "scalacheck" % scalaCheckVersion % "test"
      ),
      unmanagedSourceDirectories in Compile +=
        baseDirectory.value.getParentFile / "shared" / "src" / "main" / "scala",
      unmanagedSourceDirectories in Test +=
        baseDirectory.value.getParentFile / "shared" / "src" / "test" / "scala"
    ): _*
  )
  .jvmSettings(
    jvmProjectSettings("-protocol"): _*
  )
  .dependsOn(
    reactorsCommon % "compile->compile;test->test",
    reactorsCore % "compile->compile;test->test",
    reactorsContainer % "compile->compile;test->test"
  )


// Produces reactorsRemoteJVM

lazy val reactorsRemote = crossProject(JVMPlatform)
  .crossType(CrossType.Full)
  .in(file("reactors-remote"))
  .settings(
    projectSettings("-remote") ++ Seq(
      libraryDependencies ++= {
        Seq(
          "org.scalatest" %%% "scalatest" % scalaTestVersion % "test",
          "org.scalacheck" %%% "scalacheck" % scalaCheckVersion % "test",
          "org.scala-lang" % "scala-reflect" % scalaVersion.value
        )
      },
      unmanagedSourceDirectories in Compile +=
        baseDirectory.value.getParentFile / "shared" / "src" / "main" / "scala",
      unmanagedSourceDirectories in Test +=
        baseDirectory.value.getParentFile / "shared" / "src" / "test" / "scala"
    ): _*
  )
  .jvmSettings(
    jvmProjectSettings("-remote"): _*
  )
  .dependsOn(
    reactorsCore % "compile->compile;test->test"
  )


// JVM-only project reactorsExtra

lazy val reactorsExtra = project
  .in(file("reactors-extra"))
  .settings(
    projectSettings("-extra") ++ Seq(
      libraryDependencies ++= {
        Seq(
          "org.scala-lang" % "scala-reflect" % scalaVersion.value,
          "org.scalatest" %%% "scalatest" % scalaTestVersion % "test",
          "org.scalacheck" %%% "scalacheck" % scalaCheckVersion % "test",
          "com.typesafe.akka" %% "akka-actor" % akkaVersion % "test"
        )
      }
    ): _*
  )
  .settings(
    jvmProjectSettings("-extra"): _*
  )
  .dependsOn(
    reactorsCore.jvm % "compile->compile;test->test",
    reactorsProtocol.jvm % "compile->compile;test->test"
  )


// JVM-only project reactorsHttp

lazy val reactorsHttp = project
  .in(file("reactors-http"))
  .configs(BrowserTest)
  .settings(inConfig(BrowserTest)(Defaults.testTasks): _*)
  .settings(
    projectSettings("-http") ++ Seq(
      libraryDependencies ++= {
        Seq(
          "org.scalatest" %%% "scalatest" % scalaTestVersion % "test",
          "org.scalacheck" %%% "scalacheck" % scalaCheckVersion % "test",
          "org.scala-lang" % "scala-compiler" % scalaVersion.value,
          "org.rapidoid" % "rapidoid-http-server" % rapidoidVersion,
          "commons-io" % "commons-io" % "2.4",
          "org.apache.commons" % "commons-text" % commonsTextVersion,
          "org.scala-lang.platform" %% "scalajson" % "1.0.0-M4",
          "org.json4s" %% "json4s-jackson" % json4sJacksonVersion,
          "org.seleniumhq.selenium" % "selenium-java" % "2.53.1" % "test",
          "org.seleniumhq.selenium" % "selenium-chrome-driver" % "2.53.1" % "test"
        )
      },

      // Disable browser-based tests in normal testing.
      Test / testOptions := Seq(Tests.Filter(_ => false)),
      BrowserTest / testOptions := Seq(scalaCheckArgument()),
    ): _*
  )
  .settings(
    jvmProjectSettings("-http"): _*
  )
  .dependsOn(
    reactorsCore.jvm % "compile->compile;test->test",
    reactorsProtocol.jvm % "compile->compile;test->test"
  )


// JVM-only project reactorsDebugger

lazy val reactorsDebugger = project
  .in(file("reactors-debugger"))
  .configs(BrowserTest)
  .settings(inConfig(BrowserTest)(Defaults.testTasks): _*)
  .settings(
    projectSettings("-debugger") ++ Seq(
      libraryDependencies ++= {
        Seq(
          "org.scalatest" %%% "scalatest" % scalaTestVersion % "test",
          "org.scalacheck" %%% "scalacheck" % scalaCheckVersion % "test",
          "org.scala-lang" % "scala-compiler" % scalaVersion.value,
          "org.rapidoid" % "rapidoid-http-server" % rapidoidVersion,
          "org.rapidoid" % "rapidoid-gui" % rapidoidVersion,
          "com.github.spullara.mustache.java" % "compiler" % "0.9.2",
          "commons-io" % "commons-io" % "2.4",
          "org.apache.commons" % "commons-text" % commonsTextVersion,
          "org.seleniumhq.selenium" % "selenium-java" % "2.53.1" % "test",
          "org.seleniumhq.selenium" % "selenium-chrome-driver" % "2.53.1" % "test"
        )
      },

      // Disable browser-based tests in normal testing.
      Test / testOptions := Seq(Tests.Filter(_ => false)),
      BrowserTest / testOptions := Seq(scalaCheckArgument()),
    ): _*
  )
  .settings(
    jvmProjectSettings("-debugger"): _*
  )
  .dependsOn(
    reactorsCore.jvm % "compile->compile;test->test",
    reactorsProtocol.jvm % "compile->compile;test->test",
    reactorsHttp % "compile->compile;test->test"
  )


// Produces reactorsJVM

lazy val reactors = crossProject(JVMPlatform)
  .crossType(CrossType.Full)
  .in(file("reactors"))
  .settings(
    projectSettings("") ++ Seq(
      libraryDependencies ++= Seq(
        "org.scalatest" %%% "scalatest" % scalaTestVersion % "test",
        "org.scalacheck" %%% "scalacheck" % scalaCheckVersion % "test"
      ),
      unmanagedSourceDirectories in Compile +=
        baseDirectory.value.getParentFile / "shared" / "src" / "main" / "scala",
      unmanagedSourceDirectories in Test +=
        baseDirectory.value.getParentFile / "shared" / "src" / "test" / "scala",
    ): _*
  )
  .jvmSettings(
    jvmProjectSettings("") ++ Seq(
      libraryDependencies ++= Seq(
        "com.novocode" % "junit-interface" % "0.11" % "test",
        "junit" % "junit" % "4.12" % "test"
      )
    ): _*
  )
  .jvmConfigure(
    _.dependsOn(
      reactorsHttp % "compile->compile;test->test",
      reactorsDebugger % "compile->compile;test->test",
      reactorsExtra % "compile->compile;test->test"
    )
  )
  .dependsOn(
    reactorsCommon % "compile->compile;test->test",
    reactorsCore % "compile->compile;test->test",
    reactorsContainer % "compile->compile;test->test",
    reactorsRemote % "compile->compile;test->test",
    reactorsProtocol % "compile->compile;test->test"
  )
