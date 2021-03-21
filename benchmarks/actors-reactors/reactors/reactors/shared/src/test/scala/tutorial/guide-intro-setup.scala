/*!md
---
layout: tutorial
title: Setting up Reactors.IO
topic: reactors
logoname: reactress-mini-logo-flat.png
projectname: Reactors.IO
homepage: http://reactors.io
permalink: /reactors/setup/index.html
pagenum: 2
pagetot: 40
section: guide-intro
---
!*/
package tutorial



import io.reactors._
import org.scalatest._
import scala.concurrent.Promise
import scala.concurrent.ExecutionContext
import org.scalatest.funsuite.AsyncFunSuite



/*!md
## Setup

This section contains instructions on how to get Reactors working in your project.
Reactors.IO has multiple language frontends, and works on multiple platforms.
Currently, Reactors can be used with Scala and Java as a library for the JVM,
or alternatively on NodeJS or inside the browser if you are using the Scala.js frontend.


### SBT

If you are developing using the [sbt](http://www.scala-sbt.org/) build tool,
the easiest is to include Reactors into your project as a library dependency.

To get started with Reactors.IO, you should grab the latest snapshot version distributed
on Maven. If you are using SBT, add the following to your project definition:

```scala
resolvers ++= Seq(
  "Sonatype OSS Snapshots" at
    "https://oss.sonatype.org/content/repositories/snapshots",
  "Sonatype OSS Releases" at
    "https://oss.sonatype.org/content/repositories/releases"
)

libraryDependencies ++= Seq(
  "io.reactors" %% "reactors" % "0.8-SNAPSHOT")
```

If you are using Scala.js, use the following dependency:

```scala
libraryDependencies ++= Seq(
  "io.reactors" %%% "reactors" % "0.8-SNAPSHOT")
```

The dependency above includes all the Reactors modules.
You can also depend on a specific module, for example, `reactors-core`,
which includes only the core functionality:

```
libraryDependencies ++= Seq(
  "io.reactors" %% "reactors-core" % "0.8-SNAPSHOT")
```

If you are using Scala.js:

```
libraryDependencies ++= Seq(
  "io.reactors" %%% "reactors-core" % "0.8-SNAPSHOT")
```

Alternatively, you can download any of these dependencies manually,
and keep them in your folder for managed libraries.


### Maven

If you are using Maven, you can use the following dependency:

```
<dependency>
    <groupId>io.reactors</groupId>
    <artifactId>reactors_2.11</artifactId>
    <version>0.7</version>
</dependency>
```
!*/
class GuideSetup extends AsyncFunSuite {

  implicit override def executionContext = ExecutionContext.Implicits.global

}
