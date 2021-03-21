CI service | Status | Description
-----------|--------|------------
Travis | [![Build Status](https://travis-ci.org/reactors-io/reactors.png?branch=master)](https://travis-ci.org/reactors-io/reactors) | Linux container tests
Maven | [![Maven Artifact](https://img.shields.io/maven-central/v/io.reactors/reactors_2.11.svg)](http://mvnrepository.com/artifact/io.reactors/reactors_2.11/0.7) | Artifact on Maven

<img src='reactress-title-96.png'></img>

[Reactors.IO](http://reactors.io) is a concurrent, distributed programming framework based
on asynchronous event streams.

- [documentation](http://reactors.io/learn/)
- [FAQ](http://reactors.io/faq/)
- [download page](http://reactors.io/download/)


# Usage

Add the following line to your SBT project definition:

```
libraryDependencies ++= Seq("io.reactors" %% "reactors" % "0.8")
```

Then, import the `io.reactors` package in your project:

```
import io.reactors._
```

Alternatively, you can download the artifact from
[Maven](https://repo1.maven.org/maven2/com/storm-enroute/reactors-core_2.11/).
To learn how to write reactor-based programs,
please read the [tutorial](http://reactors.io/tutorialdocs/reactors/).


# Contributing

You will need to install [SBT](http://www.scala-sbt.org) build tool on your system.
Once you do that, go to your project folder, and run:

```
$ sbt
```

Within the `sbt` shell, you can compile the code:

```
> compile
```

You can start continuous compilation whenever your code changes:

```
> ~compile
```

After making changes, submit a pull request to the
[reactors repo at GitHub](https://github.com/reactors-io/reactors).
Tests will be run automatically, and your contribution will be reviewed.
If you want to run tests locally, run `test` or `testOnly <name-of-test>`
in the SBT shell.


# Discussion

Room on Gitter chat: [![Join the chat at https://gitter.im/reactors-io/reactors](https://badges.gitter.im/reactors-io/reactors.svg)](https://gitter.im/reactors-io/reactors?utm_source=badge&utm_medium=badge&utm_campaign=pr-badge&utm_content=badge)

Mailing list: [Google Groups](https://groups.google.com/forum/#!forum/reactors-io)

Twitter: [Reactors.IO](https://twitter.com/reactors_io)
