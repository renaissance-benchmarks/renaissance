Scala SMT-LIB
=============

Scala SMT-LIB is a lightweight abstraction over the
[SMT-LIB](http://www.smtlib.org/) standard.  It enables you to use a typesafe
API in Scala to build SMT-LIB 2.0 scripts and execute them via any solver that
supports the SMT-LIB standard.

Scala SMT-LIB provides the tools for parsing and printing the SMT-LIB syntax.
It can help you if you need to communicate with a native SMT process via its
text interface. You can also write a Scala wrapper around an SMT solver and use
it from a friendlier API. You could even get crazier and use a [pure Scala SMT
solver](https://github.com/regb/scabolic) that happens to implement the SMT-LIB
api.

The library is still in development and is evolving along with the needs of the
projects using it.

Motivation
----------

Scala SMT-LIB deals with the messy details of parsing and writing SMT-LIB. It
provides a programmer friendly interface to simplify the development of tools
that rely on SMT-LIB.

You may want to use Scala SMT-LIB if:
* You plan to write a tool that will take as input some SMT-LIB files, but do
  not wish to spend too much time figuring out the SMT-LIB standard. Then you can
  plug-in the parser component of Scala SMT-LIB in your tool and only deal with
  the Scala representation of the few SMT-LIB commands of your interest.
* You need to output a complex SMT-LIB encoding of some mathematical problems. We got
  you covered: You can programatically build a set of expressions using the
  Scala SMT-LIB abstract syntax tree, and use the printer components to get
  a valid SMT-LIB representation.
* You need to query an external black-box SMT solver, but the task of setting up a proper
  communication with this strange beast seems a bit too daunting? Scala SMT-LIB offers
  an interpreter module that abstracts SMT-Solvers as interpreters for a sequence of
  SMT-LIB commands. You can program your tool against this simple high-level API. Scala SMT-LIB
  provides integration with Z3 and CVC4 out of the box, and you can add any other solver
  by implementation a relatively thin interface.
   

Setup
-----

The project is built with sbt. To build the library, just type:

    sbt package

It will produce a jar that you can add to the classpath of your own project.

If you are building your project using sbt, it is possible to setup a reference
to this github repository in the build system to automatically get the most
recent build. If you are interested in this route, you should check the sbt
official documentation.

Examples
--------

The parser can be constructed with a java.io.Reader, you could for example do
the following:

    val is = new java.io.FileReader(inputFile)
    val parser = new smtlib.Parser(is)

The parser implements the `Iterator[Command]` and can thus be used in any
interface that expects a `TraversableOnce` element. In particular, assuming an
implicit solver that implements the Interpreter interface is in scope, you can
do the following:

    import smtlib.Commands.Script
    smtlib.Interpreter(Script(parser))

API
---

Please refer to the code ;) However, you could start with the Examples section
above.

Development
-----------

The project is still evolving and the API will likely go through quite a few
changes. It was originally part of [CafeSat](https://github.com/regb/scabolic)
and has been made standalone in order for the
[Leon](https://github.com/epfl-lara/leon) project to rely on it as well.
Hopefully, it can be useful to other people as well.

Road Map
--------

A list of potential features to be added.

* Type checking of the input script: Make sure the logic declaration corresponds to the syntax of the formulas,
  check correct syntax of terms and proper declaration of all uninterpreted symbols used.
* Expore asynchrous IO: Doesn't seem to make sense with a tree sturcture, and script are short in practice.
* Modularize the background theory definitions as an abstract component that could be extended by third party
  code. Should only provide the Core theory and the basic theories defined by SMT-LIB standard.
