CafeSat
=======

<p align="center">
  <img height="300px" src="/logo/cafesat2.jpg" />
</p>

This is the official repository for the CafeSat source code. CafeSat is a
SAT/SMT solver written entirely in Scala. CafeSat attempts provides an
efficient command-line tool to solve SMT problems, as well as a library
for Scala programs that need the capabilities of SAT/SMT solvers.

Getting Started
---------------

CafeSat is built with `sbt`.

A jar file that can be integrated to another project can be generated with:

    sbt package

If you wish to run CafeSat as a standalone tool, the jar file can be executed
using the JVM.  You need to invoke the `cafesat.Main` class.

The prefered way to use CafeSat as a standalone tool is to generate a runner
script:

    sbt cafesat

Then you can run CafeSat as follows:

    ./target/cafesat [ OPTIONS ] [ INPUT ]

To test that the build went fine, you can, for example, try to solve a
Dimacs SAT instances:

    ./target/cafesat --dimacs input.cnf

<!--
To start an interactive session in the REPL with SMT-LIB:

    ./target/cafesat

To execute an SMT-LIB script you can do the following:

    ./target/cafesat < input.smt2

which simply transparently redirect stdin to the content of the file. Or use:

    ./target/cafesat input.smt2

in which CafeSat will open the file before feeding it to the SMT solver.
-->


Overview
--------

CafeSat is a SAT and SMT solver written entirely in Scala. Its principal aim is
to provide a set of safe and well-understood logic solvers useable from a high
level programming language such as Scala. The typical approach used in tools
needing automated reasoning is to rely on an exeternal executable (usually
implemented from C/C++). This has the drawback of needing some external
dependencies, and also having part of the computation living outside of the
JVM. Some solvers provide an API, which can enable finer integration between
the tool and the solvers, but does not solve the issue of having dependencies
to native code.

With CafeSat, your Scala/Java application can live entirely in the JVM while
still using a powerful and efficient solving procedure. What you get is then
less overhead for not needing native bindings from the JVM to the system, and a
much safer control of the processes, by opposition to a native code that could
generate segmentation fault and crash in a non-recoverable state.

There are several sorts of theorem provers available. The advantage with SMT
solvers is that they are very predictable, compared to most other families of
provers. They have a well defined input theories, and pack specialized
procedure to solve problems in those theories. Unless specified otherwise, the
problem they are solving is decidable. The only unpredictable part is that the
general problem is NP-complete, which means that it could run for a very long
time on some instances. But the general design of an SMT solver is such that it
is exteremely efficient on any valid input, and so, in my opinion, works much
better when integrated in a bigger workflow, than say a general theorem prover
that relies on inference rules.

Documentation
-------------

CafeSat has been designed to be used in two distinct ways. The first one is the
classical command-line interface, which could be used manually to play with
some formulas, or as part of some scripting tasks. The second one is as part of
a bigger Scala application, with an API. With the API you get direct access to
some low level implementation part of the solver, which gives you the
possibility to customize it to your needs. The solver will also live in the
same JVM as your main application, and so you will get very precise control.


### Command Line

The basic template for using CafeSat as a command line is:

    cafesat [ OPTIONS ] [ INPUT ]

`OPTIONS` can actually be interleaved with the `INPUT` and the exact ordering
does not matter.

`INPUT` is a filename and is facultative, if none is provided, then CafeSat
will read from the standard input. In some sense, providing `INPUT` is just a
convenient shortcut, as an equivalent behaviour could be obtained with input
redirection:

    cafesat [ OPTIONS ] < cat INPUT

By default, CafeSat expects the input to be a problem in SMT-LIB 2.5, but this
behaviour can be overriden with the `--dimacs` option for reading SAT problem
in DIMACS format. CafeSat will output results to the standard output, the result
depending on the input problem, but usually would be a single textual output such
as `sat` or `unsat`. Logging will by default go to the standard error, so one
can filter any logging information using a pipe redirection as well. The default
logging level is warning, and usually should be quite silent. Logging level
can be specified using the option `--loglevel=[1-5]`. In general, if combining
CafeSat into a pipeline of tools, it is possible to parse the problem results
by ignoring the standard error (where logging goes) and only considering the
content of the standard output (where solving result) goes. Solving result
format is well defined for SMT-LIB script, so it is possible to build
a stable pipeline.

### Scala API

CafeSat exports an API usable from Scala programs. The API is not stable
yet and is expected to change frequently. It will NOT be backward compatible.

A minimal Scala doc is available [here](http://regb.github.io/cafesat/apidocs/#cafesat.api.package).

The best way to learn the API is probably to look at some projects relying on CafeSat:

  * [Cafedoku](https://github.com/regb/cafedoku)

Be sure to check which version of the library is used on each project.


Literature
----------

CafeSat has been first presented in the [Scala'13 workshop](http://dx.doi.org/10.1145/2489837.2489839).
However, note that the content of the paper is starting to get out of date.

Licence
-------

CafeSat is distributed under the terms of The MIT License.

All source code in this repository is distributed under this license. The
reference text is in the file LICENSE, no copy of the text shall be included in
any of the source file, but it is implicitly assumed they are available under
the terms specified in LICENSE.

BY COMMITTING TO THIS REPOSITORY, YOU ACCEPT TO RELEASE YOUR CODE UNDER
THE TERMS OF THE MIT LICENSE AS DESCRIBED IN THE LICENSE FILE.

Copyright
---------

The copyright for each portion of code is owned by the respective committer,
based on the git history. There is no per file or per function copyright as
this does not make sense in general. Sorry to be picky, but that's copyright
law for you. More information can be found in the COPYRIGHT.md file. Each
copyright owner implicitly distributes all code in this repository under the
MIT License.
