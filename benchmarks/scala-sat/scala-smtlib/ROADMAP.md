Road Map
========

A list of features potentially useful to add.

* Type checking of the input script: Make sure the logic declaration corresponds to the syntax of the formulas,
  check correct syntax of terms and proper declaration of all uninterpreted symbols used.
* Explore asynchrous IO: Doesn't seem to make sense with a tree sturcture, and script are short in practice.
* Modularize the background theory definitions as an abstract component that could be extended by third party
  code. Should only provide the Core theory and the basic theories defined by SMT-LIB standard.
* Explore possible usage of string interpolation to build smtlib scripts
