Changelog
=========


Current
-------

* TIP extensions
* Tree Transformers API
* Cross compilation and deployment to Maven Sonatype
* Add standard theory of floating points
* DSL wrapper
* Bug fixes
  * Remove erroneous symbol characters
  * Positions always maintained


v0.2
-----------------------
*Released 9 March 2016*

* Constructors and extractors for the standard theories (except Floating point) of SMT-LIB 2.5
  * Experimental support for non-standardized theories such as Strings and Sets.
* More robust parser and printers.
* Bug fixes, mostly small edge cases and weird symbol names.


v0.1
-----------------------
*Released 2 April 2015*

Initial version of Scala SmtLib.

* Extensive support for the SMT-LIB language version 2.5
* SMT-LIB expressions represented with a Scala AST
  * Parser turn input stream into AST representation
  * Printer turn AST representation into an SMT-LIB complient string output
* abstraction layer to communicate with solver processes over their textual input 
  * Support for Z3 and CVC4
* Scala SMT-LIB is released under the terms of the MIT license.

