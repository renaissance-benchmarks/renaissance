package org.renaissance.scala.dotty;

import dotty.tools.dotc.interfaces.CompilerCallback;
import dotty.tools.dotc.interfaces.ReporterResult;
import dotty.tools.dotc.interfaces.SimpleReporter;

/**
 * Provides a bridge method to call the {@link dotty.tools.dotc.Main} object, which
 * Scala (starting with version 2.12.9) fails to find in {@code dotty-compiler_*.jar}.
 * <p>
 * According to Dale Wijnand (@dwijnand), the contents of the JAR are compiled using Dotty,
 * so {@code scalac} 2.12.9 is not expected to be able to link to it. The fact that it works
 * on 2.12.8 appears to be pure luck. The next 2.13.x version (after 2.13.3) should be able
 * to compile code that links to the dotty-compiler library like that due to it having a dotty
 * tasty (typed AST) reader.
 * <p>
 * He also mentioned that Dotty uses Scala 2.13's standard library (scala.Option,
 * scala.collection.immutable.List, etc), therefore Scala 2.12 code should not (be able to?)
 * execute alongside Scala 2.13 or Dotty code (i.e. using the same classpath/classloader).
 */
final class JavaDotty {
  static ReporterResult process(String[] args) {
    return dotty.tools.dotc.Main.process(
      // Cast to disambiguate between several process() methods.
      args, (SimpleReporter) null, (CompilerCallback) null
    );
  }
}
