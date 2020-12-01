package org.renaissance.harness

import scopt.OptionParser

private final class ConfigParser(tags: Map[String, String]) {

  private val parser = createParser(tags)

  private def createParser(tags: Map[String, String]) = {
    new OptionParser[Config]("renaissance") {
      head(s"${tags("renaissanceTitle")}, version ${tags("renaissanceVersion")}")

      help('h', "help")
        .text("Prints this usage text.")

      opt[Int]('r', "repetitions")
        .valueName("<count>")
        .text("Execute the measured operation a fixed number of times.")
        .validate(v => if (v > 0) success else failure("<count> must be greater than 0"))
        .action((v, c) => c.withRepetitions(v))
        .maxOccurs(1)

      opt[Int]('t', "run-seconds")
        .valueName("<seconds>")
        .text("Execute the measured operation for fixed time (wall-clock).")
        .validate(v => if (v > 0) success else failure("<seconds> must be greater than 0"))
        .action((v, c) => c.withRunSeconds(v))
        .maxOccurs(1)

      opt[Int]("operation-run-seconds")
        .valueName("<seconds>")
        .text(
          "Execute the measured operation for fixed accumulated operation time (wall-clock)."
        )
        .validate(v => if (v > 0) success else failure("<seconds> must be greater than 0"))
        .action((v, c) => c.withOperationRunSeconds(v))
        .maxOccurs(1)

      opt[String]("policy")
        .valueName("<class-path>!<class-name>")
        .text(
          "Use policy plugin to control repetition of measured operation execution."
        )
        .validate(v =>
          if (v.count(_ == '!') == 1) success
          else failure("expected <class-path>!<class-name> in external policy specification")
        )
        .action((v, c) => c.withPolicy(v))
        .maxOccurs(1)

      opt[String]("plugin")
        .valueName("<class-path>!<class-name>")
        .text(
          "Load external plugin. Can appear multiple times."
        )
        .action((v, c) => c.withPlugin(v))
        .validate(v =>
          if (v.count(_ == '!') == 1) success
          else failure("expected <class-path>!<class-name> in external plugin specification")
        )
        .unbounded()

      opt[String]("with-arg")
        .text(
          "Adds an argument to the plugin or policy specified last. Can appear multiple times."
        )
        .action((v, c) => c.withExtraArg(v))
        .unbounded()

      opt[String]("csv")
        .valueName("<file-path>")
        .text("Output results to CSV file.")
        .action((v, c) => c.withCsvOutput(v))
        .maxOccurs(1)

      opt[String]("json")
        .valueName("<file-path>")
        .text("Output results to JSON file.")
        .action((v, c) => c.withJsonOutput(v))
        .maxOccurs(1)

      opt[String]('c', "configuration")
        .valueName("<name>")
        .text("Run benchmarks with given named configuration.")
        .action((v, c) => c.withConfiguration(v))
        .maxOccurs(1)

      opt[Unit]("no-forced-gc")
        .text("Do not force garbage collection before each measured operation.")
        .action((_, c) => c.withoutForcedGc())

      opt[Unit]("list")
        .text("Print list of benchmarks with their description.")
        .action((_, c) => c.withList)

      opt[Unit]("raw-list")
        .text("Print list of benchmarks (each benchmark name on separate line).")
        .action((_, c) => c.withRawList)

      opt[Unit]("group-list")
        .text("Print list of benchmark groups (each group name on separate line).")
        .action((_, c) => c.withGroupList)

      arg[String]("benchmark-specification")
        .text("Comma-separated list of benchmarks (or groups) that must be executed (or all).")
        .action((v, c) => c.withBenchmarkSpecification(v))
        .unbounded()
        .optional()
    }
  }

  def parse(args: Array[String]): Option[Config] = parser.parse(args, new Config)

  def usage(): String = parser.usage

}
