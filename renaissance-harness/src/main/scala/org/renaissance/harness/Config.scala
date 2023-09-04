package org.renaissance.harness

import java.io.File
import java.net.URI
import java.nio.file.Path
import java.nio.file.Paths
import java.util.Optional
import scala.collection.mutable

private final class Config {

  /**
   * A collection of benchmark specifiers which select the benchmarks
   * to be run. A specifier is either a benchmark name or a group name.
   */
  val benchmarkSpecifiers = mutable.ArrayBuffer[String]()

  def withBenchmarkSpecification(v: String) = {
    benchmarkSpecifiers ++= v.split(",").map(_.trim)
    this
  }

  /**
   * A buffer which holds the arguments for the policy/plugin currently
   * being configured. A new instance is created whenever a --policy or
   * --plugin option appears on the command line.
   */
  private var extraArgs = mutable.ArrayBuffer[String]()

  def withExtraArg(arg: String) = {
    this.extraArgs += arg
    this
  }

  /**
   * An ordered collection associating plugin specifiers with plugin arguments.
   * The harness will load the plugins in the order given on the command line.
   *
   * After parsing the command line, this collection may contain different plugin
   * specifiers that ultimately represent the same plugin. The harness attempts to
   * avoid creating multiple instances of the same plugin later on.
   */
  private val pluginArgs = mutable.LinkedHashMap[PluginSpecifier, mutable.Buffer[String]]()

  /**
   * Provides an ordered immutable sequence of plugin specifiers
   * along with their arguments.
   */
  def pluginsWithArgs: Seq[(PluginSpecifier, Seq[String])] = {
    pluginArgs.iterator.map(kv => (kv._1, kv._2.toSeq)).toSeq
  }

  def withPlugin(specifier: String): Config = {
    withPlugin(PluginSpecifier(specifier))
  }

  def withPlugin(specifier: PluginSpecifier): Config = {
    if (pluginArgs.contains(specifier)) {
      Console.err.println(s"error: duplicate plugin specifier: $specifier")
      sys.exit(1)
    }

    extraArgs = mutable.ArrayBuffer()
    pluginArgs += (specifier -> extraArgs)
    this
  }

  /**
   * Holds the type of the benchmark repetition policy.
   */
  var policyType = PolicyType.FIXED_OP_COUNT

  /**
   * Number of times to repeat the measured operation.
   */
  var repetitions: Option[Int] = Option.empty

  def withRepetitions(count: Int) = {
    policyType = PolicyType.FIXED_OP_COUNT
    repetitions = Option(count)
    this
  }

  /**
   * Number of seconds to run the benchmark for.
   */
  var runSeconds = 240

  def withRunSeconds(seconds: Int) = {
    policyType = PolicyType.FIXED_TIME
    runSeconds = seconds
    this
  }

  def withOperationRunSeconds(seconds: Int) = {
    policyType = PolicyType.FIXED_OP_TIME
    runSeconds = seconds
    this
  }

  /**
   * External policy specifier. Valid only when policyType is EXTERNAL.
   */
  var policyPlugin: PluginSpecifier = _

  def withPolicy(specifier: String) = {
    policyType = PolicyType.EXTERNAL
    policyPlugin = PluginSpecifier(specifier)
    withPlugin(specifier)
  }

  /**
   * Name of the file to use for CSV output.
   */
  var csvOutput: Option[Path] = None

  def withCsvOutput(outputFile: String) = {
    csvOutput = Some(Paths.get(outputFile))
    this
  }

  /**
   * Name of the file to use for JSON output.
   */
  var jsonOutput: Option[Path] = None

  def withJsonOutput(outputFile: String) = {
    jsonOutput = Some(Paths.get(outputFile))
    this
  }

  /**
   * A flag which tells the harness to only print a list of all
   * benchmarks in a human-readable form.
   */
  var printList = false

  def withList() = {
    printList = true
    this
  }

  /**
   * A flag which tells the harness to only print a list of all
   * benchmark names, which is suitable for scripts.
   */
  var printRawList = false

  def withRawList() = {
    printRawList = true
    this
  }

  /**
   * A flag which tells the harness to only print a list of all
   * benchmark group names, which is suitable for scripts.
   */
  var printGroupList = false

  def withGroupList() = {
    printGroupList = true
    this
  }

  /**
   * The name of the benchmark configuration to use. Different configurations
   * represent different settings of benchmark parameters.
   */
  var configuration = "default"

  def withConfiguration(name: String) = {
    configuration = name
    this
  }

  /**
   * A collection of configuration parameter overrides.
   */
  val parameterOverrides = mutable.Map[String, String]()

  def withParameterOverride(specifier: String) = {
    val parts = specifier.split("=", 2).map(_.trim)
    parameterOverrides += (parts(0) -> parts(1))
    this
  }

  /**
   * Force garbage collection before executing the measured operation. This is
   * enabled by default to avoid accumulating garbage between operations which
   * can then trigger GC during operation.
   */
  var forceGc = true

  def withoutForcedGc() = {
    forceGc = false
    this
  }

  /**
   * Check the JVM specification version requirements in the benchmarks
   * selected for execution. This is enabled by default to avoid running
   * benchmarks on an incompatible/unsupported JVM. Can be disabled for
   * testing purposes.
   */
  var checkJvm = true

  def withoutJvmCheck() = {
    checkJvm = false
    this
  }

  /**
   * Determines whether to use a separate class loader for each benchmark
   * module. Defaults to 'true' to ensure separation of benchmarks from
   * the harness and from each other.
   *
   * If set to 'false', the harness will load everything using a single
   * (default) classloader. This is useful for running single benchmarks
   * without the main bundle in environments that do not support multiple
   * classloaders, such as the Native Image.
   */
  var useModules = true

  def withStandalone() = {
    useModules = false
    this
  }

  /**
   * The directory to use for scratch files. Uses current directory by default
   * to avoid storing data to (potentially tmpfs-backed temporary directory),
   * which could create artificial memory pressure.
   */
  var scratchBase: Path = Paths.get("")

  def withScratchBase(name: String) = {
    scratchBase = Paths.get(name)
    this
  }

  /**
   * Do not delete the contents of the scratch directory after the VM exits.
   * This is useful for debugging and is disabled by default.
   */
  var keepScratch = false

  def withKeepScratch() = {
    keepScratch = true
    this
  }

  /**
   * URI that overrides the default location of the file with benchmark
   * metadata. If empty, the benchmark suite will use the default location.
   * We use the Java [[Optional]] type, because we pass the value to Java.
   */
  var benchmarkMetadataOverrideUri: Optional[URI] = Optional.empty()

  def withBenchmarkMetadata(uri: URI) = {
    benchmarkMetadataOverrideUri = Optional.of(uri)
    this
  }

}

private object PolicyType extends Enumeration {
  type PolicyType = Value
  val FIXED_OP_COUNT, FIXED_OP_TIME, FIXED_TIME, EXTERNAL = Value
}

/**
 * An external plugin specifier. It only captures where to find
 * the plugin code and (optionally) which class to instantiate.
 */
private final case class PluginSpecifier(paths: Seq[String], className: Option[String]) {

  override def toString: String = {
    val ps = paths.mkString(File.pathSeparator)
    className.map(cn => s"$ps!$cn").getOrElse(ps)
  }

}

private object PluginSpecifier {

  def apply(specifier: String): PluginSpecifier = {
    val splitIndex = specifier.lastIndexOf("!")
    val className = if (splitIndex < 0) None else Some(specifier.substring(splitIndex + 1))
    val codePaths = if (splitIndex < 0) specifier else specifier.substring(0, splitIndex)
    PluginSpecifier(codePaths.split(File.pathSeparator).toSeq, className)
  }

}
