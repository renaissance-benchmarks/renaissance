package org.renaissance.harness

import java.nio.file.{Path, Paths}
import scala.collection.mutable

private final class Config {

  val benchmarkSpecifiers = mutable.ArrayBuffer[String]()

  var policyType = PolicyType.FIXED_OP_COUNT
  var repetitions: Option[Int] = Option.empty
  var runSeconds = 240

  val pluginsWithArgs = mutable.LinkedHashMap[String, mutable.ArrayBuffer[String]]()

  // External policy specifier. Valid only when policyType is EXTERNAL
  var policyPlugin: String = _

  // Holds the current buffer into which policy/plugin arguments are appended.
  // Switched when a --policy or --plugin option occurs on the command line.
  var extraArgs = mutable.ArrayBuffer[String]()

  var csvOutput: Option[String] = Option.empty
  var jsonOutput: Option[String] = Option.empty

  var printList = false
  var printRawList = false
  var printGroupList = false

  var configuration = "default"

  /**
   * Force garbage collection before executing the measured operation. This is
   * enabled by default to avoid accumulating garbage between operations which
   * can then trigger GC during operation.
   */
  var forceGc = true

  /**
   * Check the JVM specification version requirements in the benchmarks
   * selected for execution. This is enabled by default to avoid running
   * benchmarks on an incompatible/unsupported JVM. Can be disabled for
   * testing purposes.
   */
  var checkJvm = true

  /**
   * The directory to use for scratch files. Uses current directory by default
   * to avoid storing data to (potentially tmpfs-backed temporary directory),
   * which could create artificial memory pressure.
   */
  var scratchBase: Path = Paths.get("")

  /**
   * Do not delete the contents of the scratch directory after the VM exits.
   * This is useful for debugging and is disabled by default.
   */
  var keepScratch = false

  def withBenchmarkSpecification(v: String) = {
    benchmarkSpecifiers ++= v.split(",").map(_.trim)
    this
  }

  def withPlugin(specifier: String) = {
    extraArgs = mutable.ArrayBuffer()
    pluginsWithArgs += (specifier -> extraArgs)
    this
  }

  def withPolicy(specifier: String) = {
    policyType = PolicyType.EXTERNAL
    policyPlugin = specifier
    withPlugin(specifier)
  }

  def withExtraArg(arg: String) = {
    this.extraArgs += arg
    this
  }

  def withRepetitions(count: Int) = {
    policyType = PolicyType.FIXED_OP_COUNT
    repetitions = Option(count)
    this
  }

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

  def withCsvOutput(outputFile: String) = {
    csvOutput = Option(outputFile)
    this
  }

  def withJsonOutput(outputFile: String) = {
    jsonOutput = Option(outputFile)
    this
  }

  def withList = {
    printList = true
    this
  }

  def withRawList = {
    printRawList = true
    this
  }

  def withGroupList = {
    printGroupList = true
    this
  }

  def withConfiguration(name: String) = {
    configuration = name
    this
  }

  def withoutForcedGc() = {
    forceGc = false
    this
  }

  def withoutJvmCheck() = {
    checkJvm = false
    this
  }

  def withScratchBase(name: String) = {
    scratchBase = Paths.get(name)
    this
  }

  def withKeepScratch() = {
    keepScratch = true
    this
  }

}

private object PolicyType extends Enumeration {
  type PolicyType = Value
  val FIXED_OP_COUNT, FIXED_OP_TIME, FIXED_TIME, EXTERNAL = Value
}
