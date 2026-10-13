package org.renaissance.actors

import org.renaissance.BenchmarkContext

/**
 * Benchmark parameters for the [[AkkaUct]] benchmark. Created from
 * [[BenchmarkContext]] using [[UctConfig.fromContext]].
 */
private[actors] final class UctConfig private (
  _nodeCountMax: Int,
  _branchingFactor: Int,
  _topologySeed: Int,
  _urgentPathLengthFractionMin: Double,
  _topologyCount: Int,
  _temperatureTolerance: Double
) {

  /**
   * Upper bound on number of nodes in the unbalanced tree. The generated tree may
   * be smaller depending on random expansion choices.
   */
  val nodeCountMax: Int = _nodeCountMax

  /**
   * Fan-out of the interior nodes. Also governs the scaling of the shock temperature
   * (a leaf at depth `d` contributes `1/branchingFactor^d` to the root average).
   */
  val branchingFactor: Int = _branchingFactor

  /**
   * Base seed for topology generation. Topology `i` is built with seed [[topologySeed]] + `i`
   * to obtain distinct but reproducible topologies across repetitions.
   */
  val topologySeed: Int = _topologySeed

  /** Number of root-to-leaf paths tagged for urgent update. */
  val urgentPathCount: Int = 10

  /**
   * Minimum eligible path length as a fraction of the tree height. Keeps urgent
   * paths long enough so that the urgent temperature update messages pass through
   * multiple actor mailboxes on their way to the urgent leaves.
   */
  val urgentPathLengthFractionMin: Double = _urgentPathLengthFractionMin

  /** Number of (distinct) topologies to run the benchmark on. */
  val topologyCount: Int = _topologyCount

  /**
   * Acceptable floating-point deviation in temperature comparisons during validation.
   */
  val temperatureTolerance: Double = _temperatureTolerance

  /** Minimum required shift in root temperature from nominal to shocked. */
  val rootShockMargin: Double = temperatureTolerance * UctConfig.ShockMarginMultiplier
}

private[actors] object UctConfig {

  /**
   * Scales the temperature tolerance to compute the root shock margin; must be >> 1
   * so the validation window reliably distinguishes a successful shock from
   * floating-point noise.
   */
  val ShockMarginMultiplier: Double = 1000.0

  /**
   * Total number of temperature reductions per iteration.
   * Reductions 1 .. ReductionCount-1 are normal scatter-gather reductions.
   * Reduction reductionCount is the shock reduction: MeasureTemperature +
   * UrgentUpdateTemperature sent simultaneously.
   */
  val ReductionCount: Int = 3

  /** Creates a [[UctConfig]] by reading all parameters from the given context. */
  def fromContext(c: BenchmarkContext): UctConfig =
    new UctConfig(
      _nodeCountMax = c.parameter("node_count_max").toPositiveInteger,
      _branchingFactor = c.parameter("branching_factor").toPositiveInteger,
      _topologyCount = c.parameter("topology_count").toPositiveInteger,
      _urgentPathLengthFractionMin = c.parameter("urgent_path_length_fraction_min").toDouble,
      _topologySeed = c.parameter("topology_seed").toInteger,
      _temperatureTolerance = c.parameter("temperature_tolerance").toDouble
    )
}
