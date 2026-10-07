package org.renaissance.actors

object UctConfig {

  /** Upper bound on the number of nodes in the pre-computed tree. */
  val NodeCount: Int = 100_000

  /** Branching factor: each interior node has exactly this many children. */
  val BranchingFactor: Int = 10

  /** Number of urgent paths (leaves) to select for the shock reduction.
   * We set bigger number of urgent paths than running threads due
   * to a non-deterministic workload. With this approach we overload system and some
   * actors will not be active some time. The goal is that when non-active actor
   * wakes up, it sees 2 messages in its mailbox and dispatcher prioritize the urgent one.
   * With lower or same urgent paths as threads it is possible that it will see only 1 (non-urgent)
   *  message nad immediately starts to process it
   */
  val UrgentPathCount: Int = 2 * Runtime.getRuntime().availableProcessors()

  /** Minimum depth fraction [0, 1] a leaf must reach to be eligible for urgent path selection. */
  val UrgentLeafDepthFractionMin: Double = 0.9

  /**
   * Total number of temperature reductions per iteration.
   * Reductions 1 .. ReductionCount-1 are normal scatter-gather reductions.
   * Reduction reductionCount is the shock reduction: MeasureTemperature +
   * UrgentUpdateTemperature sent simultaneously.
   */
  val ReductionCount: Int = 3

  /**
   * Multiplier on [[TemperatureTolerance]] used to compute the per-topology shock temperature
   * (see [[AkkaUct.computeShockTemperature]]); must be >> 1 so the validation window
   * reliably distinguishes a successful shock from floating-point noise.
   */
  val ShockMarginMultiplier: Double = 1000.0

  /** Tolerance for temperature comparisons in result validation. */
  val TemperatureTolerance: Double = 1e-5

  /** Minimum required shift in root temperature from nominal to shocked. */
  val RootShockMargin: Double = TemperatureTolerance * ShockMarginMultiplier

  /** Seed for the tree topology. */
  val TopologySeed: Long = 2L

  /** Seed used to assign deterministic initial temperatures to leaf nodes. */
  val LeafTemperatureSeed: Long = 42L
}
