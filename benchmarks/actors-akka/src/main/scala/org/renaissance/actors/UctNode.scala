package org.renaissance.actors

/**
 * Unique identifier of a node in the pre-computed tree topology.
 * Defined as an opaque type to restrict its use as an integer, with
 * a `+` operation to produce offset identifiers.
 * Nodes are numbered contiguously starting from 0 (root).
 */
opaque private[actors] type NodeId = Int

private[actors] object NodeId {

  /** The root node of every topology. */
  val Root: NodeId = 0

  /** Turns an Int into a NodeId. */
  def apply(n: Int): NodeId = n

  extension (id: NodeId) {
    def toLong: Long = id.toLong
    def +(offset: Int): NodeId = id + offset
  }

  given ordering: Ordering[NodeId] = Ordering.Int
}

/**
 * Expansion of an interior node in the pre-computed tree.
 * Determines the IDs of its children.
 *
 * @param firstChildId node ID of the first child;
 *   children occupy firstChildId .. firstChildId+childCount-1
 */
private[actors] final case class Expansion(firstChildId: NodeId) {

  def childIds(childCount: Int): IndexedSeq[NodeId] =
    (0 until childCount).map(slot => firstChildId + slot)
}

/**
 * A leaf of the UCT. Leaf nodes have no structure beyond their node ID and depth
 * (see [[Topology]]), but they have a deterministic initial temperature derived
 * from the node ID. Leaf actors use it to initialize their temperature, and the
 * benchmark uses it to compute the expected temperatures at the root.
 */
private[actors] object LeafNode {

  /** Lower bound (inclusive) of the initial leaf temperatures. */
  private val InitialTemperatureMin: Double = 0.1

  /** Upper bound (exclusive) of the initial leaf temperatures. */
  val InitialTemperatureMax: Double = 0.9

  /** 2^64 divided by the golden ratio. Used to scatter the bits of a multiplicand. */
  inline private val FibonacciHashMultiplier = 0x9e3779b97f4a7c15L

  /**
   * Bit pattern of 1.0, in which the mantissa bits are all zero, the sign is zero,
   * and the 11 exponent bits contain 1023 (biased zero). Setting any mantissa bits
   * in this pattern produces values in the [1.0, 2.0) range.
   */
  private val DoubleOneBits: Long = java.lang.Double.doubleToRawLongBits(1.0)

  /**
   * Initial temperature of the given leaf, between [[InitialTemperatureMin]] (inclusive)
   * and [[InitialTemperatureMax]] (exclusive). Multiplies the leaf ID by a Fibonacci hash
   * constant (see Knuth, TAOCP Vol. 3, Sec. 6.4) to scatter the bits, then coerces the top
   * 52 bits into the mantissa of a double to get a value in [1.0, 2.0) range, and finally
   * subtracts 1.0 to shift the value to the [0.0, 1.0) range without division.
   */
  def initialTemperatureOf(leafId: NodeId): Double = {
    // The root (ID 0) is always interior, so no leaf gets the degenerate hash 0.
    val hash = leafId.toLong * FibonacciHashMultiplier
    val fraction = java.lang.Double.longBitsToDouble(DoubleOneBits | asMantissaBits(hash)) - 1.0

    val temperatureRange = InitialTemperatureMax - InitialTemperatureMin
    InitialTemperatureMin + fraction * temperatureRange
  }

  /**
   * Isolates the top 52 bits of the given value and shifts them so that they
   * overlap with the mantissa bits in a double.
   */
  inline private def asMantissaBits(bits: Long): Long = {
    // A double stores 52 mantissa bits, the 53rd bit of precision being a hidden
    // (leading) one. At the moment, we cannot use `Double.PRECISION` (Java 19+).
    inline val mantissaBitCount = 53 - 1

    bits >>> (java.lang.Long.SIZE - mantissaBitCount)
  }
}
