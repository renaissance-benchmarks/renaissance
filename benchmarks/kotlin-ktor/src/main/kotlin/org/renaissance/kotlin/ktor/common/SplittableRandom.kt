package org.renaissance.kotlin.ktor.common

import kotlin.random.Random

/**
 * A [Random] that can [split] off an independent, well-separated child
 * generator without consuming values from this one. Backed by
 * [SplittableRandom] instead of the newer `java.util.random.RandomGenerator`
 * hierarchy to maintain compatibility with JDK 11.
 */
class SplittableRandom private constructor(private val random: java.util.SplittableRandom) : Random() {
  constructor(seed: Long) : this(java.util.SplittableRandom(seed))

  fun split(): SplittableRandom = SplittableRandom(random.split())

  /**
   * Random's every other method is implemented in terms of this one,
   * so nothing else needs overriding.
   */
  override fun nextBits(bitCount: Int): Int =
    random.nextInt().ushr(32 - bitCount) and (-bitCount).shr(31)
}
