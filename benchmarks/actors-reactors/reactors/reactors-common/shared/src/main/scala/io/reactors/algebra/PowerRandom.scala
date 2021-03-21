package io.reactors
package algebra



import scala.util.Random



class PowerRandom(private val jucRandom: java.util.Random) {
  self =>

  private val rand = new Random(jucRandom)

  def this(seed: Long) = this(new java.util.Random(seed))

  def boolean() = rand.nextBoolean()

  def int() = rand.nextInt()

  def int(n: Int) = rand.nextInt(n)

  def float() = rand.nextFloat()

  def long() = rand.nextLong()

  def long(n: Int) = math.abs(rand.nextLong()) % n

  def double() = rand.nextDouble()

  def string(length: Int) = rand.nextString(length)

}


