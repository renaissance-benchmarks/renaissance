/* scala-stm - (c) 2009-2011, Stanford University, PPL */

package scala.concurrent.stm.skel


/** A random number generator that focuses on speed and lack of inter-thread
 *  interference, rather than on the quality of the numbers returned.  The
 *  `object SimpleRandom` is striped internally to reduce
 *  contention when accessed from multiple threads.  The `class
 *  SimpleRandom` should only be used by a single thread.
 *  <p>
 *  The constants in this 64-bit linear congruential random number generator
 *  are from http://nuclear.llnl.gov/CNP/rng/rngman/node4.html.
 *
 *  @author Nathan Bronson
 */
object SimpleRandom {
  // 64 byte cache lines are typical, so there are 8 slots per cache line.
  // This means that the probability that any two threads have false sharing is
  // p = 8 / #slots.  If there are n processors, each of which is running 1
  // thread, then the probability that no other threads have false sharing with
  // the current thread is (1-p)^(n-1).  If p is small, that is about
  // 1 - (n-1)p, which is pretty close to 1 - np.  If we want the probability
  // of false conflict for a thread to be less than k, then we need np < k, or
  // p < k/n, or 8/Slots < k/n, or #slots > 8n/k.  If we let k = 1/8, then we
  // get #slots=64*n.
  private val mask = {
    val min = 64 * Runtime.getRuntime.availableProcessors
    var slots = 1
    while (slots < min) slots *= 2
    slots - 1
  }
  
  private val states = Array.tabulate(mask + 1)({ _ * 0x123456789abcdefL })

  /** Returns a random value chosen from a uniform distribution of all valid
   *  `Int`s.
   */
  def nextInt(): Int = {
    val id = (Thread.currentThread.getId.asInstanceOf[Int] * 13) & mask

    val next = step(states(id))
    states(id) = next

    extract(next)
  }
  
  /** Returns a random value chosen from a uniform distribution of the
   *  non-negative integers less than `n`, or throws `IllegalArgumentException`
   *  if `n` is negative or zero.
   */
  def nextInt(n: Int): Int = {
    if (n <= 0)
      throw new IllegalArgumentException

    var x = -1
    while (x == -1) x = tryClamp(nextInt(), n)
    x
  }

  private def step(x: Long) = x * 2862933555777941757L + 3037000493L
  
  private def extract(x: Long) = (x >> 30).asInstanceOf[Int]

  /** r is the random, returns -1 on failure. */
  private def tryClamp(r: Int, n: Int): Int = {
    // get a positive number
    val x = r & Int.MaxValue

    if ((n & -n) == n) {
      // for powers of two, we use high bits instead of low bits
      ((x.toLong * n) >> 31).toInt
    } else {
      val z = x % n
      if (x - z + (n - 1) < 0) {
        // x is bigger than floor(MAX_INT/n)*n, so we are not getting an even
        // distribution.  Try again.
        -1
      } else {
        z
      }
    }
  }
}

/** An clonable unsynchronized random number generator that uses the same
 *  algorithm as the concurrent `object SimpleRandom`.  The caller must ensure
 *  that each `SimpleRandom` instance is used from only one thread at a time.
 *
 *  @author Nathan Bronson
 */
class SimpleRandom private (private var _state: Long, dummy: Boolean) {
  import SimpleRandom._

  def this(seed: Int) = this(SimpleRandom.step(SimpleRandom.step(seed)), false)
  def this() = this(System.identityHashCode(Thread.currentThread))

  override def clone = new SimpleRandom(_state, false)

  /** Returns a random value chosen from a uniform distribution of all valid
   *  `Int`s.
   */
  def nextInt(): Int = {
    _state = step(_state)
    extract(_state)
  }

  /** Returns a random value chosen from a uniform distribution of the
   *  non-negative integers less than `n`, or throws `IllegalArgumentException`
   *  if `n` is negative or zero.
   */
  def nextInt(n: Int): Int = {
    if (n <= 0)
      throw new IllegalArgumentException

    var x = -1
    while (x == -1) x = tryClamp(nextInt(), n)
    x
  }
}
