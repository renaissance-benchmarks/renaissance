/* scala-stm - (c) 2009-2011, Stanford University, PPL */

package scala.concurrent.stm
package ccstm

import java.util.concurrent.atomic.AtomicLong


private[ccstm] trait GV6 {

  /** The global timestamp.  We use TL2's GV6 scheme to avoid the need to
   *  increment this during every transactional commit.  Non-transactional
   *  writes are even more conservative, incrementing the global version only
   *  when it lags the local version by a (configurable) fixed amount.  This
   *  helps reduce contention (especially when there are many non-transactional
   *  writes), but it means we must always validate transactions that are not
   *  read-only.  To help reduce the spurious revalidations caused by GV6, we
   *  adaptively adjust the ratio of silent commits.  Spurious revalidations
   *  can also be triggered by silent non-txn run ahead, so we use bit 0 of the
   *  version to differentiate the type of the most recent write, 0 for non-txn
   *  and 1 for txn.
   */
  val globalVersion = new AtomicLong(1)

  private val silentCommitRatioMin = System.getProperty("ccstm.gv6.min", "1").toInt
  private val silentCommitRatioMax =
    System.getProperty("ccstm.gv6.max", (Runtime.getRuntime.availableProcessors min 16).toString).toInt

  /** The approximate ratio of the number of commits to the number of
   *  increments of `globalVersion`, as in TL2's GV6 scheme.  If
   *  greater than one, the actual choice to advance or not is made with a
   *  random number generator.
   */
  private var silentCommitRatio =
    (Runtime.getRuntime.availableProcessors / 2) max silentCommitRatioMin min silentCommitRatioMax

  private var silentCommitCutoff = intRangeFraction(silentCommitRatio)

  private val silentCommitRand = skel.SimpleRandom

  /** The maximum value of `nonTxnWriteVersion - globalVersion` that
   *  will be allowed before a non-transactional store attempts to increase
   *  `globalVersion`.  Any value larger than zero admits the
   *  possibility that a non-transactional write will leave a version number
   *  that forces revalidation of a transaction that discovers it (like a
   *  silently-committed txn under GV6).  Larger values can help amortize the
   *  cost of updating the counter.  This is double the "ccstm.nontxn.runahead"
   *  property because we reserve bit 0 to record the txn state of the last
   *  writer.
   */
  private val nonTxnSilentRunAhead = 2 * System.getProperty("ccstm.nontxn.runahead", "32").toInt

  /** If `x` is a signed integer evenly chosen from a uniform distribution
   *  between Integer.MIN_VALUE and Integer.MAX_VALUE, then the test
   *  `(x <= intRangeFraction(r))` will succeed `1.0 / r` of the time.
   */
  private def intRangeFraction(r: Int) = ((1 << 31) + ((1L << 32) / r) - 1).asInstanceOf[Int]

  /** Returns a value that is greater than `prevVersion` and greater
   *  than the value of `globalVersion` on entry.  May increase
   *  `globalVersion`.
   */
  def nonTxnWriteVersion(prevVersion: Long): Long = {
    val g = globalVersion.get
    val result = (math.max(g, prevVersion) + 2) & ~1L
    if (result > g + nonTxnSilentRunAhead) {
      globalVersion.compareAndSet(g, prevVersion + 1)
    }
    result
  }

  /** Returns a version to use for reading in a new transaction. */
  def freshReadVersion: Long = globalVersion.get

  /** Guarantees that `globalVersion.get` is &ge;
   *  `minRV`, and returns `globalVersion.get`.  This form of
   *  `freshReadVersion` is used when the read version of a transaction needs
   *  to be advanced by revalidating.
   */
  def freshReadVersion(minRV: Long): Long = {
    // A call to this method corresponds to an mid-txn revalidation, which is
    // relatively costly.  If minRV is odd then the revalidation is due to a
    // silent commit, so consider adjusting the silent commit ratio.  We only
    // do this 1/64 of the time, though.
    if ((minRV & 127) == 1) {
      reduceRevalidateProbability()
    }

    (while (true) {
      val g = globalVersion.get
      if (g >= minRV) {
        return g
      }
      if (globalVersion.compareAndSet(g, minRV)) {
        return minRV
      }
    }).asInstanceOf[Nothing]
  }

  /** Returns a value that is greater than `globalVersion.get` and greater than
   *  `readVersion`, possibly increasing `globalVersion`.
   */
  def freshCommitVersion(readVersion: Long): Long = {
    val cutoff = silentCommitCutoff
    val install = cutoff == Int.MaxValue || silentCommitRand.nextInt <= cutoff

    val gvSnap = globalVersion.get
    val result = (math.max(readVersion, gvSnap) + 1) | 1L

    // if we fail to install with a CAS, 1/128 prob of adjusting
    // silentCommitRatio
    if (install &&
        !globalVersion.compareAndSet(gvSnap, result) &&
        (result & 254) == 0)
      reduceContentionProbability()

    result
  }

  private def reduceRevalidateProbability() {
    // increment the commit version on more commits, so reduce the ratio
    val r = silentCommitRatio
    if (r > silentCommitRatioMin) {
      silentCommitRatio = r - 1
      silentCommitCutoff = intRangeFraction(r - 1)
      //System.err.println("reduced ratio to " + (r - 1))
    }
  }

  private def reduceContentionProbability() {
    // increment the commit version on fewer commits, so reduce the ratio
    val r = silentCommitRatio
    if (r < silentCommitRatioMax) {
      silentCommitRatio = r + 1
      silentCommitCutoff = intRangeFraction(r + 1)
      //System.err.println("increased ratio to " + (r + 1))
    }
  }
}
