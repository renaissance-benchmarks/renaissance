/* scala-stm - (c) 2009-2011, Stanford University, PPL */

package scala.concurrent.stm
package ccstm


import java.util.concurrent.atomic.AtomicReferenceArray


private case class SlotLock(txn: AnyRef, refCount: Int)

/** This class manages a mapping from active transaction to a bounded integral
 *  range, so that transaction identities to be packed into some of the bits of
 *  an integral value.
 *
 *  @author Nathan Bronson
 */
private[ccstm] final class TxnSlotManager[T <: AnyRef](range: Int, reservedSlots: Int) {

  assert(range >= 16 & (range & (range - 1)) == 0)
  assert(range >= reservedSlots + 16)

  private def nextSlot(tries: Int) = {
    ((skel.SimpleRandom.nextInt << 4) | ((-tries >> 1) & 0xf)) & (range - 1)
  }

  /** CAS on the entries manages the actual acquisition.  Entries are either
   *  transactions, or SlotLock objects.
   */
  private val slots = new AtomicReferenceArray[AnyRef](range)

  @throws(classOf[InterruptedException])
  def assign(txn: T, slotHint: Int): Int = {
    // We advance to the next slot number after the hint, wrapping around in a
    // 64 byte space.  This avoids rollback from late steals, but keeps us in
    // a cache line we already own.
    var s = ((slotHint & ~0xf) | ((slotHint + 1) & 0xf)) & (range - 1)

    var tries = 0
    while (s < reservedSlots || slots.get(s) != null || !slots.compareAndSet(s, null, txn)) {
      s = nextSlot(tries)
      tries += 1
      if (tries > 100) {
        if (Thread.interrupted)
          throw new InterruptedException
        Thread.`yield`
      }
    }
    s
  }

  /** Returns the slot associated with `slot` at some instant.  The
   *  returned value may be obsolete before this method returns.
   */
  def lookup(slot:Int): T = unwrap(slots.get(slot))

  private def unwrap(e: AnyRef): T = {
    e match {
      case SlotLock(txn, _) => txn.asInstanceOf[T]
      case txn => txn.asInstanceOf[T]
    }
  }

  /** A non-racy version of `lookup`, that must be paired with
   *  `endLookup`.
   */
  def beginLookup(slot: Int): T = {
    var e: AnyRef = null
    do {
      e = slots.get(slot)
    } while (e != null && !slots.compareAndSet(slot, e, locked(e)))
    unwrap(e)
  }

  private def locked(e: AnyRef): AnyRef = {
    e match {
      case SlotLock(txn, rc) => SlotLock(txn, rc + 1)
      case txn => SlotLock(txn, 1)
    }
  }

  def endLookup(slot: Int, observed: T) {
    if (null != observed) release(slot)
  }

  def release(slot: Int) {
    var e: AnyRef = null
    do {
      e = slots.get(slot)
    } while (!slots.compareAndSet(slot, e, unlocked(e)))
  }

  private def unlocked(e: AnyRef): AnyRef = {
    e match {
      case SlotLock(txn, 1) => txn
      case SlotLock(txn, rc) => SlotLock(txn, rc - 1)
      case txn => null
    }
  }

//  def assertAllReleased() {
//    for (i <- 0 until range) {
//      val e = slots.get(i)
//      if (null != e) {
//        assert(false, i + " -> " + e)
//      }
//    }
//  }
}
