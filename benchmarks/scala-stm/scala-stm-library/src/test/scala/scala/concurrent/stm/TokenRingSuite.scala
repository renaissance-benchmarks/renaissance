/* scala-stm - (c) 2009-2010, Stanford University, PPL */

package scala.concurrent.stm

import java.util.concurrent.CyclicBarrier
import org.scalatest.FunSuite


/** This test uses the transactional retry mechanism to pass a token around a
 *  ring of threads.  When there are two threads this is a ping-pong test.  A
 *  separate `Ref` is used for each handoff.
 *
 *  @author Nathan Bronson
 */
class TokenRingSuite extends FunSuite {
  test("small non-txn threesome") { tokenRing(3, 10000, false, false) }
  test("small txn threesome") { tokenRing(3, 1000, true, false) }
  test("small txn threesome reading via write") { tokenRing(3, 1000, true, true) }

  test("non-txn ping-pong", Slow) { tokenRing(2, 1000000, false, false) }
  test("non-txn threesome", Slow) { tokenRing(3, 1000000, false, false) }
  test("non-txn large ring", Slow) { tokenRing(32, 10000, false, false) }
  test("txn ping-pong", Slow) { tokenRing(2, 100000, true, false) }
  test("txn threesome", Slow) { tokenRing(3, 100000, true, false) }
  test("txn large ring", Slow) { tokenRing(32, 10000, true, false) }
  test("txn ping-pong reading via write", Slow) { tokenRing(2, 100000, true, true) }
  test("txn threesome reading via write", Slow) { tokenRing(3, 100000, true, true) }
  test("txn large ring reading via write", Slow) { tokenRing(32, 10000, true, true) }

  def tokenRing(ringSize: Int, handoffsPerThread: Int, useTxns: Boolean, useSwap: Boolean) {
    val ready = Array.tabulate(ringSize)(i => Ref(i == 0))
    val threads = new Array[Thread](ringSize - 1)
    val barrier = new CyclicBarrier(ringSize, new Runnable {
      var start = 0L
      def run {
        val now = System.currentTimeMillis
        if (start == 0) {
          start = now
        } else {
          val elapsed = now - start
          val handoffs = handoffsPerThread * ringSize
          println("tokenRing(" + ringSize + "," + handoffsPerThread + "," + useTxns +
            ")  total_elapsed=" + elapsed + " msec,  throughput=" +
            (handoffs * 1000L) / elapsed + " handoffs/sec,  latency=" +
            (elapsed * 1000000L) / handoffs + " nanos/handoff")
        }
      }
    })

    for (index <- 0 until ringSize) {
      val work = new Runnable {
        def run {
          val next = (index + 1) % ringSize
          barrier.await
          for (h <- 0 until handoffsPerThread) {
            if (!useTxns) {
              ready(index).single await { _ == true }
              ready(index).single() = false
              ready(next).single() = true
            } else {
              atomic { implicit t =>
                if (!useSwap) {
                  if (ready(index).get == false) retry
                  ready(index)() = false
                } else {
                  if (ready(index).swap(false) == false) retry
                }
                ready(next)() = true
              }
            }
          }
          barrier.await
        }
      }
      if (index < ringSize - 1) {
        threads(index) = new Thread(work, "worker " + index)
        threads(index).start
      } else {
        work.run
      }
    }

    for (t <- threads) t.join
  }
}
