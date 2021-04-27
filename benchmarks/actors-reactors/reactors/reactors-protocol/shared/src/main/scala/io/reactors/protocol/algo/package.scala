package io.reactors
package protocol



import io.reactors.common.BinaryHeap
import scala.util.Random



package object algo {
  import scala.language.implicitConversions

  private[reactors] class EventsSamplingOps[@spec(Int, Long, Double) T](
    val events: Events[T]
  ) {
    /** Returns `k` uniformly sampled elements after this event stream unreacts.
     *
     *  This method takes `O(k)` space and reacting to each event takes `O(1)` time.
     *  If the remainder of `this` stream has less than `k` elements, then all those
     *  elements are returned in the sample.
     *
     *  See "Random sampling with a reservoir", by Vitter.
     */
    def sampleReservoir(k: Int)(implicit a: Arrayable[T]): IVar[Array[T]] = {
      assert(k > 0)
      val random = new Random
      val array = a.newRawArray(k)
      var i = 0
      val updates = events.map { x =>
        if (i < k) {
          array(i) = x
        } else {
          val j = random.nextInt(i + 1)
          if (j < k) array(j) = x
        }
        i += 1
        array
      }
      (Events.single(array) union updates).last
        .map(a => if (i < k) a.take(i) else a).toIVar
    }

    /** Returns `k` sampled elements after this event stream unreacts.
     *
     *  This mehtod takes `O(k)` space and reacting to each event takes `O(log k)` time.
     *  If the remainder of `this` stream has less than `k` elements, then all those
     *  elements are returned in the sample.
     *
     *  See "Weighted random sampling with a reservoir", by Efraimidis and Spirakis.
     */
    def sampleWeighted(k: Int, weight: T => Double)(
      implicit a: Arrayable[T]
    ): IVar[Array[T]] = {
      assert(k > 0)
      val random = new Random
      val heap = new BinaryHeap[(T, Double)](16)(implicitly, Order.double(_._2 - _._2))
      var i = 0
      val updates = events.map { x =>
        val p = math.pow(random.nextDouble(), 1 / weight(x))
        if (i < k) {
          heap.enqueue((x, p))
        } else if (heap.head._2 < p) {
          heap.dequeue()
          heap.enqueue((x, p))
        }
        i += 1
        heap
      }
      (Events.single(heap) union updates).last.map { h =>
        val array = a.newRawArray(h.size)
        var i = 0
        for (t <- h) {
          array(i) = t._1
          i += 1
        }
        array
      }.toIVar
    }
  }

  implicit def sampling[@spec(Int, Long, Double) T](events: Events[T]): EventsSamplingOps[T] =
    new EventsSamplingOps(events)
}
