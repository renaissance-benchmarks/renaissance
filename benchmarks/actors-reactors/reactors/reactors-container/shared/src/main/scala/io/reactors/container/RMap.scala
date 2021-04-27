package io.reactors
package container



import scala.annotation.implicitNotFound



/** Base class for reactive maps.
 *
 *  Reactive map is a collection of pairs of elements that exposes event streams of map
 *  keys with hints that are values mapped to those keys.
 *
 *  @tparam K       type of the keys in the map
 *  @tparam V       type of the values in the map
 */
trait RMap[@spec(Int, Long, Double) K, V]
extends RContainer[K] {
  /** Returns the value associated with the specified key.
   */
  def apply(k: K): V

  /** A stream of modifications events.
   *
   *  This stream is called immediately after the `inserts` and `removes` event streams
   *  emit values, and immediately before a modification method returns. Together with
   *  `inserts` and `removes`, it can be used to create event streams that, for example,
   *  track only the insertion of the new keys into the map, or modification of existing
   *  keys in the map.
   *
   *  @return         event stream with an event emitted per modification operation
   */
  def modified: Events[Unit]

  /** Creates an event stream that emits newly inserted keys.
   *
   *  @return         event stream with newly inserted keys
   */
  def adds: Events[K] = {
    modified.incremental {
      var key: K = null.asInstanceOf[K]
      var value: V = null.asInstanceOf[V]
      var seenInsert = false
      var seenRemove = false
      val sub = new Subscription.Composite(
        removes.on({ seenRemove = true }),
        inserts.onReaction(new Observer[K] {
          def react(k: K, v: Any) = {
            key = k
            value = v.asInstanceOf[V]
            seenInsert = true
          }
          def except(t: Throwable) = throw t
          def unreact() {}
        })
      )
      val sampler = (target: Observer[K]) => {
        val emit = seenInsert && !seenRemove
        seenInsert = false
        seenRemove = false
        if (emit) target.react(key, value)
      }
      (sub, sampler)
    }
  }

  /** Creates an stream that emits updates to keys that were already in the map.
   *
   *  @return         event stream with modified keys that had already been in the map
   */
  def updates: Events[K] = {
    modified.incremental {
      var key: K = null.asInstanceOf[K]
      var value: V = null.asInstanceOf[V]
      var seenInsert = false
      var seenRemove = false
      val sub = new Subscription.Composite(
        removes.on({ seenRemove = true }),
        inserts.onReaction(new Observer[K] {
          def react(k: K, v: Any) = {
            key = k
            value = v.asInstanceOf[V]
            seenInsert = true
          }
          def except(t: Throwable) = throw t
          def unreact() {}
        })
      )
      val sampler = (target: Observer[K]) => {
        val emit = seenInsert && seenRemove
        seenInsert = false
        seenRemove = false
        if (emit) target.react(key, value)
      }
      (sub, sampler)
    }
  }

  /** Filters and maps the values for which the partial function is defined.
   */
  def collectValue[W](pf: PartialFunction[V, W]): RMap[K, W] =
    new RMap.CollectValue(this, pf)

  /** Converts this map into a container of key-value pairs.
   *
   *  '''Note:''' this operation boxes the keys and values into tuple objects.
   *
   *  @return         a container with the key-value pairs in this map
   */
  def pairs: RContainer[(K, V)] = new RMap.Pairs(this)

  /** Converts this reactive map into another reactive map.
   */
  def toMap[That](implicit factory: RMap.Factory[K, V, That]): That = {
    val elements = new Events.Emitter[K]
    val container = factory(inserts union elements, removes)
    for (k <- this) elements.react(k, apply(k).asInstanceOf[AnyRef])
    elements.unreact()
    container
  }
}


object RMap {

  def apply[That](f: That => RMap.On[_, _])(
    implicit rf: RMap.Factory[_, _, That]
  ): That = {
    rf(m => f(m).subscription)
  }

  /** Reacts to insert and remove events on the reactive map.
   */
  abstract class On[@spec(Int, Long, Double) K, V](self: RMap[K, V]) {
    private[reactors] var subscription = Subscription.empty

    private[reactors] def init(b: On[K, V]) {
      subscription = new Subscription.Composite(
        self.inserts.onReaction(insertObserver),
        self.removes.onReaction(removeObserver)
      )
    }
    init(this)

    def insert(k: K, v: V): Unit
    def remove(k: K, v: V): Unit
    def except(t: Throwable) = throw t
    def unreact() = {}
    private[reactors] def insertObserver: Observer[K] =
      new InsertObserver(this)
    private[reactors] def removeObserver: Observer[K] =
      new RemoveObserver(this)
  }

  private[reactors] class InsertObserver[@spec(Int, Long, Double) K, V](
    val self: On[K, V]
  ) extends Observer[K] {
    def react(k: K, v: Any) = self.insert(k, v.asInstanceOf[V])
    def except(t: Throwable) = self.except(t)
    def unreact() = self.unreact()
  }

  private[reactors] class RemoveObserver[@spec(Int, Long, Double) K, V](
    val self: On[K, V]
  ) extends Observer[K] {
    def react(k: K, v: Any) = self.remove(k, v.asInstanceOf[V])
    def except(t: Throwable) = self.except(t)
    def unreact() = self.unreact()
  }

  /** Used to create reactive map objects.
   */
  @implicitNotFound(
    msg = "Cannot create a map of type ${That} with elements of type ${K} and ${V}.")
  trait Factory[@spec(Int, Long, Double) K, V, That] {
    def apply(inserts: Events[K], removes: Events[K]): That
    def apply(f: That => Subscription): That
  }

  private[reactors] class Pairs[@spec(Int, Long, Double) K, @spec(Int, Long, Double) V](
    val self: RMap[K, V]
  ) extends RContainer[(K, V)] {
    def inserts: Events[(K, V)] = self.inserts.zipHint((k, h) => (k, h.asInstanceOf[V]))
    def removes: Events[(K, V)] = self.removes.zipHint((k, h) => (k, h.asInstanceOf[V]))
    def foreach(f: ((K, V)) => Unit) = for (k <- self) f((k, self(k)))
    def size = self.size
    def unsubscribe() = {}
  }

  private[reactors] trait Derived[@spec(Int, Long, Double) K, V]
  extends RMap[K, V] {
    def selfModified: Events[Unit]
    def modified: Events[Unit] = {
      selfModified.incremental {
        var seenInsert = false
        var seenRemove = false
        val sub = new Subscription.Composite(
          inserts.on({ seenInsert = true }),
          removes.on({ seenRemove = true })
        )
        val sampler = (obs: Observer[Unit]) => {
          val emit = seenInsert || seenRemove
          seenInsert = false
          seenRemove = false
          if (emit) obs.react((), null)
        }
        (sub, sampler)
      }
    }
  }

  private[reactors] class CollectValue[@spec(Int, Long, Double) K, V, W](
    val self: RMap[K, V],
    val typedPf: PartialFunction[V, W]
  ) extends Derived[K, W] {
    def selfModified = self.modified
    val pf = typedPf.asInstanceOf[PartialFunction[Any, W]]
    def apply(k: K) = pf(self.apply(k))
    def inserts: Events[K] = self.inserts.collectHint(pf)
    def removes: Events[K] = self.removes.collectHint(pf)
    def foreach(f: K => Unit) =
      for (k <- self) if (pf.isDefinedAt(self(k))) f(k)
    def size = self.count(k => pf.isDefinedAt(self(k))).get
    def unsubscribe() = {}
  }
}
