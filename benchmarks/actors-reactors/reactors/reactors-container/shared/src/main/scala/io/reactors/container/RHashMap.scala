package io.reactors
package container



import scala.collection._
import scala.reflect.ClassTag



/** A reactive hash map.
 *
 *  In addition to standard `inserts` and `removes`, and other container event streams,
 *  reactive hash maps expose event streams with elements at specific keys.
 *
 *  @tparam K       type of the keys in the map, specialized
 *  @tparam V       type of the values in the map, must be a reference parameter
 */
class RHashMap[@spec(Int, Long, Double) K, V >: Null <: AnyRef](
  implicit val arrayable: Arrayable[K], val hash: Hash[K], val spec: Spec[K]
) extends RMap[K, V] with RContainer.Modifiable {
  private var table: Array[RHashMap.Entry[K, V]] = null
  private var elemCount = 0
  private var entryCount = 0
  private[reactors] var can: RHashMap.Can[K, V] = _
  private[reactors] var insertsEmitter: Events.Emitter[K] = null
  private[reactors] var removesEmitter: Events.Emitter[K] = null
  private[reactors] var modifiedEmitter: Events.Emitter[Unit] = null
  private[reactors] var subscription: Subscription = null

  protected def init(k: K) {
    can = RHashMap.canFor[K, V](arrayable)
    table = new Array(RHashMap.initSize)
    insertsEmitter = new Events.Emitter[K]
    removesEmitter = new Events.Emitter[K]
    modifiedEmitter = new Events.Emitter[Unit]
    subscription = Subscription.empty
  }

  init(null.asInstanceOf[K])

  def inserts: Events[K] = insertsEmitter

  def removes: Events[K] = removesEmitter

  def modified: Events[Unit] = modifiedEmitter

  def unsubscribe() = subscription.unsubscribe()

  /** Adds a key-value pair to the map.
   *
   *  If a key equal to the key from the pair already exists in the map, the existing
   *  mapping is removed.
   */
  def +=(kv: (K, V)) = {
    insert(kv._1, kv._2)
  }

  /** Removes a key-value pair from the map.
   *
   *  A key-value pair is removed iff the same key-value pair already exists in the map.
   */
  def -=(kv: (K, V)) = {
    delete(kv._1, kv._2) != null
  }

  private[reactors] def foreachEntry(f: RHashMap.Entry[K, V] => Unit) {
    var i = 0
    while (i < table.length) {
      var entry = table(i)
      while (entry ne null) {
        f(entry)
        entry = entry.next
      }
      i += 1
    }
  }

  def foreachTuple(f: ((K, V)) => Unit) = foreachEntry {
    e => if (e.value != null) f((e.key, e.value))
  }

  def foreach(f: K => Unit) = foreachEntry {
    e => if (e.value != null) f(e.key)
  }

  /** Returns an event stream that emits values stored at a specific key.
   *
   *  Each time that the value at the key is updated, an event is emitted. The initial
   *  value is emitted to the event stream when subscribing to the event stream. If
   *  there is no value associated with the key, or a value was just removed, then `nil`
   *  is emitted.
   *
   *  @param key     key for which to emit values
   */
  def at(key: K): Events[V] = ensure(key)

  private[reactors] def lookup(k: K): RHashMap.Entry[K, V] = {
    val pos = index(k)
    var entry = table(pos)

    while (entry != null && entry.key != k) {
      entry = entry.next
    }

    if (entry == null) null
    else entry
  }

  private[reactors] def ensure(k: K): RHashMap.Entry[K, V] = {
    val pos = index(k)
    var entry = table(pos)
    checkResize()

    while (entry != null && entry.key != k) {
      entry = entry.next
    }

    if (entry == null) {
      entry = can.newEntry(k, this)
      entry.next = table(pos)
      table(pos) = entry
      entry
    } else entry
  }

  private[reactors] def clean(entry: RHashMap.Entry[K, V]) {
    if (entry.value == null) {
      val pos = index(entry.key)
      table(pos) = table(pos).remove(entry)
    }
  }

  private[reactors] def insert(k: K, v: V): V = try {
    acquireModify()
    assert(v != null)
    checkResize()

    val pos = index(k)
    var entry = table(pos)

    while (entry != null && entry.key != k) {
      entry = entry.next
    }

    var previousValue: V = null
    if (entry == null) {
      entry = can.newEntry(k, this)
      entry.value = v
      entry.next = table(pos)
      table(pos) = entry
      entryCount += 1
    } else {
      previousValue = entry.value
      entry.value = v
    }

    var needRemoveEvent = false
    if (previousValue == null) elemCount += 1
    else needRemoveEvent = true
    
    insertsEmitter.react(k, v)
    if (needRemoveEvent) removesEmitter.react(k, previousValue)
    modifiedEmitter.react((), null)
    
    entry.propagate()

    previousValue
  } finally releaseModify()

  private[reactors] def emitInserts(k: K, v: V) {
    if (insertsEmitter.hasSubscriptions) insertsEmitter.react(k, v)
  }

  private[reactors] def emitRemoves(k: K, v: V) {
    if (removesEmitter.hasSubscriptions) removesEmitter.react(k, v)
  }

  private[reactors] def delete(k: K, expectedValue: V = null): V = try {
    acquireModify()
    val pos = index(k)
    var entry = table(pos)

    while (entry != null && entry.key != k) {
      entry = entry.next
    }

    if (entry == null) null
    else {
      val previousValue = entry.value

      if (expectedValue == null || expectedValue == previousValue) {
        entry.value = null

        elemCount -= 1
        if (!entry.hasSubscriptions) {
          table(pos) = table(pos).remove(entry)
          entryCount -= 1
        }

        if (removesEmitter.hasSubscriptions)
          removesEmitter.react(k, previousValue)
        entry.propagate()
        modifiedEmitter.react((), null)

        previousValue
      } else null
    }
  } finally releaseModify()

  private def checkResize()(implicit s: Spec[K]) {
    if (entryCount * 1000 / RHashMap.loadFactor > table.length) {
      val otable = table
      val ncapacity = table.length * 2
      table = new Array(ncapacity)
      elemCount = 0
      entryCount = 0

      var opos = 0
      while (opos < otable.length) {
        var entry = otable(opos)
        while (entry != null) {
          val nextEntry = entry.next
          val pos = index(entry.key)
          entry.next = table(pos)
          table(pos) = entry
          entryCount += 1
          if (entry.value != null) elemCount += 1
          entry = nextEntry
        }
        opos += 1
      }
    }
  }

  private def index(k: K): Int = {
    val hc = hash(k)
    math.abs(scala.util.hashing.byteswap32(hc)) % table.length
  }

  private def noKeyError(key: K) = throw new NoSuchElementException("key: " + key)

  /** Denotes the absence of values at various keys.
   */
  def nil: V = null

  /** Gets the value at the specified key, or `nil` if there is none.
   */
  def applyOrNil(key: K): V = {
    val entry = lookup(key)
    if (entry == null || entry.value == null) null
    else entry.value
  }

  /** Returns the value at the specified key, or throws an exception if there is none.
   */
  def apply(key: K): V = {
    val entry = lookup(key)
    if (entry == null || entry.value == null) noKeyError(key)
    else entry.value
  }

  /** Optionally gets the value associated to the specified key.
   */
  def get(key: K): Option[V] = {
    val entry = lookup(key)
    if (entry == null || entry.value == null) None
    else Some(entry.value)
  }

  /** Checks if the given key exists in the map.
   */
  def contains(key: K): Boolean = {
    val entry = lookup(key)
    if (entry == null || entry.value == null) false
    else true
  }

  /** Updates the value at the specific key.
   */
  def update(key: K, value: V): Unit = {
    insert(key, value)
  }

  /** Removes the mapping at the specified key.
   */
  def remove(key: K): Boolean = delete(key) match {
    case null => false
    case v => true
  }

  /** Removes all elements from the map.
   */
  def clear()(implicit s: Spec[K]): Unit = try {
    acquireModify()
    var pos = 0
    while (pos < table.length) {
      var entry = table(pos)
      while (entry != null) {
        val nextEntry = entry.next
        val previousValue = entry.value

        entry.value = null
        if (!entry.hasSubscriptions) table(pos) = table(pos).remove(entry)
        entry.propagate()(spec)
        if (previousValue != null) {
          elemCount -= 1
          removesEmitter.react(entry.key, previousValue)
        }
        modifiedEmitter.react((), null)

        entry = nextEntry
      }

      pos += 1
    }
    if (elemCount != 0) {
      throw new IllegalStateException("Size not zero after clear: " + elemCount)
    }
  } finally releaseModify()

  def size: Int = elemCount
  
  override def toString = {
    val elems = mutable.Buffer[(K, V)]()
    this.foreachTuple(kv => elems += kv)
    s"RHashMap($size, ${elems.mkString(", ")})"
  }

}


object RHashMap {

  trait Entry[@spec(Int, Long, Double) K, V >: Null <: AnyRef]
  extends Events.Push[V] {
    def outer: RHashMap[K, V]
    def key: K
    def value: V
    def value_=(v: V): Unit
    def next: Entry[K, V]
    def next_=(e: Entry[K, V]): Unit
    def apply(): V = value
    def propagate()(implicit s: Spec[K]) = reactAll(value, null)
    def remove(e: Entry[K, V]): Entry[K, V] = if (this eq e) next else {
      if (next ne null) next = next.remove(e)
      this
    }
    override def onReaction(obs: Observer[V]): Subscription = {
      val sub = super.onReaction(obs)
      obs.react(value, null)
      sub.andThen(if (!hasSubscriptions) outer.clean(this))
    }
    override def toString = s"Entry($key, $value)"
  }

  trait Can[@spec(Int, Long, Double) K, V >: Null <: AnyRef] {
    def newEntry(key: K, outer: RHashMap[K, V]): RHashMap.Entry[K, V]
  }

  def canFor[
    @spec(Int, Long, Double) K,
    V >: Null <: AnyRef
  ](a: Arrayable[K]): Can[K, V] = {
    import scala.language.existentials

    val cls = a.newRawArray(0).getClass
    val elemcls = cls.getComponentType
    val can = {
      if (cls == classOf[Array[Int]]) canInt[V]
      else if (cls == classOf[Array[Long]]) canLong[V]
      else if (cls == classOf[Array[Double]]) canDouble[V]
      else if (classOf[AnyRef].isAssignableFrom(elemcls)) canAnyRef[AnyRef, V]
      else sys.error(s"Cannot create hash map for key class $cls")
    }
    can.asInstanceOf[Can[K, V]]
  }

  implicit def canAnyRef[K >: Null <: AnyRef, V >: Null <: AnyRef] = new Can[K, V] {
    def newEntry(k: K, o: RHashMap[K, V]) = new RHashMap.Entry[K, V] {
      def outer = o
      def key = k
      var value: V = _
      var next: Entry[K, V] = null
    }
  }

  implicit def canInt[V >: Null <: AnyRef] = new Can[Int, V] {
    def newEntry(k: Int, o: RHashMap[Int, V]) = new RHashMap.Entry[Int, V] {
      def outer = o
      def key = k
      var value: V = _
      var next: Entry[Int, V] = null
    }
  }

  implicit def canLong[V >: Null <: AnyRef] = new Can[Long, V] {
    def newEntry(k: Long, o: RHashMap[Long, V]) = new RHashMap.Entry[Long, V] {
      def outer = o
      def key = k
      var value: V = _
      var next: Entry[Long, V] = null
    }
  }

  implicit def canDouble[V >: Null <: AnyRef] = new Can[Double, V] {
    def newEntry(k: Double, o: RHashMap[Double, V]) = new RHashMap.Entry[Double, V] {
      def outer = o
      def key = k
      var value: V = _
      var next: Entry[Double, V] = null
    }
  }

  val initSize = 16

  val loadFactor = 750

  implicit def containerFactory[@spec(Int, Long, Double) K, V >: Null <: AnyRef](
    implicit a: Arrayable[K], hash: Hash[K], spec: Spec[K]
  ) = {
    new RContainer.Factory[(K, V), RHashMap[K, V]] {
      def apply(inserts: Events[(K, V)], removes: Events[(K, V)]): RHashMap[K, V] = {
        val hm = new RHashMap[K, V]
        hm.subscription = new Subscription.Composite(
          inserts.onEvent(hm += _),
          removes.onEvent(hm -= _)
        )
        hm
      }
    }
  }

  implicit def factory[@spec(Int, Long, Double) K, V >: Null <: AnyRef](
    implicit a: Arrayable[K], hash: Hash[K], spec: Spec[K]
  ) = {
    new RMap.Factory[K, V, RHashMap[K, V]] {
      def apply(inserts: Events[K], removes: Events[K]): RHashMap[K, V] = {
        val hm = new RHashMap[K, V]
        hm.subscription = new Subscription.Composite(
          inserts.onReaction(new FactoryInsertObserver(hm)),
          removes.onReaction(new FactoryRemoveObserver(hm))
        )
        hm
      }
      def apply(f: RHashMap[K, V] => Subscription): RHashMap[K, V] = {
        val hm = new RHashMap[K, V]
        hm.subscription = f(hm)
        hm
      }
    }
  }

  class FactoryInsertObserver[@spec(Int, Long, Double) K, V >: Null <: AnyRef](
    hm: RHashMap[K, V]
  ) extends Observer[K] {
    def react(x: K, v: Any) = hm.insert(x, v.asInstanceOf[V])
    def except(t: Throwable) = {}
    def unreact() = {}
  }

  class FactoryRemoveObserver[@spec(Int, Long, Double) K, V >: Null <: AnyRef](
    hm: RHashMap[K, V]
  ) extends Observer[K] {
    def react(x: K, v: Any) = hm.delete(x, v.asInstanceOf[V])
    def except(t: Throwable) = {}
    def unreact() = {}
  }

}
