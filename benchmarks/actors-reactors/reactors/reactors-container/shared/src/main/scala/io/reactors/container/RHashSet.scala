package io.reactors
package container



import scala.reflect.ClassTag



/** A reactive hash set.
 *
 *  @tparam T       type of the elements in the set
 */
class RHashSet[@spec(Int, Long, Double) T](
  implicit val arrayable: Arrayable[T]
) extends RContainer[T] with RContainer.Modifiable {
  private var table: Array[T] = null
  private var sz = 0
  private[reactors] var insertsEmitter: Events.Emitter[T] = null
  private[reactors] var removesEmitter: Events.Emitter[T] = null
  private[reactors] var subscription: Subscription = null
  private[reactors] var nil: T = _

  protected def init(ee: Arrayable[T]) {
    table = arrayable.newArray(RHashSet.initSize)
    insertsEmitter = new Events.Emitter[T]
    removesEmitter = new Events.Emitter[T]
    subscription = Subscription.empty
    nil = arrayable.nil
  }

  init(arrayable)

  def inserts: Events[T] = insertsEmitter

  def removes: Events[T] = removesEmitter

  def unsubscribe() = subscription.unsubscribe()

  def +=(elem: T): Boolean = {
    this add elem
  }

  def -=(elem: T): Boolean = {
    this remove elem
  }

  def foreach(f: T => Unit) {
    var i = 0
    while (i < table.length) {
      val k = table(i)
      if (k != nil) {
        f(k)
      }
      i += 1
    }
  }

  def size: Int = sz

  private[container] def lookup(k: T): Boolean = {
    var pos = index(k)
    var curr = table(pos)

    while (curr != nil && curr != k) {
      pos = (pos + 1) % table.length
      curr = table(pos)
    }

    if (curr == nil) false
    else true
  }

  private[container] def insert(k: T, notify: Boolean = true): Boolean = try {
    if (notify) acquireModify()
    checkResize()

    var pos = index(k)
    var curr = table(pos)
    assert(k != nil)

    while (curr != nil && curr != k) {
      pos = (pos + 1) % table.length
      curr = table(pos)
    }

    table(pos) = k
    val added = curr == nil
    if (added) sz += 1
    else removesEmitter.react(k, null)
    if (notify) insertsEmitter.react(k, null)

    added
  } finally releaseModify()

  private[container] def delete(k: T): Boolean = try {
    acquireModify()
    var pos = index(k)
    var curr = table(pos)

    while (curr != nil && curr != k) {
      pos = (pos + 1) % table.length
      curr = table(pos)
    }

    if (curr == nil) false
    else {
      var h0 = pos
      var h1 = (h0 + 1) % table.length
      while (table(h1) != nil) {
        val h2 = index(table(h1))
        if (h2 != h1 && before(h2, h0)) {
          table(h0) = table(h1)
          h0 = h1
        }
        h1 = (h1 + 1) % table.length
      }

      table(h0) = arrayable.nil
      sz -= 1
      removesEmitter.react(k, null)

      true
    }
  } finally releaseModify()

  private[reactors] def checkResize()(implicit arrayable: Arrayable[T]) {
    if (sz * 1000 / RHashSet.loadFactor > table.length) {
      val otable = table
      val ncapacity = table.length * 2
      table = arrayable.newArray(ncapacity)
      sz = 0

      var pos = 0
      while (pos < otable.length) {
        val curr = otable(pos)
        if (curr != nil) {
          val result = insert(curr, false)
        }

        pos += 1
      }
    }
  }

  private def before(i: Int, j: Int) = {
    val d = table.length >> 1
    if (i <= j) j - i < d
    else i - j > d
  }

  private def index(k: T): Int = {
    val hc = k.##
    math.abs(scala.util.hashing.byteswap32(hc)) % table.length
  }

  def apply(key: T): Boolean = lookup(key)

  def contains(key: T): Boolean = lookup(key)

  def add(key: T): Boolean = insert(key)

  def remove(key: T): Boolean = delete(key)

  def clear()(implicit a: Arrayable[T]): Unit = try {
    acquireModify()
    var pos = 0
    while (pos < table.length) {
      val elem = table(pos)
      if (elem != nil) {
        table(pos) = arrayable.nil
        sz -= 1
        removesEmitter.react(elem, null)
      }

      pos += 1
    }
  } finally releaseModify()

}


object RHashSet {

  def apply[@spec(Int, Long, Double) T: Arrayable]() = new RHashSet[T]

  val initSize = 16

  val loadFactor = 450

  implicit def factory[@spec(Int, Long, Double) T: Arrayable] =
    new RContainer.Factory[T, RHashSet[T]] {
      def apply(inserts: Events[T], removes: Events[T]): RHashSet[T] = {
        val hs = new RHashSet[T]
        hs.subscription = new Subscription.Composite(
          inserts.onEvent(hs += _),
          removes.onEvent(hs -= _)
        )
        hs
      }
    }

}
