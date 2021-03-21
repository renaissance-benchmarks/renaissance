package io.reactors
package common






/** Bloom-filtered hash map that has fast checks when the key is not in the map.
 *
 *  Equality and hashing are reference-based.
 *
 *  The fast checks use the identity hash. The map cannot contain `null` keys or values.
 *  Values are specialized for integers and longs.
 *
 *  The internal representation is a linear array when there are `4` keys or less,
 *  and it switches to the slightly slower hash-based variant only after inserting
 *  more than `4` keys.
 */
class BloomMap[K >: Null <: AnyRef: Arrayable, @specialized(Int, Long) V: Arrayable] {
  private var keytable = implicitly[Arrayable[K]].newRawArray(4)
  private var valtable = implicitly[Arrayable[V]].newArray(4)
  private var rawSize = 0
  private var bloom = new Array[Byte](0)
  private val rawNil = implicitly[Arrayable[V]].nil

  def contains(key: K): Boolean = {
    if (keytable.length <= 4) {
      fastlookup(key) != rawNil
    } else {
      val hash = System.identityHashCode(key) >>> 1
      val idx = (hash >>> 2) % bloom.length
      val pos = 1 << (hash & 0x7)
      val down = (bloom(idx) & pos) == 0
      if (down) false
      else lookup(key, hash) != rawNil
    }
  }

  private def fastlookup(key: K): V = {
    var pos = 0
    while (pos < 4) {
      val curr = keytable(pos)
      if (curr eq key) {
        return valtable(pos)
      }
      pos += 1
    }
    rawNil
  }

  private def lookup(key: K, hash: Int): V = {
    var pos = hash % keytable.length
    var curr = keytable(pos)
    while (curr != null && (curr ne key)) {
      pos = (pos + 1) % keytable.length
      curr = keytable(pos)
    }
    valtable(pos)
  }

  def nil: V = rawNil

  def get(key: K): V = {
    if (keytable.length <= 4) {
      fastlookup(key)
    } else {
      val hash = System.identityHashCode(key) >>> 1
      val idx = (hash >>> 2) % bloom.length
      val pos = 1 << (hash & 0x7)
      val down = (bloom(idx) & pos) == 0
      if (down) rawNil
      else lookup(key, hash)
    }
  }

  private def fastinsert(key: K, value: V): V = {
    var pos = 0
    while (pos < 4) {
      val curr = keytable(pos)
      if (curr eq key) {
        val previousValue = valtable(pos)
        keytable(pos) = key
        valtable(pos) = value
        return previousValue
      }
      if (curr eq null) {
        keytable(pos) = key
        valtable(pos) = value
        rawSize += 1
        return rawNil
      }
      pos += 1
    }
    sys.error("Should not reach here.")
  }

  private def insert(key: K, value: V): V = {
    var pos = (System.identityHashCode(key) >>> 1) % keytable.length
    assert(pos >= 0)
    var curr = keytable(pos)
    while (curr != null && (curr ne key)) {
      pos = (pos + 1) % keytable.length
      curr = keytable(pos)
    }

    val previousValue = valtable(pos)
    keytable(pos) = key
    valtable(pos) = value
    
    val keyAdded = curr == null
    if (keyAdded) rawSize += 1
    previousValue
  }

  private def checkResize(nil: V): Unit = {
    if (rawSize > keytable.length.toLong * BloomMap.loadFactor / 1000) {
      resize(nil)
    }
  }

  private def resize(nil: V): Unit = {
    val okeytable = keytable
    val ovaltable = valtable
    val ncapacity = keytable.length * 2
    keytable = implicitly[Arrayable[K]].newRawArray(ncapacity)
    valtable = implicitly[Arrayable[V]].newArray(ncapacity)
    rawSize = 0

    var pos = 0
    while (pos < okeytable.length) {
      val curr = okeytable(pos)
      if (curr != null) {
        val specializationDummy = insert(curr, ovaltable(pos))
      }
      pos += 1
    }
  }

  private def resizeBloomFilter() {
    bloom = new Array(keytable.length / 2)
    var i = 0
    while (i < keytable.length) {
      val key = keytable(i)
      if (key != null) {
        val hash = System.identityHashCode(key) >>> 1
        val idx = (hash >>> 2) % bloom.length
        val pos = 1 << (hash & 0x7)
        bloom(idx) = (bloom(idx) | pos).toByte
      }
      i += 1
    }
  }

  def put(key: K, value: V): Unit = {
    assert(key != null)
    if (keytable.length <= 4 && rawSize < 4) {
      fastinsert(key, value)
    } else {
      checkResize(rawNil)
      insert(key, value)
      if (bloom.length < keytable.length / 4) {
        resizeBloomFilter()
      }
      val hash = System.identityHashCode(key) >>> 1
      val idx = (hash >>> 2) % bloom.length
      val pos = 1 << (hash & 0x7)
      bloom(idx) = (bloom(idx) | pos).toByte
    }
  }

  def size: Int = rawSize

  def isEmpty: Boolean = size == 0

  def nonEmpty: Boolean = !isEmpty

  private def before(i: Int, j: Int): Boolean = {
    val d = keytable.length >> 1
    if (i <= j) j - i < d
    else i - j > d
  }

  private def delete(key: K): V = {
    assert(key != null)
    if (keytable.length <= 4) {
      var pos = 0
      while (pos < 4) {
        val curr = keytable(pos)
        if (curr eq key) {
          return valtable(pos)
        }
        pos += 1
      }
      rawNil
    } else {
      var pos = (System.identityHashCode(key) >>> 1) % keytable.length
      var curr = keytable(pos)
      while (curr != null && (curr ne key)) {
        pos = (pos + 1) % keytable.length
        curr = keytable(pos)
      }
      if (curr == null) rawNil
      else {
        val previousValue = valtable(pos)
        var h0 = pos
        var h1 = (h0 + 1) % keytable.length
        while (keytable(h1) != null) {
          val h2 = (System.identityHashCode(keytable(h1)) >>> 1) % keytable.length
          if (h2 != h1 && before(h2, h0)) {
            keytable(h0) = keytable(h1)
            valtable(h0) = valtable(h1)
            h0 = h1
          }
          h1 = (h1 + 1) % keytable.length
        }
        keytable(h0) = null
        valtable(h0) = rawNil
        rawSize -= 1
        previousValue
      }
    }
  }

  def remove(key: K): V = delete(key)

  def clear()(implicit spec: BloomMap.Spec[V]): Unit = if (rawSize > 0) {
    var i = 0
    while (i < keytable.length) {
      keytable(i) = null
      valtable(i) = rawNil
      i += 1
    }
    i = 0
    while (i < bloom.length) {
      bloom(i) = 0
      i += 1
    }
    rawSize = 0
  }
}


object BloomMap {
  val loadFactor = 200

  class Spec[@specialized(Int, Long) T]

  implicit val intSpec = new Spec[Int]

  implicit val longSpec = new Spec[Long]

  private val anySpecValue = new Spec[Any]

  implicit def anySpec[T] = anySpecValue.asInstanceOf[Spec[T]]
}
