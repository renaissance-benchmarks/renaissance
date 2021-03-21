package io.reactors.common



import java.util.concurrent.atomic.AtomicInteger
import scala.reflect.ClassTag



class IndexMap[K <: IndexMap.Key, V >: Null <: AnyRef: ClassTag] {
  private var array = new Array[V](4)

  def apply(k: K): V = {
    val idx = k.index
    if (idx < array.length) {
      array(idx)
    } else null
  }

  def update(k: K, v: V): Unit = put(k, v)

  private def ensureSize(idx: Int): Unit = {
    var nlen = array.length
    while (idx >= nlen) {
      nlen *= 2
    }
    val narray = new Array[V](nlen)
    System.arraycopy(array, 0, narray, 0, array.length)
    array = narray
  }

  def put(k: K, v: V): V = {
    val idx = k.index
    if (idx >= array.length) ensureSize(idx)
    val prev = array(idx)
    array(idx) = v
    prev
  }

  def remove(k: K): V = put(k, null)
}


object IndexMap {
  private[reactors] val indexCounter = new AtomicInteger(0)

  abstract class Key {
    val index = indexCounter.incrementAndGet()
  }
}