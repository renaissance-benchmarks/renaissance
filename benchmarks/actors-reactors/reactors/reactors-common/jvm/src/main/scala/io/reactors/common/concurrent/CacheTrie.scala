package io.reactors.common.concurrent



import sun.misc.Unsafe
import scala.annotation.switch
import scala.annotation.tailrec



class CacheTrie[K <: AnyRef, V <: AnyRef](
  val useCounters: Boolean = true,
  val doCompression: Boolean = true
) {
  import CacheTrie._

  private val unsafe: Unsafe = Platform.unsafe
  @volatile private var rawCache: Array[AnyRef] = null
  private val rawRoot: Array[AnyRef] = createWideArray()

  private def createWideArray(): Array[AnyRef] = {
    val node = new Array[AnyRef](16 + 1)
    node(16) = Integer.valueOf(0)
    node
  }

  private def createNarrowArray(): Array[AnyRef] = {
    val node = new Array[AnyRef](4 + 1)
    node(4) = Integer.valueOf(0)
    node
  }

  private def createCacheArray(level: Int): Array[AnyRef] = {
    new Array[AnyRef](1 + (1 << level))
  }

  private def usedLength(array: Array[AnyRef]) = array.length - 1

  @tailrec
  private def decrementCount(array: Array[AnyRef]): Unit = {
    val countIndex = array.length - 1
    val count = READ(array, countIndex).asInstanceOf[Integer]
    val newCount = Integer.valueOf(count.intValue - 1)
    if (!CAS(array, countIndex, count, newCount)) decrementCount(array)
  }

  @tailrec
  private def incrementCount(array: Array[AnyRef]): Unit = {
    val countIndex = array.length - 1
    val count = READ(array, countIndex).asInstanceOf[Integer]
    val newCount = Integer.valueOf(count.intValue + 1)
    if (!CAS(array, countIndex, count, newCount)) incrementCount(array)
  }

  private def sequentialFixCount(array: Array[AnyRef]): Unit = {
    var i = 0
    var count = 0
    while (i < usedLength(array)) {
      val entry = array(i)
      if (entry != null) count += 1
      if (entry.isInstanceOf[Array[AnyRef]]) {
        sequentialFixCount(entry.asInstanceOf[Array[AnyRef]])
      }
      i += 1
    }
    array(array.length - 1) = Integer.valueOf(count)
  }

  private def READ(array: Array[AnyRef], pos: Int): AnyRef = {
    unsafe.getObjectVolatile(array, ArrayBase + (pos << ArrayShift))
  }

  private def CAS(array: Array[AnyRef], pos: Int, ov: AnyRef, nv: AnyRef): Boolean = {
    unsafe.compareAndSwapObject(array, ArrayBase + (pos << ArrayShift), ov, nv)
  }

  private def WRITE(array: Array[AnyRef], pos: Int, nv: AnyRef): Unit = {
    unsafe.putObjectVolatile(array, ArrayBase + (pos << ArrayShift), nv)
  }

  private def READ_CACHE: Array[AnyRef] = rawCache

  private def CAS_CACHE(ov: Array[AnyRef], nv: Array[AnyRef]) = {
    unsafe.compareAndSwapObject(this, CacheTrieRawCacheOffset, ov, nv)
  }

  private def READ_WIDE(enode: ENode): Array[AnyRef] = enode.wide

  private def CAS_WIDE(enode: ENode, ov: Array[AnyRef], nv: Array[AnyRef]): Boolean = {
    unsafe.compareAndSwapObject(enode, ENodeWideOffset, ov, nv)
  }

  private def READ_TXN(snode: SNode[_, _]): AnyRef = snode.txn

  private def CAS_TXN(snode: SNode[_, _], nv: AnyRef): Boolean = {
    unsafe.compareAndSwapObject(snode, SNodeFrozenOffset, NoTxn, nv)
  }

  private def spread(h: Int): Int = {
    (h ^ (h >>> 16)) & 0x7fffffff
  }

  private[concurrent] def fastLookup(key: K): V = {
    val hash = spread(key.hashCode)
    fastLookup(key, hash)
  }

  private[concurrent] final def fastLookup(key: K, hash: Int): V = {
    val cache = READ_CACHE
    if (cache == null) {
      slowLookup(key, hash, 0, rawRoot, null)
    } else {
      val len = cache.length
      val mask = len - 1 - 1
      val pos = 1 + (hash & mask)
      val cachee = READ(cache, pos)
      val level = 31 - Integer.numberOfLeadingZeros(len - 1)
      if (cachee eq null) {
        // Nothing is cached at this location, do slow lookup.
        slowLookup(key, hash, 0, rawRoot, cache)
      } else if (cachee.isInstanceOf[SNode[_, _]]) {
        // println(s"$key - found single node cachee, cache level $level")
        val oldsn = cachee.asInstanceOf[SNode[K, V]]
        val txn = READ_TXN(oldsn)
        if (txn eq NoTxn) {
          val oldhash = oldsn.hash
          val oldkey = oldsn.key
          if ((oldhash == hash) && ((oldkey eq key) || (oldkey == key))) oldsn.value
          else null.asInstanceOf[V]
        } else {
          // The single node is either frozen or scheduled for modification
          slowLookup(key, hash, 0, rawRoot, cache)
        }
      } else if (cachee.isInstanceOf[Array[AnyRef]]) {
        // println(s"$key - found array cachee, cache level $level")
        val an = cachee.asInstanceOf[Array[AnyRef]]
        val mask = usedLength(an) - 1
        val pos = (hash >>> level) & mask
        val old = READ(an, pos)
        if (old eq null) {
          // The key is not present in the cache trie.
          null.asInstanceOf[V]
        } else if (old.isInstanceOf[SNode[_, _]]) {
          val oldsn = old.asInstanceOf[SNode[K, V]]
          val txn = READ_TXN(oldsn)
          if (txn eq NoTxn) {
            // The single node is up-to-date.
            // Check if the key is contained in the single node.
            val oldhash = oldsn.hash
            val oldkey = oldsn.key
            if ((oldhash == hash) && ((oldkey eq key) || (oldkey == key))) oldsn.value
            else null.asInstanceOf[V]
          } else {
            // The single node is either frozen or scheduled for modification.
            slowLookup(key, hash, 0, rawRoot, cache)
          }
        } else {
          def resumeSlowLookup(): V = {
            if (old.isInstanceOf[Array[AnyRef]]) {
              // Continue the search from the specified level.
              val oldan = old.asInstanceOf[Array[AnyRef]]
              slowLookup(key, hash, level + 4, oldan, cache)
            } else if (old.isInstanceOf[LNode[_, _]]) {
              // Check if the key is contained in the list node.
              var tail = old.asInstanceOf[LNode[K, V]]
              while (tail != null) {
                if ((tail.hash == hash) && ((tail.key eq key) || (tail.key == key))) {
                  return tail.value
                }
                tail = tail.next
              }
              null.asInstanceOf[V]
            } else if ((old eq FVNode) || old.isInstanceOf[FNode]) {
              // Array node contains a frozen node, so it is obsolete -- do slow lookup.
              slowLookup(key, hash, 0, rawRoot, cache)
            } else if (old.isInstanceOf[ENode]) {
              // Help complete the transaction.
              val en = old.asInstanceOf[ENode]
              completeExpansion(cache, en)
              fastLookup(key, hash)
            } else if (old.isInstanceOf[XNode]) {
              // Help complete the transaction.
              val xn = old.asInstanceOf[XNode]
              completeCompression(cache, xn)
              fastLookup(key, hash)
            } else {
              sys.error(s"Unexpected case -- $old")
            }
          }
          resumeSlowLookup()
        }
      } else {
        sys.error(s"Unexpected case -- $cachee is not supposed to be cached.")
      }
    }
  }

  final def apply(key: K): V = {
    val result = lookup(key)
    if (result.asInstanceOf[AnyRef] eq null) throw new NoSuchElementException
    else result
  }

  final def get(key: K): Option[V] = {
    val result = lookup(key)
    if (result.asInstanceOf[AnyRef] eq null) None
    else Some(result)
  }

  final def lookup(key: K): V = {
    val hash = spread(key.hashCode)
    fastLookup(key, hash)
  }

  private[concurrent] def slowLookup(key: K): V = {
    val hash = spread(key.hashCode)
    slowLookup(key, hash)
  }

  private[concurrent] def slowLookup(key: K, hash: Int): V = {
    val node = rawRoot
    val cache = READ_CACHE
    slowLookup(key, hash, 0, node, cache)
  }

  @tailrec
  private[concurrent] final def slowLookup(
    key: K, hash: Int, level: Int, node: Array[AnyRef], cache: Array[AnyRef]
  ): V = {
    if (cache != null && (1 << level) == (cache.length - 1)) {
      inhabitCache(cache, node, hash, level)
    }
    val mask = usedLength(node) - 1
    val pos = (hash >>> level) & mask
    val old = READ(node, pos)
    if (old eq null) {
      null.asInstanceOf[V]
    } else if (old.isInstanceOf[Array[AnyRef]]) {
      val an = old.asInstanceOf[Array[AnyRef]]
      slowLookup(key, hash, level + 4, an, cache)
    } else if (old.isInstanceOf[SNode[_, _]]) {
      val cacheLevel =
        if (cache == null) 0
        else 31 - Integer.numberOfLeadingZeros(cache.length - 1)
      if (level < cacheLevel || level >= cacheLevel + 8) {
        recordCacheMiss()
      }
      val oldsn = old.asInstanceOf[SNode[K, V]]
      if (cache != null && (1 << (level + 4)) == (cache.length - 1)) {
        // println(s"about to inhabit for single node -- ${level + 4} vs $cacheLevel")
        inhabitCache(cache, oldsn, hash, level + 4)
      }
      if ((oldsn.hash == hash) && ((oldsn.key eq key) || (oldsn.key == key))) {
        oldsn.value
      } else {
        null.asInstanceOf[V]
      }
    } else if (old.isInstanceOf[LNode[_, _]]) {
      val cacheLevel =
        if (cache == null) 0
        else 31 - Integer.numberOfLeadingZeros(cache.length - 1)
      if (level < cacheLevel || level >= cacheLevel + 8) {
        // A potential cache miss -- we need to check the cache state.
        recordCacheMiss()
      }
      val oldln = old.asInstanceOf[LNode[K, V]]
      if (oldln.hash != hash) {
        null.asInstanceOf[V]
      } else {
        var tail = oldln
        while (tail != null) {
          if ((tail.key eq key) || (tail.key == key)) {
            return tail.value
          }
          tail = tail.next
        }
        null.asInstanceOf[V]
      }
    } else if (old.isInstanceOf[ENode]) {
      val enode = old.asInstanceOf[ENode]
      val narrow = enode.narrow
      slowLookup(key, hash, level + 4, narrow, cache)
    } else if (old.isInstanceOf[XNode]) {
      val xnode = old.asInstanceOf[XNode]
      val stale = xnode.stale
      slowLookup(key, hash, level + 4, stale, cache)
    } else if (old eq FVNode) {
      null.asInstanceOf[V]
    } else if (old.isInstanceOf[FNode]) {
      val frozen = old.asInstanceOf[FNode].frozen
      if (frozen.isInstanceOf[SNode[_, _]]) {
        sys.error(s"Unexpected case (should never be frozen): $frozen")
      } else if (frozen.isInstanceOf[LNode[_, _]]) {
        val ln = frozen.asInstanceOf[LNode[K, V]]
        if (ln.hash != hash) {
          null.asInstanceOf[V]
        } else {
          var tail = ln
          while (tail != null) {
            if ((tail.key eq key) || (tail.key == key)) {
              return tail.value
            }
            tail = tail.next
          }
          null.asInstanceOf[V]
        }
      } else if (frozen.isInstanceOf[Array[AnyRef]]) {
        val an = frozen.asInstanceOf[Array[AnyRef]]
        slowLookup(key, hash, level + 4, an, cache)
      } else {
        sys.error(s"Unexpected case: $old")
      }
    } else {
      sys.error(s"Unexpected case: $old")
    }
  }

  final def insert(key: K, value: V): Unit = {
    val hash = spread(key.hashCode)
    fastInsert(key, value, hash)
  }

  private def fastInsert(key: K, value: V, hash: Int): Unit = {
    val cache = READ_CACHE
    fastInsert(key, value, hash, cache, cache)
  }

  @tailrec
  private def fastInsert(
    key: K, value: V, hash: Int, cache: Array[AnyRef], prevCache: Array[AnyRef]
  ): Unit = {
    if (cache == null) {
      slowInsert(key, value, hash)
    } else {
      val len = cache.length
      val mask = len - 1 - 1
      val pos = 1 + (hash & mask)
      val cachee = READ(cache, pos)
      val level = 31 - Integer.numberOfLeadingZeros(len - 1)
      if (cachee eq null) {
        // Inconclusive -- retry one cache layer above.
        val stats = READ(cache, 0)
        val parentCache = stats.asInstanceOf[CacheNode].parent
        fastInsert(key, value, hash, parentCache, cache)
      } else if (cachee.isInstanceOf[Array[AnyRef]]) {
        // Read from the array node.
        val an = cachee.asInstanceOf[Array[AnyRef]]
        val mask = usedLength(an) - 1
        val pos = (hash >>> level) & mask
        val old = READ(an, pos)
        if (old eq null) {
          // Try to write the single node directly.
          val sn = new SNode(hash, key, value)
          if (CAS(an, pos, old, sn)) {
            incrementCount(an)
            return
          } else fastInsert(key, value, hash, cache, prevCache)
        } else if (old.isInstanceOf[Array[AnyRef]]) {
          // Continue search recursively.
          val oldan = old.asInstanceOf[Array[AnyRef]]
          val res = slowInsert(key, value, hash, level + 4, oldan, an, prevCache)
          if (res eq Restart) fastInsert(key, value, hash, cache, prevCache)
        } else if (old.isInstanceOf[SNode[_, _]]) {
          val oldsn = old.asInstanceOf[SNode[K, V]]
          val txn = READ_TXN(oldsn)
          if (txn eq NoTxn) {
            // No other transaction in progress.
            if ((oldsn.hash == hash) && ((oldsn.key eq key) || (oldsn.key == key))) {
              // Replace this key in the parent.
              val sn = new SNode(hash, key, value)
              if (CAS_TXN(oldsn, sn)) {
                CAS(an, pos, oldsn, sn)
                // Note: must not increment the count here.
              } else fastInsert(key, value, hash, cache, prevCache)
            } else if (usedLength(an) == 4) {
              // Must expand, but cannot do so without the parent.
              // Retry one cache level above.
              val stats = READ(cache, 0)
              val parentCache = stats.asInstanceOf[CacheNode].parent
              fastInsert(key, value, hash, parentCache, cache)
            } else {
              // Create an array node at the next level and replace the single node.
              val nnode = newNarrowOrWideNode(
                oldsn.hash, oldsn.key, oldsn.value, hash, key, value, level + 4)
              if (CAS_TXN(oldsn, nnode)) {
                CAS(an, pos, oldsn, nnode)
              } else fastInsert(key, value, hash, cache, prevCache)
            }
          } else if (txn eq FSNode) {
            // Must restart from the root, to find the transaction node, and help.
            slowInsert(key, value, hash)
          } else {
            // Complete the current transaction, and retry.
            CAS(an, pos, oldsn, txn)
            fastInsert(key, value, hash, cache, prevCache)
          }
        } else {
          // Must restart from the root, to find the transaction node, and help.
          slowInsert(key, value, hash)
        }
      } else if (cachee.isInstanceOf[SNode[_, _]]) {
        // Need a reference to the parent array node -- retry one cache level above.
        val stats = READ(cache, 0)
        val parentCache = stats.asInstanceOf[CacheNode].parent
        fastInsert(key, value, hash, parentCache, cache)
      } else {
        sys.error(s"Unexpected case -- $cachee is not supposed to be cached.")
      }
    }
  }

  private[concurrent] final def slowInsert(key: K, value: V): Unit = {
    val hash = spread(key.hashCode)
    slowInsert(key, value, hash)
  }

  private def slowInsert(key: K, value: V, hash: Int): Unit = {
    val node = rawRoot
    val cache = READ_CACHE
    var result = Restart
    do {
      result = slowInsert(key, value, hash, 0, node, null, cache)
    } while (result == Restart)
  }

  @tailrec
  private[concurrent] final def slowInsert(
    key: K, value: V, hash: Int, level: Int,
    current: Array[AnyRef], parent: Array[AnyRef],
    cache: Array[AnyRef]
  ): AnyRef = {
    if (cache != null && (1 << level) == (cache.length - 1)) {
      inhabitCache(cache, current, hash, level)
    }
    val mask = usedLength(current) - 1
    val pos = (hash >>> level) & mask
    val old = READ(current, pos)
    if (old eq null) {
      // Fast-path -- CAS the node into the empty position.
      val cacheLevel =
        if (cache == null) 0
        else 31 - Integer.numberOfLeadingZeros(cache.length - 1)
      if (level < cacheLevel || level >= cacheLevel + 8) {
        recordCacheMiss()
      }
      val snode = new SNode(hash, key, value)
      if (CAS(current, pos, old, snode)) {
        incrementCount(current)
        Success
      } else slowInsert(key, value, hash, level, current, parent, cache)
    } else if (old.isInstanceOf[Array[_]]) {
      // Repeat the search on the next level.
      val oldan = old.asInstanceOf[Array[AnyRef]]
      slowInsert(key, value, hash, level + 4, oldan, current, cache)
    } else if (old.isInstanceOf[SNode[_, _]]) {
      val oldsn = old.asInstanceOf[SNode[K, V]]
      val txn = READ_TXN(oldsn)
      if (txn eq NoTxn) {
        // The node is not frozen or marked for freezing.
        if ((oldsn.hash == hash) && ((oldsn.key eq key) || (oldsn.key == key))) {
          val sn = new SNode(hash, key, value)
          if (CAS_TXN(oldsn, sn)) {
            CAS(current, pos, oldsn, sn)
            // Note: must not increment count here.
            Success
          } else slowInsert(key, value, hash, level, current, parent, cache)
        } else if (usedLength(current) == 4) {
          // Expand the current node, aiming to avoid the collision.
          // Root size always 16, so parent is non-null.
          val parentmask = usedLength(parent) - 1
          val parentlevel = level - 4
          val parentpos = (hash >>> parentlevel) & parentmask
          val enode = new ENode(parent, parentpos, current, hash, level)
          if (CAS(parent, parentpos, current, enode)) {
            completeExpansion(cache, enode)
            val wide = READ_WIDE(enode)
            slowInsert(key, value, hash, level, wide, parent, cache)
          } else {
            slowInsert(key, value, hash, level, current, parent, cache)
          }
        } else {
          // Replace the single node with a narrow node.
          val nnode = newNarrowOrWideNode(
            oldsn.hash, oldsn.key, oldsn.value, hash, key, value, level + 4)
          if (CAS_TXN(oldsn, nnode)) {
            CAS(current, pos, oldsn, nnode)
            Success
          } else slowInsert(key, value, hash, level, current, parent, cache)
        }
      } else if (txn eq FSNode) {
        // We landed into the middle of another transaction.
        // We must restart from the top, find the transaction node and help.
        Restart
      } else {
        // The single node had been scheduled for replacement by some thread.
        // We need to help, then retry.
        CAS(current, pos, oldsn, txn)
        slowInsert(key, value, hash, level, current, parent, cache)
      }
    } else if (old.isInstanceOf[LNode[_, _]]) {
      val oldln = old.asInstanceOf[LNode[K, V]]
      val nn = newListNarrowOrWideNode(oldln, hash, key, value, level + 4)
      if (CAS(current, pos, oldln, nn)) Success
      else slowInsert(key, value, hash, level, current, parent, cache)
    } else if (old.isInstanceOf[ENode]) {
      // There is another transaction in progress, help complete it, then restart.
      val enode = old.asInstanceOf[ENode]
      completeExpansion(cache, enode)
      Restart
    } else if (old.isInstanceOf[XNode]) {
      // There is another transaction in progress, help complete it, then restart.
      val xnode = old.asInstanceOf[XNode]
      completeCompression(cache, xnode)
      Restart
    } else if ((old eq FVNode) || old.isInstanceOf[FNode]) {
      // We landed into the middle of some other thread's transaction.
      // We need to restart from the top to find the transaction's descriptor,
      // and if we find it, then help and restart once more.
      Restart
    } else {
      sys.error("Unexpected case -- " + old)
    }
  }

  def remove(key: K): V = {
    val hash = spread(key.hashCode)
    fastRemove(key, hash)
  }

  def fastRemove(key: K, hash: Int): V = {
    val cache = READ_CACHE
    val result = fastRemove(key, hash, cache, cache, 0)
    result.asInstanceOf[V]
  }

  @tailrec
  private def fastRemove(
    key: K, hash: Int, cache: Array[AnyRef], prevCache: Array[AnyRef], ascends: Int
  ): AnyRef = {
    if (cache == null) {
      slowRemove(key, hash)
    } else {
      val len = cache.length
      val mask = len - 1 - 1
      val pos = 1 + (hash & mask)
      val cachee = READ(cache, pos)
      val level = 31 - Integer.numberOfLeadingZeros(len - 1)
      // println("fast remove -- " + level)
      if (cachee eq null) {
        // Inconclusive -- must retry one cache level above.
        val stats = READ(cache, 0)
        val parentCache = stats.asInstanceOf[CacheNode].parent
        fastRemove(key, hash, parentCache, cache, ascends + 1)
      } else if (cachee.isInstanceOf[Array[AnyRef]]) {
        // Read from an array node.
        val an = cachee.asInstanceOf[Array[AnyRef]]
        val mask = usedLength(an) - 1
        val pos = (hash >>> level) & mask
        val old = READ(an, pos)
        if (old eq null) {
          // The key does not exist.
          if (ascends > 1) {
            recordCacheMiss()
          }
          null
        } else if (old.isInstanceOf[Array[AnyRef]]) {
          // Continue searching recursively.
          val oldan = old.asInstanceOf[Array[AnyRef]]
          val res = slowRemove(key, hash, level + 4, oldan, an, prevCache)
          if (res == Restart) fastRemove(key, hash, cache, prevCache, ascends)
          else res
        } else if (old.isInstanceOf[SNode[_, _]]) {
          val oldsn = old.asInstanceOf[SNode[K, V]]
          val txn = READ_TXN(oldsn)
          if (txn eq NoTxn) {
            // No other transaction in progress.
            if ((oldsn.hash == hash) && ((oldsn.key eq key) || (oldsn.key == key))) {
              // Remove the key.
              if (CAS_TXN(oldsn, null)) {
                CAS(an, pos, oldsn, null)
                decrementCount(an)
                if (ascends > 1) {
                  recordCacheMiss()
                }
                if (isCompressible(an)) {
                  compressDescend(rawRoot, null, hash, 0)
                }
                oldsn.value
              } else fastRemove(key, hash, cache, prevCache, ascends)
            } else {
              // The key does not exist.
              if (ascends > 1) {
                recordCacheMiss()
              }
              null
            }
          } else if (txn eq FSNode) {
            // Must restart from the root, to find the transaction node, and help.
            slowRemove(key, hash)
          } else {
            // Complete the current transaction, and retry.
            CAS(an, pos, oldsn, txn)
            fastRemove(key, hash, cache, prevCache, ascends)
          }
        } else {
          // Must restart from the root, to find the transaction node, and help.
          slowRemove(key, hash)
        }
      } else if (cachee.isInstanceOf[SNode[_, _]]) {
        // Need parent array node -- retry one cache level above.
        val stats = READ(cache, 0)
        val parentCache = stats.asInstanceOf[CacheNode].parent
        fastRemove(key, hash, parentCache, cache, ascends + 1)
      } else {
        sys.error(s"Unexpected case -- $cachee is not supposed to be cached.")
      }
    }
  }

  private[concurrent] def slowRemove(key: K): V = {
    val hash = spread(key.hashCode)
    slowRemove(key, hash)
  }

  private[concurrent] def slowRemove(key: K, hash: Int): V = {
    val node = rawRoot
    val cache = READ_CACHE
    var result: AnyRef = null
    do {
      result = slowRemove(key, hash, 0, node, null, cache)
    } while (result == Restart)
    result.asInstanceOf[V]
  }

  private def isCompressible(current: Array[AnyRef]): Boolean = {
    if (!doCompression) return false
    if (useCounters) {
      val count = READ(current, current.length - 1).asInstanceOf[Integer].intValue
      if (count > 1) {
        return false
      }
    }
    var found: AnyRef = null
    var i = 0
    while (i < usedLength(current)) {
      val old = READ(current, i)
      if (old != null) {
        if (found == null && old.isInstanceOf[SNode[_, _]]) {
          found = old
        } else {
          return false
        }
      }
      i += 1
    }
    true
  }

  private def compressSingleLevel(
    cache: Array[AnyRef], current: Array[AnyRef], parent: Array[AnyRef],
    hash: Int, level: Int
  ): Boolean = {
    if (parent == null) {
      return false
    }
    if (!isCompressible(current)) {
      return false
    }
    // It is likely that the node is compressible, so we freeze it and try to compress.
    val parentmask = usedLength(parent) - 1
    val parentpos = (hash >>> (level - 4)) & parentmask
    val xn = new XNode(parent, parentpos, current, hash, level)
    if (CAS(parent, parentpos, current, xn)) {
      completeCompression(cache, xn)
    } else {
      false
    }
  }

  private def compressAscend(
    cache: Array[AnyRef], current: Array[AnyRef], parent: Array[AnyRef],
    hash: Int, level: Int
  ): Unit = {
    val mustContinue = compressSingleLevel(cache, current, parent, hash, level)
    if (mustContinue) {
      // Continue compressing if possible.
      // TODO: Investigate if full ascend is feasible.
      compressDescend(rawRoot, null, hash, 0)
    }
  }

  private def compressDescend(
    current: Array[AnyRef], parent: Array[AnyRef], hash: Int, level: Int
  ): Boolean = {
    // Dive into the cache starting from the root for the given hash,
    // and compress as much as possible.
    val pos = (hash >>> level) & (usedLength(current) - 1)
    val old = READ(current, pos)
    if (old.isInstanceOf[Array[AnyRef]]) {
      val an = old.asInstanceOf[Array[AnyRef]]
      if (!compressDescend(an, current, hash, level + 4)) return false
    }
    // We do not care about maintaining the cache in the slow compression path,
    // so we just use the top-level cache.
    if (parent != null) {
      val cache = READ_CACHE
      return compressSingleLevel(cache, current, parent, hash, level)
    }
    return false
  }

  private def compressFrozen(frozen: Array[AnyRef], level: Int): AnyRef = {
    var single: AnyRef = null
    var i = 0
    while (i < usedLength(frozen)) {
      val old = READ(frozen, i)
      if (old != FVNode) {
        if (single == null && old.isInstanceOf[SNode[_, _]]) {
          // It is possible that this is the only entry in the array node.
          single = old
        } else {
          // There are at least 2 nodes that are not FVNode.
          // Unfortunately, the node was modified before it was completely frozen.
          if (usedLength(frozen) == 16) {
            val wide = createWideArray()
            sequentialTransfer(frozen, wide, level)
            sequentialFixCount(wide)
            return wide
          } else {
            // If the node is narrow, then it cannot have any children.
            val narrow = createNarrowArray()
            sequentialTransferNarrow(frozen, narrow, level)
            sequentialFixCount(narrow)
            return narrow
          }
        }
      }
      i += 1
    }
    if (single != null) {
      val oldsn = single.asInstanceOf[SNode[K, V]]
      single = new SNode(oldsn.hash, oldsn.key, oldsn.value)
    }
    return single
  }

  private def completeCompression(cache: Array[AnyRef], xn: XNode): Boolean = {
    val parent = xn.parent
    val parentpos = xn.parentpos
    val level = xn.level

    // First, freeze and compress the subtree below.
    val stale = xn.stale
    val compressed = freezeAndCompress(cache, stale, level)

    // Then, replace with the compressed version in the parent.
    if (CAS(parent, parentpos, xn, compressed)) {
      if (compressed == null) {
        decrementCount(parent)
      }
      return compressed == null || compressed.isInstanceOf[SNode[K, V]]
    }
    return false
  }

  private def completeCompressionAlt(cache: Array[AnyRef], xn: XNode): Boolean = {
    val parent = xn.parent
    val parentpos = xn.parentpos
    val level = xn.level

    // First, freeze the subtree below.
    val stale = xn.stale
    freeze(cache, stale)

    // Then, create a compressed version, and replace it in the parent.
    val compressed = compressFrozen(stale, level)
    if (CAS(parent, parentpos, xn, compressed)) {
      if (compressed == null) {
        decrementCount(parent)
      }
      return compressed == null || compressed.isInstanceOf[SNode[K, V]]
    }
    return false
  }

  @tailrec
  private def slowRemove(
    key: K, hash: Int, level: Int, current: Array[AnyRef], parent: Array[AnyRef],
    cache: Array[AnyRef]
  ): AnyRef = {
    // println("slow remove -- " + level)
    val mask = usedLength(current) - 1
    val pos = (hash >>> level) & mask
    val old = READ(current, pos)
    if (old eq null) {
      // The key does not exist.
      null
    } else if (old.isInstanceOf[Array[AnyRef]]) {
      // Repeat search at the next level.
      val oldan = old.asInstanceOf[Array[AnyRef]]
      slowRemove(key, hash, level + 4, oldan, current, cache)
    } else if (old.isInstanceOf[SNode[_, _]]) {
      val cacheLevel =
        if (cache == null) 0
        else 31 - Integer.numberOfLeadingZeros(cache.length - 1)
      if (level < cacheLevel || level >= cacheLevel + 8) {
        recordCacheMiss()
      }
      val oldsn = old.asInstanceOf[SNode[K, V]]
      val txn = READ_TXN(oldsn)
      if (txn eq NoTxn) {
        // There is no other transaction in progress.
        if ((oldsn.hash == hash) && ((oldsn.key eq key) || (oldsn.key == key))) {
          // The same key, remove it.
          if (CAS_TXN(oldsn, null)) {
            CAS(current, pos, oldsn, null)
            decrementCount(current)
            compressAscend(cache, current, parent, hash, level)
            oldsn.value.asInstanceOf[AnyRef]
          } else slowRemove(key, hash, level, current, parent, cache)
        } else {
          // The target key does not exist.
          null
        }
      } else if (txn eq FSNode) {
        // We landed into a middle of another transaction.
        // We must restart from the top, find the transaction node and help.
        Restart
      } else {
        // The single node had been scheduled for replacement by some thread.
        // We need to help and retry.
        CAS(current, pos, oldsn, txn)
        slowRemove(key, hash, level, current, parent, cache)
      }
    } else if (old.isInstanceOf[LNode[_, _]]) {
      val oldln = old.asInstanceOf[LNode[K, V]]
      val (result, nn) = newListNodeWithoutKey(oldln, hash, key)
      if (CAS(current, pos, oldln, nn)) result
      else slowRemove(key, hash, level, current, parent, cache)
    } else if (old.isInstanceOf[ENode]) {
      // There is another transaction in progress, help complete it, then restart.
      val enode = old.asInstanceOf[ENode]
      completeExpansion(cache, enode)
      Restart
    } else if (old.isInstanceOf[XNode]) {
      // There is another transaction in progress, help complete it, then restart.
      val xnode = old.asInstanceOf[XNode]
      completeCompression(cache, xnode)
      Restart
    } else if ((old eq FVNode) || old.isInstanceOf[FNode]) {
      // We landed into the middle of some other thread's transaction.
      // We need to restart above, from the descriptor.
      Restart
    } else {
      sys.error("Unexpected case -- " + old)
    }
  }

  private def isFrozenS(n: AnyRef): Boolean = {
    if (n.isInstanceOf[SNode[_, _]]) {
      val f = READ_TXN(n.asInstanceOf[SNode[_, _]])
      f eq FSNode
    } else false
  }

  private def isFrozenA(n: AnyRef): Boolean = {
    n.isInstanceOf[FNode] && n.asInstanceOf[FNode].frozen.isInstanceOf[Array[AnyRef]]
  }

  private def isFrozenL(n: AnyRef): Boolean = {
    n.isInstanceOf[FNode] && n.asInstanceOf[FNode].frozen.isInstanceOf[LNode[_, _]]
  }

  private def freezeAndCompress(
    cache: Array[AnyRef], current: Array[AnyRef], level: Int
  ): AnyRef = {
    var single: AnyRef = null
    var i = 0
    while (i < usedLength(current)) {
      val node = READ(current, i)
      if (node eq null) {
        // Freeze null.
        // If it fails, then either someone helped or another txn is in progress.
        // If another txn is in progress, then reinspect the current slot.
        if (!CAS(current, i, node, FVNode)) i -= 1
      } else if (node.isInstanceOf[SNode[_, _]]) {
        val sn = node.asInstanceOf[SNode[K, V]]
        val txn = READ_TXN(sn)
        if (txn eq NoTxn) {
          // Freeze single node.
          // If it fails, then either someone helped or another txn is in progress.
          // If another txn is in progress, then we must reinspect the current slot.
          if (!CAS_TXN(node.asInstanceOf[SNode[K, V]], FSNode)) i -= 1
          else {
            if (single == null) single = sn
            else single = current
          }
        } else if (txn eq FSNode) {
          // We can skip, another thread previously froze this node.
          single = current
        } else  {
          // Another thread is trying to replace the single node.
          // In this case, we help and retry.
          single = current
          CAS(current, i, node, txn)
          i -= 1
        }
      } else if (node.isInstanceOf[LNode[_, _]]) {
        // Freeze list node.
        // If it fails, then either someone helped or another txn is in progress.
        // If another txn is in progress, then we must reinspect the current slot.
        single = current
        val fnode = new FNode(node)
        CAS(current, i, node, fnode)
        i -= 1
      } else if (node.isInstanceOf[Array[AnyRef]]) {
        // Freeze the array node.
        // If it fails, then either someone helped or another txn is in progress.
        // If another txn is in progress, then reinspect the current slot.
        single = current
        val fnode = new FNode(node)
        CAS(current, i, node, fnode)
        i -= 1
      } else if (isFrozenL(node)) {
        // We can skip, another thread previously helped with freezing this node.
        single = current
      } else if (node.isInstanceOf[FNode]) {
        // We still need to freeze the subtree recursively.
        single = current
        val subnode = node.asInstanceOf[FNode].frozen.asInstanceOf[Array[AnyRef]]
        freeze(cache, subnode.asInstanceOf[Array[AnyRef]])
      } else if (node eq FVNode) {
        // We can continue, another thread already froze this slot.
        single = current
      } else if (node.isInstanceOf[ENode]) {
        // If some other txn is in progress, help complete it,
        // then restart from the current position.
        single = current
        val enode = node.asInstanceOf[ENode]
        completeExpansion(cache, enode)
        i -= 1
      } else if (node.isInstanceOf[XNode]) {
        // It some other txn is in progress, help complete it,
        // then restart from the current position.
        single = current
        val xnode = node.asInstanceOf[XNode]
        completeCompression(cache, xnode)
        i -= 1
      } else {
        sys.error("Unexpected case -- " + node)
      }
      i += 1
    }
    if (single.isInstanceOf[SNode[_, _]]) {
      val oldsn = single.asInstanceOf[SNode[K, V]]
      single = new SNode(oldsn.hash, oldsn.key, oldsn.value)
      return single
    } else if (single != null) {
      return compressFrozen(current, level)
    } else {
      return single
    }
  }

  private def freeze(cache: Array[AnyRef], current: Array[AnyRef]): Unit = {
    var i = 0
    while (i < usedLength(current)) {
      val node = READ(current, i)
      if (node eq null) {
        // Freeze null.
        // If it fails, then either someone helped or another txn is in progress.
        // If another txn is in progress, then reinspect the current slot.
        if (!CAS(current, i, node, FVNode)) i -= 1
      } else if (node.isInstanceOf[SNode[_, _]]) {
        val sn = node.asInstanceOf[SNode[K, V]]
        val txn = READ_TXN(sn)
        if (txn eq NoTxn) {
          // Freeze single node.
          // If it fails, then either someone helped or another txn is in progress.
          // If another txn is in progress, then we must reinspect the current slot.
          if (!CAS_TXN(node.asInstanceOf[SNode[K, V]], FSNode)) i -= 1
        } else if (txn eq FSNode) {
          // We can skip, another thread previously froze this node.
        } else  {
          // Another thread is trying to replace the single node.
          // In this case, we help and retry.
          CAS(current, i, node, txn)
          i -= 1
        }
      } else if (node.isInstanceOf[LNode[_, _]]) {
        // Freeze list node.
        // If it fails, then either someone helped or another txn is in progress.
        // If another txn is in progress, then we must reinspect the current slot.
        val fnode = new FNode(node)
        CAS(current, i, node, fnode)
        i -= 1
      } else if (node.isInstanceOf[Array[AnyRef]]) {
        // Freeze the array node.
        // If it fails, then either someone helped or another txn is in progress.
        // If another txn is in progress, then reinspect the current slot.
        val fnode = new FNode(node)
        CAS(current, i, node, fnode)
        i -= 1
      } else if (isFrozenL(node)) {
        // We can skip, another thread previously helped with freezing this node.
      } else if (node.isInstanceOf[FNode]) {
        // We still need to freeze the subtree recursively.
        val subnode = node.asInstanceOf[FNode].frozen.asInstanceOf[Array[AnyRef]]
        freeze(cache, subnode.asInstanceOf[Array[AnyRef]])
      } else if (node eq FVNode) {
        // We can continue, another thread already froze this slot.
      } else if (node.isInstanceOf[ENode]) {
        // If some other txn is in progress, help complete it,
        // then restart from the current position.
        val enode = node.asInstanceOf[ENode]
        completeExpansion(cache, enode)
        i -= 1
      } else if (node.isInstanceOf[XNode]) {
        // It some other txn is in progress, help complete it,
        // then restart from the current position.
        val xnode = node.asInstanceOf[XNode]
        completeCompression(cache, xnode)
        i -= 1
      } else {
        sys.error("Unexpected case -- " + node)
      }
      i += 1
    }
  }

  private def sequentialInsert(
    sn: SNode[K, V], wide: Array[AnyRef], level: Int
  ): Unit = {
    val mask = usedLength(wide) - 1
    val pos = (sn.hash >>> level) & mask
    if (wide(pos) == null) wide(pos) = sn
    else sequentialInsert(sn, wide, level, pos)
  }

  @tailrec
  private def sequentialInsert(
    sn: SNode[K, V], wide: Array[AnyRef], level: Int, pos: Int
  ): Unit = {
    val old = wide(pos)
    if (old.isInstanceOf[SNode[_, _]]) {
      val oldsn = old.asInstanceOf[SNode[K, V]]
      val an = newNarrowOrWideNodeUsingFreshThatNeedsCountFix(oldsn, sn, level + 4)
      wide(pos) = an
    } else if (old.isInstanceOf[Array[AnyRef]]) {
      val oldan = old.asInstanceOf[Array[AnyRef]]
      val npos = (sn.hash >>> (level + 4)) & (usedLength(oldan) - 1)
      if (oldan(npos) == null) {
        oldan(npos) = sn
      } else if (usedLength(oldan) == 4) {
        val an = createWideArray()
        sequentialTransfer(oldan, an, level + 4)
        wide(pos) = an
        sequentialInsert(sn, wide, level, pos)
      } else {
        sequentialInsert(sn, oldan, level + 4, npos)
      }
    } else if (old.isInstanceOf[LNode[_, _]]) {
      val oldln = old.asInstanceOf[LNode[K, V]]
      val nn = newListNarrowOrWideNode(oldln, sn.hash, sn.key, sn.value, level + 4)
      wide(pos) = nn
    } else {
      sys.error("Unexpected case: " + old)
    }
  }

  private def sequentialTransfer(
    source: Array[AnyRef], wide: Array[AnyRef], level: Int
  ): Unit = {
    val mask = usedLength(wide) - 1
    var i = 0
    while (i < usedLength(source)) {
      val node = source(i)
      if (node eq FVNode) {
        // We can skip, the slot was empty.
      } else if (isFrozenS(node)) {
        // We can copy it over to the wide node.
        val oldsn = node.asInstanceOf[SNode[K, V]]
        val sn = new SNode(oldsn.hash, oldsn.key, oldsn.value)
        val pos = (sn.hash >>> level) & mask
        if (wide(pos) == null) wide(pos) = sn
        else sequentialInsert(sn, wide, level, pos)
      } else if (isFrozenL(node)) {
        var tail = node.asInstanceOf[FNode].frozen.asInstanceOf[LNode[K, V]]
        while (tail != null) {
          val sn = new SNode(tail.hash, tail.key, tail.value)
          val pos = (sn.hash >>> level) & mask
          sequentialInsert(sn, wide, level, pos)
          tail = tail.next
        }
      } else if (node.isInstanceOf[FNode]) {
        val fn = node.asInstanceOf[FNode]
        val an = fn.frozen.asInstanceOf[Array[AnyRef]]
        sequentialTransfer(an, wide, level)
      } else {
        sys.error("Unexpected case -- source array node should have been frozen.")
      }
      i += 1
    }
  }

  private def sequentialTransferNarrow(
    source: Array[AnyRef], narrow: Array[AnyRef], level: Int
  ): Unit = {
    var i = 0
    while (i < 4) {
      val node = source(i)
      if (node eq FVNode) {
        // We can skipp, this slow was empty.
      } else if (isFrozenS(node)) {
        val oldsn = node.asInstanceOf[SNode[K, V]]
        val sn = new SNode(oldsn.hash, oldsn.key, oldsn.value)
        narrow(i) = sn
      } else if (isFrozenL(node)) {
        val chain = node.asInstanceOf[FNode].frozen.asInstanceOf[LNode[K, V]]
        narrow(i) = chain
      } else {
        sys.error(s"Unexpected case: $node")
      }
      i += 1
    }
  }

  private def newNarrowOrWideNode(
    h1: Int, k1: K, v1: V, h2: Int, k2: K, v2: V, level: Int
  ): AnyRef = {
    newNarrowOrWideNodeUsingFresh(
      new SNode(h1, k1, v1), new SNode(h2, k2, v2), level)
  }

  private def newNarrowOrWideNodeUsingFresh(
    sn1: SNode[K, V], sn2: SNode[K, V], level: Int
  ): AnyRef = {
    if (sn1.hash == sn2.hash) {
      val ln1 = new LNode(sn1)
      val ln2 = new LNode(sn2, ln1)
      ln2
    } else {
      val pos1 = (sn1.hash >>> level) & (4 - 1)
      val pos2 = (sn2.hash >>> level) & (4 - 1)
      if (pos1 != pos2) {
        val an = createNarrowArray()
        val pos1 = (sn1.hash >>> level) & (usedLength(an) - 1)
        an(pos1) = sn1
        val pos2 = (sn2.hash >>> level) & (usedLength(an) - 1)
        an(pos2) = sn2
        an(an.length - 1) = Integer.valueOf(2)
        an
      } else {
        val an = createWideArray()
        sequentialInsert(sn1, an, level)
        sequentialInsert(sn2, an, level)
        sequentialFixCount(an)
        an
      }
    }
  }

  private def newNarrowOrWideNodeUsingFreshThatNeedsCountFix(
    sn1: SNode[K, V], sn2: SNode[K, V], level: Int
  ): AnyRef = {
    if (sn1.hash == sn2.hash) {
      val ln1 = new LNode(sn1)
      val ln2 = new LNode(sn2, ln1)
      ln2
    } else {
      val pos1 = (sn1.hash >>> level) & (4 - 1)
      val pos2 = (sn2.hash >>> level) & (4 - 1)
      if (pos1 != pos2) {
        val an = createNarrowArray()
        val pos1 = (sn1.hash >>> level) & (usedLength(an) - 1)
        an(pos1) = sn1
        val pos2 = (sn2.hash >>> level) & (usedLength(an) - 1)
        an(pos2) = sn2
        an
      } else {
        val an = createWideArray()
        sequentialInsert(sn1, an, level)
        sequentialInsert(sn2, an, level)
        an
      }
    }
  }

  private def newNarrowOrWideNodeThatNeedsCountFix(
    h1: Int, k1: K, v1: V, h2: Int, k2: K, v2: V, level: Int
  ): AnyRef = {
    newNarrowOrWideNodeUsingFreshThatNeedsCountFix(
      new SNode(h1, k1, v1), new SNode(h2, k2, v2), level)
  }

  private def newListNodeWithoutKey(
    oldln: CacheTrie.LNode[K, V], hash: Int, k: K
  ): (V, CacheTrie.LNode[K, V]) = {
    var tail = oldln
    while (tail != null) {
      if (tail.key == k) {
        // Only reallocate list if the key must be removed.
        val result = tail.value
        var ln: LNode[K, V] = null
        tail = oldln
        while (tail != null) {
          if (tail.key != k) {
            ln = new LNode(tail.hash, tail.key, tail.value, ln)
          }
          tail = tail.next
        }
        return (result, ln)
      }
      tail = tail.next
    }
    return (null.asInstanceOf[V], oldln)
  }

  // TODO: Fix a corner-case in which must check if key is already in the list node.
  private def newListNarrowOrWideNode(
    oldln: CacheTrie.LNode[K, V], hash: Int, k: K, v: V, level: Int
  ): AnyRef = {
    var tail = oldln
    var ln: LNode[K, V] = null
    while (tail != null) {
      ln = new LNode(tail.hash, tail.key, tail.value, ln)
      tail = tail.next
    }
    if (ln.hash == hash) {
      new LNode(hash, k, v, ln)
    } else {
      val an = createWideArray()
      val pos1 = (ln.hash >>> level) & (usedLength(an) - 1)
      an(pos1) = ln
      val sn = new SNode(hash, k, v)
      sequentialInsert(sn, an, level)
      sequentialFixCount(an)
      an
    }
  }

  private def completeExpansion(cache: Array[AnyRef], enode: ENode): Unit = {
    val parent = enode.parent
    val parentpos = enode.parentpos
    val level = enode.level

    // First, freeze the subtree beneath the narrow node.
    val narrow = enode.narrow
    freeze(cache, narrow)

    // Second, populate the target array, and CAS it into the parent.
    var wide = createWideArray()
    sequentialTransfer(narrow, wide, level)
    sequentialFixCount(wide)
    // If this CAS fails, then somebody else already committed the wide array.
    if (!CAS_WIDE(enode, null, wide)) {
      wide = READ_WIDE(enode)
    }
    // We need to write the agreed value back into the parent.
    // If we failed, it means that somebody else succeeded.
    // If we succeeded, then we must update the cache.
    // Note that not all nodes will get cached from this site,
    // because some array nodes get created outside expansion
    // (e.g. when creating a node to resolve collisions in sequentialTransfer).
    if (CAS(parent, parentpos, enode, wide)) {
      inhabitCache(cache, wide, enode.hash, level)
    }
  }

  @tailrec
  private def inhabitCache(
    cache: Array[AnyRef], nv: AnyRef, hash: Int, cacheeLevel: Int
  ): Unit = {
    if (cache eq null) {
      // Only create the cache if the entry is at least level 12,
      // since the expectation on the number of elements is ~80.
      // This means that we can afford to create a cache with 256 entries.
      if (cacheeLevel >= 12) {
        val cn = createCacheArray(8)
        cn(0) = new CacheNode(null, 8)
        CAS_CACHE(null, cn)
        val newCache = READ_CACHE
        inhabitCache(newCache, nv, hash, cacheeLevel)
      }
    } else {
      val len = cache.length
      val cacheLevel = Integer.numberOfTrailingZeros(len - 1)
      if (cacheeLevel == cacheLevel) {
        val mask = len - 1 - 1
        val pos = 1 + (hash & mask)
        WRITE(cache, pos, nv)
      } else {
        // We have a cache level miss -- update statistics, and rebuild if necessary.
        // TODO: Probably not necessary here.
      }
    }
  }

  def sampleAndUpdateCache(cache: Array[AnyRef], stats: CacheNode): Unit = {
    // Sample the hash trie to estimate the level distribution.
    // Use an 8-byte histogram, total sample size must be less than 255.
    var histogram = 0L
    val sampleSize = 128
    val sampleType = 2
    var seed = Thread.currentThread.getId + System.identityHashCode(this)
    val levelOffset = 4
    (sampleType: @switch) match {
      case 0 =>
        var i = 0
        while (i < sampleSize) {
          seed = (seed * 0x5DEECE66DL + 0xBL) & ((1L << 48) - 1);
          val hash = (seed >>> 16).toInt
          @tailrec
          def sampleHash(node: Array[AnyRef], level: Int, hash: Int): Int = {
            val mask = usedLength(node) - 1
            val pos = (hash >>> level) & mask
            val child = READ(node, pos)
            if (child.isInstanceOf[Array[AnyRef]]) {
              sampleHash(child.asInstanceOf[Array[AnyRef]], level + 4, hash)
            } else {
              level + levelOffset
            }
          }
          val level = sampleHash(rawRoot, 0, hash)
          val shift = (level >>> 2) << 3
          val addend = 1L << shift
          histogram += addend
          i += 1
        }
      case 1 =>
        var i = 0
        while (i < sampleSize) {
          seed = (seed * 0x5DEECE66DL + 0xBL) & ((1L << 48) - 1);
          val hash = (seed >>> 16).toInt
          def sampleKey(node: Array[AnyRef], level: Int, hash: Int): Int = {
            val mask = usedLength(node) - 1
            val pos = (hash >>> level) & mask
            var i = (pos + 1) % usedLength(node)
            while (i != pos) {
              val ch = READ(node, i)
              if (ch.isInstanceOf[SNode[_, _]] || isFrozenS(ch) || isFrozenL(ch)) {
                return level + levelOffset
              } else if (ch.isInstanceOf[Array[AnyRef]]) {
                val an = ch.asInstanceOf[Array[AnyRef]]
                val result = sampleKey(an, level + 4, hash)
                if (result != -1) return result
              } else if (isFrozenA(ch)) {
                val an = ch.asInstanceOf[FNode].frozen.asInstanceOf[Array[AnyRef]]
                val result = sampleKey(an, level + 4, hash)
                if (result != -1) return result
              }
              i = (i + 1) % usedLength(node)
            }
            -1
          }
          val level = sampleKey(rawRoot, 0, hash)
          if (level == -1) i = sampleSize
          else {
            val shift = (level >>> 2) << 3
            val addend = 1L << shift
            histogram += addend
            i += 1
          }
        }
      case 2 =>
        def count(histogram: Long): Int = {
          (
            ((histogram >>> 0) & 0xff) +
            ((histogram >>> 8) & 0xff) +
            ((histogram >>> 16) & 0xff) +
            ((histogram >>> 24) & 0xff) +
            ((histogram >>> 32) & 0xff) +
            ((histogram >>> 40) & 0xff) +
            ((histogram >>> 48) & 0xff) +
            ((histogram >>> 56) & 0xff)
          ).toInt
        }
        def sampleUnbiased(
          node: Array[AnyRef], level: Int, maxRepeats: Int, maxSamples: Int,
          startHistogram: Long, startSeed: Long
        ): Long = {
          var seed = startSeed
          var histogram = startHistogram
          val mask = usedLength(node) - 1
          var i = 0
          while (i < maxRepeats && count(histogram) < maxSamples) {
            seed = (seed * 0x5DEECE66DL + 0xBL) & ((1L << 48) - 1);
            val hash = (seed >>> 16).toInt
            val pos = hash & mask
            val ch = READ(node, pos)
            if (ch.isInstanceOf[Array[AnyRef]]) {
              val an = ch.asInstanceOf[Array[AnyRef]]
              histogram += sampleUnbiased(
                an, level + 4, math.min(maxSamples, maxRepeats * 4), maxSamples,
                histogram, seed + 1
              )
            } else if (
              ch.isInstanceOf[SNode[_, _]] || isFrozenS(ch) || isFrozenL(ch)
            ) {
              val shift = ((level + levelOffset) >>> 2) << 3
              histogram += 1L << shift
            } else if (isFrozenA(ch)) {
              val an = ch.asInstanceOf[FNode].frozen.asInstanceOf[Array[AnyRef]]
              histogram += sampleUnbiased(
                an, level + 4, maxRepeats * 4, maxSamples, histogram, seed + 1
              )
            }
            i += 1
          }
          histogram
        }
        var i = 0
        val trials = 32
        while (i < trials) {
          seed += 1
          histogram += sampleUnbiased(rawRoot, 0, 1, sampleSize / trials, 0L, seed)
          i += 1
        }
    }

    // Find two consecutive levels with most elements.
    // Additionally, record the number of elements at the current cache level.
    val oldCacheLevel = stats.level
    var cacheCount = 0
    var bestLevel = 0
    var bestCount = (histogram & 0xff) + ((histogram >>> 8) & 0xff)
    var level = 8
    while (level < 64) {
      val count =
        ((histogram >>> level) & 0xff) + ((histogram >>> (level + 8)) & 0xff)
      if (count > bestCount) {
        bestCount = count
        bestLevel = level >> 1
      }
      if ((level >> 1) == oldCacheLevel) {
        cacheCount += count.toInt
      }
      level += 8
    }

    // Debug information.
    def printDebugInformation() {
      println(debugPerLevelDistribution)
      println(s"best level:  ${bestLevel} (count: $bestCount)")
      println(s"cache level: ${stats.level} (count: $cacheCount)")
      val histogramString =
        (0 until 8).map(_ * 8).map(histogram >>> _).map(_ & 0xff).mkString(",")
      println(histogramString)
      println(debugCacheStats)
      println()
    }
    // printDebugInformation()

    // Decide whether to change the cache levels.
    val repairThreshold = 1.40f
    if (cacheCount * repairThreshold < bestCount) {
      // printDebugInformation()
      var currCache = cache
      var currStats = stats
      while (currStats.level > bestLevel) {
        // Drop cache level.
        val parentCache = currStats.parent
        if (CAS_CACHE(currCache, parentCache)) {
          if (parentCache == null) {
            return
          }
          currCache = parentCache
          currStats = READ(parentCache, 0).asInstanceOf[CacheNode]
        } else {
          // Bail out immediately -- cache will be repaired by someone else eventually.
          return
        }
      }
      while (currStats.level < bestLevel) {
        // Add cache level.
        val nextLevel = currStats.level + 4
        val nextCache = createCacheArray(nextLevel)
        nextCache(0) = new CacheNode(currCache, nextLevel)
        if (CAS_CACHE(currCache, nextCache)) {
          currCache = nextCache
          currStats = READ(nextCache, 0).asInstanceOf[CacheNode]
        } else {
          // Bail our immediately -- cache will be repaired by someone else eventually.
          return
        }
      }
    }
  }

  private def recordCacheMiss(): Unit = {
    val missCountMax = 2048
    val cache = READ_CACHE
    if (cache ne null) {
      val stats = READ(cache, 0).asInstanceOf[CacheNode]
      if (stats.approximateMissCount > missCountMax) {
        // We must again check if the cache level is obsolete.
        // Reset the miss count.
        stats.resetMissCount()

        // Resample to find out if cache needs to be repaired.
        sampleAndUpdateCache(cache, stats)
      } else {
        stats.bumpMissCount()
      }
    }
  }

  private[concurrent] def debugReadCache: Array[AnyRef] = READ_CACHE

  private[concurrent] def debugReadRoot: Array[AnyRef] = rawRoot

  private[concurrent] def debugCachePopulateTwoLevelSingle(
    level: Int, key: K, value: V
  ): Unit = {
    rawCache = createCacheArray(level)
    rawCache(0) = new CacheNode(null, level)
    var i = 1
    while (i < rawCache.length) {
      val an = createNarrowArray()
      rawCache(i) = an
      var j = 0
      while (j < usedLength(an)) {
        an(j) = new SNode(0, key, value)
        j += 1
      }
      sequentialFixCount(an)
      i += 1
    }
  }

  private[concurrent] def debugCachePopulateTwoLevel(
    level: Int, keys: Array[K], values: Array[V]
  ): Unit = {
    rawCache = createCacheArray(level)
    rawCache(0) = new CacheNode(null, level)
    var i = 1
    while (i < rawCache.length) {
      val an = createNarrowArray()
      rawCache(i) = an
      var j = 0
      while (j < usedLength(an)) {
        an(j) = new SNode(0, keys(i * 4 + j), values(i * 4 + j))
        j += 1
      }
      sequentialFixCount(an)
      i += 1
    }
  }

  private[concurrent] def debugCachePopulateOneLevel(
    level: Int, keys: Array[K], values: Array[V], scarce: Boolean
  ): Unit = {
    rawCache = createCacheArray(level)
    rawCache(0) = new CacheNode(null, level)
    var i = 1
    while (i < rawCache.length) {
      if (!scarce || i % 4 == 0) {
        rawCache(i) = new SNode(0, keys(i), values(i))
      }
      i += 1
    }
  }

  private[concurrent] def debugLoadFactor(): Double = {
    var full = 0
    var total = 0
    def traverse(node: Array[AnyRef]): Unit = {
      total += usedLength(node)
      var i = 0
      while (i < usedLength(node)) {
        val old = READ(node, i)
        if (old.isInstanceOf[SNode[_, _]]) {
          full += 1
        } else if (old.isInstanceOf[LNode[_, _]]) {
          full += 1
        } else if (old.isInstanceOf[Array[AnyRef]]) {
          traverse(old.asInstanceOf[Array[AnyRef]])
        }
        i += 1
      }
    }
    traverse(rawRoot)
    return 1.0 * full / total
  }

  private[concurrent] def debugTree: String = {
    val res = new StringBuilder
    def traverse(indent: String, node: Array[AnyRef]): Unit = {
      var i = 0
      while (i < usedLength(node)) {
        val old = READ(node, i)
        if (old == null) {
          res.append(s"${indent}<empty>")
          res.append("\n")
        } else if (old.isInstanceOf[SNode[_, _]]) {
          val sn = old.asInstanceOf[SNode[K, V]]
          res.append(s"${indent}")
          val txn = READ_TXN(sn)
          val marker = if (txn eq NoTxn) "_" else txn.toString
          val id = System.identityHashCode(sn)
          res.append(
            s"SN[${Integer.toHexString(sn.hash)}:${sn.key}:${sn.value}:$marker]@$id")
          res.append("\n")
        } else if (old.isInstanceOf[LNode[_, _]]) {
          var ln = old.asInstanceOf[LNode[K, V]]
          while (ln != null) {
            res.append(s"${indent}")
            res.append(s"LN[${Integer.toHexString(ln.hash)}:${ln.key}:${ln.value}]")
            res.append("->")
            ln = ln.next
          }
          res.append("\n")
        } else if (old.isInstanceOf[Array[AnyRef]]) {
          val an = old.asInstanceOf[Array[AnyRef]]
          res.append(s"${indent}${if (usedLength(an) == 4) "narrow" else "wide"}")
          res.append("\n")
          traverse(indent + "  ", an)
        } else {
          res.append("unsupported case: " + old)
        }
        i += 1
      }
    }
    traverse("", rawRoot)
    res.toString
  }

  def debugCacheStats: String = {
    def traverse(cache: Array[AnyRef]): String = {
      if (cache == null) {
        return "empty cache"
      }
      val stats = cache(0).asInstanceOf[CacheNode]
      var count = 0
      var acount = 0
      var scount = 0
      for (i <- 1 until cache.length) {
        val c = cache(i)
        if (c != null && c != FVNode && !c.isInstanceOf[FNode]) {
          count += 1
        }
        if (c.isInstanceOf[Array[AnyRef]]) {
          acount += 1
        }
        if (c.isInstanceOf[SNode[_, _]]) {
          scount += 1
        }
      }
      traverse(stats.parent) + "\n|\n" + s"""
      |cache level: ${stats.level}, $count / ${cache.length - 1}
      |a-nodes: $acount
      |s-nodes: $scount
      """.stripMargin.trim
    }

    val cache = READ_CACHE
    "----\n" + traverse(cache) + "\n----"
  }

  def debugPerLevelDistribution: String = {
    val histogram = new Array[Int](10)
    var sz = 0
    def traverse(node: Array[AnyRef], level: Int): Unit = {
      var i = 0
      while (i < usedLength(node)) {
        val old = node(i)
        if (old.isInstanceOf[SNode[_, _]]) {
          histogram((level + 4) / 4) += 1
          sz += 1
        } else if (old.isInstanceOf[LNode[_, _]]) {
          var ln = old.asInstanceOf[LNode[_, _]]
          while (ln != null) {
            histogram((level + 4) / 4) += 1
            sz += 1
            ln = ln.next
          }
        } else if (old.isInstanceOf[Array[AnyRef]]) {
          val an = old.asInstanceOf[Array[AnyRef]]
          traverse(an, level + 4)
        } else if (old eq null) {
        } else {
          sys.error(s"Unexpected case: $old")
        }
        i += 1
      }
    }
    traverse(this.debugReadRoot, 0)
    val sb = new StringBuilder
    sb.append(s":: size $sz ::\n")
    for (i <- 0 until histogram.length) {
      val num = histogram(i)
      val percent = (100.0 * num / sz).toInt
      sb.append(f"${i * 4}%3d: $num%8d ($percent%3d%%) ${"*" * (num * 40 / sz)}\n")
    }
    sb.toString
  }

  private[concurrent] def assertCorrectCounts(): Unit = {
    def traverse(node: Array[AnyRef]): Unit = {
      var i = 0
      var count = 0
      while (i < usedLength(node)) {
        val old = node(i)
        if (old != null) {
          count += 1
        }
        if (old.isInstanceOf[Array[AnyRef]]) {
          traverse(old.asInstanceOf[Array[AnyRef]])
        }
        i += 1
      }
      assert(count == node(node.length - 1).asInstanceOf[Integer],
        s"Counted $count, node: ${ANode.toString(node)}")
    }
    traverse(rawRoot)
  }
}


object CacheTrie {
  private val ArrayBase = Platform.unsafe.arrayBaseOffset(classOf[Array[AnyRef]])
  private val ArrayShift = {
    val scale = Platform.unsafe.arrayIndexScale(classOf[Array[AnyRef]])
    require((scale & (scale - 1)) == 0)
    31 - Integer.numberOfLeadingZeros(scale)
  }
  private val ENodeWideOffset = {
    val field = classOf[ENode].getDeclaredField("wide")
    Platform.unsafe.objectFieldOffset(field)
  }
  private val SNodeFrozenOffset = {
    val field = classOf[SNode[_, _]].getDeclaredField("txn")
    Platform.unsafe.objectFieldOffset(field)
  }
  private val CacheTrieRawCacheOffset = {
    val field = classOf[CacheTrie[_, _]].getDeclaredField("rawCache")
    Platform.unsafe.objectFieldOffset(field)
  }
  private val availableProcessors = Runtime.getRuntime.availableProcessors()

  /* result types */

  val Success = new AnyRef

  val Restart = new AnyRef

  /* node types */

  object NoTxn

  class SNode[K <: AnyRef, V](
    @volatile var txn: AnyRef,
    val hash: Int,
    val key: K,
    val value: V
  ) {
    def this(h: Int, k: K, v: V) = this(NoTxn, h, k, v)
    override def toString = {
      val id = System.identityHashCode(this)
      s"SN[$hash, $key, $value, ${if (txn != NoTxn) txn else '_'}]@$id"
    }
  }

  class LNode[K <: AnyRef, V](
    val hash: Int,
    val key: K,
    val value: V,
    val next: LNode[K, V]
  ) {
    def this(sn: SNode[K, V], next: LNode[K, V]) = this(sn.hash, sn.key, sn.value, next)
    def this(sn: SNode[K, V]) = this(sn, null)
    override def toString = s"LN[$hash, $key, $value] -> $next"
  }

  class ENode(
    val parent: Array[AnyRef],
    val parentpos: Int,
    val narrow: Array[AnyRef],
    val hash: Int,
    val level: Int
  ) {
    @volatile var wide: Array[AnyRef] = null
    override def toString = s"EN"
  }

  class XNode(
    val parent: Array[AnyRef],
    val parentpos: Int,
    val stale: Array[AnyRef],
    val hash: Int,
    val level: Int
  ) {
    override def toString = s"XN"
  }

  object ANode {
    def toString(an: Array[AnyRef]) = an.mkString("AN[", ", ", "]")
  }

  val FVNode = new AnyRef

  val FSNode = new AnyRef

  class FNode(
    val frozen: AnyRef
  )

  class CacheNode(val parent: Array[AnyRef], val level: Int) {
    val missCounts = new Array[Int](availableProcessors * math.min(16, level))

    private def pos: Int = {
      val id = Thread.currentThread.getId
      val pos = (id ^ (id >>> 16)).toInt & (missCounts.length - 1)
      pos
    }

    final def approximateMissCount: Int = {
      missCounts(0)
    }

    final def resetMissCount(): Unit = {
      missCounts(0) = 0
    }

    final def bumpMissCount(): Unit = {
      missCounts(0) += 1
    }
  }
}
