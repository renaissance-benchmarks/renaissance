package io.reactors.common.concurrent



import sun.misc.Unsafe
import scala.annotation.switch
import scala.annotation.tailrec



class ByteswapTree[K <: AnyRef: Ordering, V <: AnyRef] {
  import ByteswapTree._

  private val ordering = implicitly[Ordering[K]]
  @volatile private var root: Node = new Leaf

  private def unsafe: Unsafe = Platform.unsafe

  private def SLOT_MASK: Long = 0xfL

  private def COUNT_SHIFT: Int = 60

  private def READ_MASK(leaf: Leaf): Long = {
    unsafe.getLongVolatile(leaf, LeafMaskOffset)
  }

  private def CAS_MASK(leaf: Leaf, ov: Long, nv: Long): Boolean = {
    unsafe.compareAndSwapLong(leaf, LeafMaskOffset, ov, nv)
  }

  private def READ_ENTRY(leaf: Leaf, idx: Long): AnyRef = {
    unsafe.getObjectVolatile(leaf, LeafEntryOffset + idx * LeafEntryScaling)
  }

  private def CAS_ENTRY(
    leaf: Leaf, idx: Int, ov: AnyRef, nv: AnyRef
  ): Boolean = {
    unsafe.compareAndSwapObject(leaf, LeafEntryOffset + idx * LeafEntryScaling, ov, nv)
  }

  private def insert(k: K, v: V): Unit = {
    ???
  }

  private[concurrent] def debugLeafInsert(k: K, v: V): Boolean = {
    val leaf = root.asInstanceOf[Leaf]
    insert(leaf, k, v)
  }

  private[concurrent] def debugLeaf: Leaf = root.asInstanceOf[Leaf]

  private[concurrent] def assertLeafInvariants(
    msg: String = "", check: (Int, AnyRef) => Unit
  ): Unit = {
    val leaf = root.asInstanceOf[Leaf]
    val mask = READ_MASK(leaf)
    val count = (mask >>> COUNT_SHIFT).toInt
    for (i <- 0 until count)
      assert(READ_ENTRY(leaf, i) != null, s"$msg: entry missing at $i")
    for (i <- 0 until count) {
      val idx = (mask >>> (i << 2)) & SLOT_MASK
      val entry = READ_ENTRY(leaf, idx)
      assert(entry != null, s"$msg: $i-th index $idx is empty")
      check(i, entry)
    }
  }

  @tailrec
  private def insert(leaf: Leaf, k: K, v: V): Boolean = {
    // Determine node state.
    val mask = READ_MASK(leaf)
    val count = (mask >>> COUNT_SHIFT).toInt

    if (count == 0 && mask != 0) {
      // The leaf was frozen.
      return false
    }

    // Attempt to propose the next entry.
    val entry = new Item(k, v)
    if (!CAS_ENTRY(leaf, count, null, entry)) {
      // Help complete the insertion of an already proposed key.
      val otherEntry = READ_ENTRY(leaf, count)
      if (otherEntry.isInstanceOf[Item[_, _]]) {
        val otherKey = otherEntry.asInstanceOf[Item[K, V]].key
        helpInsert(leaf, otherKey, mask, count)
      } else {
        val otherFrozen = otherEntry.asInstanceOf[Frozen]
        helpFreeze(otherFrozen)
      }

      // Retry.
      insert(leaf, k, v)
    } else {
      helpInsert(leaf, k, mask, count)
    }
  }

  @tailrec
  private def helpInsert(leaf: Leaf, k: K, mask: Long, count: Int): Boolean = {
    val removedCount = java.lang.Long.numberOfLeadingZeros(~(mask << 4)) >> 2
    val liveCount = count - removedCount

    // Determine the position for the key, and whether to replace an old key.
    var existing = false
    var left = 0
    var right = liveCount - 1
    while (left <= right) {
      val m = (left + right) >> 1
      val midx = (mask >>> (m << 2)) & SLOT_MASK
      val entry = READ_ENTRY(leaf, midx).asInstanceOf[Item[K, V]]
      val comparison = ordering.compare(entry.key, k)
      if (comparison < 0) left = m + 1
      else if (comparison > 0) right = m - 1
      else {
        left = m
        right = -1
        existing = k == entry.key
      }
    }
    val index = left.toLong

    // Determine the new mask.
    var newMask: Long = 0L
    if (existing) {
      newMask |= (count + 1L) << COUNT_SHIFT
      val removedBits = (removedCount + 1L) << 2
      newMask |= ((1L << removedBits) - 1) << (60 - removedBits)
      val permutationBits = (1 << (liveCount << 2)) - 1
      newMask |= permutationBits & ~(0xfL << (index << 2))
      newMask |= count.toLong << (index << 2)
    } else {
      newMask |= (count + 1L) << COUNT_SHIFT
      val removedBits = removedCount.toLong << 2
      newMask |= ((1L << removedBits) - 1) << (60 - removedBits)
      val suffixLength = liveCount - index
      val suffixBits = ((1L << (suffixLength << 2)) - 1) << (index << 2)
      newMask |= (mask & suffixBits) << 4
      newMask |= count.toLong << (index << 2)
      val prefixBits = ((1L << (index << 2)) - 1)
      newMask |= mask & prefixBits
    }

    // Try to commit the proposed entry.
    if (CAS_MASK(leaf, mask, newMask)) {
      // Successfully added the key.
      // Done.
      return true
    } else {
      // A concurrent operation. There are 2 possibilities:
      // (a) Somebody else completed this insertion. In this case, we are done.
      // (b) Somebody else removed an entry from this leaf. In this case, we retry.
      val postMask = READ_MASK(leaf)
      val postCount = (postMask >>> COUNT_SHIFT).toInt
      if (postCount == 0 && postMask != 0) {
        // a1) Was frozen.
        // Done.
        return true
      } else if (postCount > count) {
        // a2) Insertion was completed.
        // Done.
        return true
      } else {
        // b) The count was not yet incremented.
        // Retry.
        helpInsert(leaf, k, postMask, postCount)
      }
    }
  }

  private def helpFreeze(frozen: Frozen) {
    ???
  }
}


object ByteswapTree {
  private def offset(cls: Class[_], fieldName: String): Long = {
    val field = cls.getDeclaredField(fieldName)
    Platform.unsafe.objectFieldOffset(field)
  }

  private[concurrent] val LeafMaskOffset = offset(classOf[Leaf], "mask")
  private[concurrent] val LeafEntryOffset = offset(classOf[Leaf], "entry0")
  private[concurrent] val LeafEntryScaling =
    offset(classOf[Leaf], "entry1") - offset(classOf[Leaf], "entry0")
  private[concurrent] val InnerMaskOffset = offset(classOf[Inner], "mask")
  private[concurrent] val InnerEntryOffset = offset(classOf[Inner], "entry0")
  private[concurrent] val InnerEntryScaling =
    offset(classOf[Inner], "entry1") - offset(classOf[Inner], "entry0")
  private[concurrent] val InnerKeyOffset = offset(classOf[Inner], "key0")
  private[concurrent] val InnerKeyScaling =
    offset(classOf[Inner], "key1") - offset(classOf[Inner], "key0")

  private def layoutCheck(cls: Class[_], rootName: String): Unit = {
    def offset(fieldName: String): Long = {
      val field = cls.getDeclaredField(fieldName)
      Platform.unsafe.objectFieldOffset(field)
    }

    val firstOffset = offset(rootName + "0")
    val scalingFactor = offset(rootName + "1") - firstOffset

    def compareOffsets(idx: Int, fieldName: String): Unit = {
      val entryOffset = offset(fieldName)
      val expectedOffset = firstOffset + idx * scalingFactor
      if (entryOffset != expectedOffset) {
        throw new RuntimeException(
          s"Assumptions about layout are not met by this VM in $cls. " +
          s"Field $fieldName is at offset $entryOffset, expected $expectedOffset.")
      }
    }

    for (i <- 1 until 15) {
      compareOffsets(i, rootName + i)
    }
  }

  layoutCheck(classOf[Leaf], "entry")
  layoutCheck(classOf[Inner], "entry")
  layoutCheck(classOf[Inner], "key")

  abstract class Node

  class Leaf extends Node {
    @volatile var mask: Long = 0
    @volatile var unused0: AnyRef = null
    @volatile var entry0: AnyRef = null
    @volatile var entry1: AnyRef = null
    @volatile var entry2: AnyRef = null
    @volatile var entry3: AnyRef = null
    @volatile var entry4: AnyRef = null
    @volatile var entry5: AnyRef = null
    @volatile var entry6: AnyRef = null
    @volatile var entry7: AnyRef = null
    @volatile var entry8: AnyRef = null
    @volatile var entry9: AnyRef = null
    @volatile var entry10: AnyRef = null
    @volatile var entry11: AnyRef = null
    @volatile var entry12: AnyRef = null
    @volatile var entry13: AnyRef = null
    @volatile var entry14: AnyRef = null

    override def toString = {
      s"Leaf(${mask.toBinaryString}, $entry0, $entry1, $entry2, $entry3, $entry4, " +
      s"$entry5, $entry6, $entry7, $entry8, $entry9, $entry10, $entry11, $entry12, " +
      s"$entry13, $entry14)"
    }
  }

  class Inner extends Node {
    @volatile var mask: Long = 0
    @volatile var unused0: AnyRef = null
    @volatile var entry0: AnyRef = null
    @volatile var entry1: AnyRef = null
    @volatile var entry2: AnyRef = null
    @volatile var entry3: AnyRef = null
    @volatile var entry4: AnyRef = null
    @volatile var entry5: AnyRef = null
    @volatile var entry6: AnyRef = null
    @volatile var entry7: AnyRef = null
    @volatile var entry8: AnyRef = null
    @volatile var entry9: AnyRef = null
    @volatile var entry10: AnyRef = null
    @volatile var entry11: AnyRef = null
    @volatile var entry12: AnyRef = null
    @volatile var entry13: AnyRef = null
    @volatile var entry14: AnyRef = null
    @volatile var key0: AnyRef = null
    @volatile var key1: AnyRef = null
    @volatile var key2: AnyRef = null
    @volatile var key3: AnyRef = null
    @volatile var key4: AnyRef = null
    @volatile var key5: AnyRef = null
    @volatile var key6: AnyRef = null
    @volatile var key7: AnyRef = null
    @volatile var key8: AnyRef = null
    @volatile var key9: AnyRef = null
    @volatile var key10: AnyRef = null
    @volatile var key11: AnyRef = null
    @volatile var key12: AnyRef = null
    @volatile var key13: AnyRef = null
    @volatile var key14: AnyRef = null
  }

  class Item[K <: AnyRef, V <: AnyRef](val key: K, val value: V) {
    override def toString = s"<$key, $value>"
  }

  class Frozen {
    override def toString = "Frozen"
  }
}
