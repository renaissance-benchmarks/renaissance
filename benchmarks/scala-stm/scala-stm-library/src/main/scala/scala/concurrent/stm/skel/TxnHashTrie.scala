/* scala-stm - (c) 2009-2011, Stanford University, PPL */

package scala.concurrent.stm
package skel

import annotation.tailrec

/** `TxnHashTrie` implements a transactional mutable hash trie using Ref-s,
 *  with lazy cloning to allow efficient snapshots.  Fundamental operations are
 *  provided for hash tries representing either sets or maps, both of which are
 *  represented as a Ref.View[Node[A, B]].  If the initial empty leaf is
 *  `emptySetValue` then no values can be stored in the hash trie, and
 *  operations that take or return values will expect and produce null.
 *
 *  @author Nathan Bronson
 */
private[skel] object TxnHashTrie {

  final val LogBF = 4
  final val BF = 16

  // It would seem that the leaf copying is inefficient when compared to a tree
  // that allows more sharing, but a back-of-the-envelope calculation indicates
  // that the crossover point for the total bytes allocates to construct an
  // immutable node holding N elements is about 12.  Even at N=32 the total
  // bytes required by this Leaf implementation is only about 2/3 more than an
  // ideal balanced tree, and those bytes are accessed in a more cache friendly
  // fashion.
  final val MaxLeafCapacity = 14

  def keyHash[A](key: A): Int = if (key == null) 0 else mixBits(key.##)

  def mixBits(h: Int) = {
    // make sure any bit change results in a change in the bottom LogBF bits
    val s = LogBF
    val x = h ^ (h >>> (s * 3)) ^ (h >>> (s * 6))
    x ^ (x >>> s) ^ (x >>> (s * 2))
  }

  def indexFor(shift: Int, hash: Int) = (hash >>> shift) & (BF - 1)

  //////// shared instances
  
  val emptyLeaf = new Leaf[Any, Unit](Array.empty[Int], Array.empty[AnyRef])

  //////// publicly-visible stuff

  sealed abstract class Node[A, B] {
    def cappedSize(cap: Int): Int
    def txnIsEmpty(implicit txn: InTxn): Boolean
    def keyForeach[U](f: A => U)
    def mapForeach[U](f: ((A, B)) => U)
    def keyIterator: Iterator[A]
    def valueIterator: Iterator[B]
    def mapIterator: Iterator[(A, B)]
  }

  sealed trait BuildingNode[A, B] {
    def endBuild: Node[A, B]
  }

  type SetNode[A] = Node[A, AnyRef]
  type SetBuildingNode[A] = BuildingNode[A, AnyRef]

  /** If used by a Set, values will be null. */
  final class Leaf[A, B](val hashes: Array[Int],
                         val kvs: Array[AnyRef]) extends Node[A, B] with BuildingNode[A, B] {

    def endBuild = this

    def cappedSize(cap: Int): Int = hashes.length
    def txnIsEmpty(implicit txn: InTxn) = hashes.length == 0

    def getKey(i: Int): A = kvs(2 * i).asInstanceOf[A]
    def setKey(i: Int, k: A) { kvs(2 * i) = k.asInstanceOf[AnyRef] }

    def getValue(i: Int): B = kvs(2 * i + 1).asInstanceOf[B]
    def setValue(i: Int, v: B) { kvs(2 * i + 1) = v.asInstanceOf[AnyRef] }

    def getKeyValue(i: Int): (A, B) = (getKey(i), getValue(i))

    def contains(hash: Int, key: A): Boolean = find(hash, key) >= 0

    def get(hash: Int, key: A): Option[B] = {
      val i = find(hash, key)
      if (i < 0)
        None
      else
        Some(getValue(i))
    }

    def get(i: Int): Option[B] = {
      if (i < 0)
        None
      else
        Some(getValue(i))
    }

    def find(hash: Int, key: A): Int = {
      var i = hashes.length
      while (i > 0) {
        i -= 1
        val h = hashes(i)
        if (h == hash && keyEqual(key.asInstanceOf[AnyRef], kvs(2 * i)))
          return i
        if (h < hash)
          return ~(i + 1)
      }
      return ~0
    }

    private def keyEqual(lhs: AnyRef, rhs: AnyRef): Boolean = {
      if (lhs eq rhs)
        true
      else if (lhs == null || rhs == null)
        false
      else if (lhs.getClass eq rhs.getClass) {
        if (lhs.isInstanceOf[java.lang.Integer])
          true // we know the hashes match, and hashCode() = value for ints
        else if (lhs.isInstanceOf[java.lang.Long])
          lhs.asInstanceOf[java.lang.Long].longValue == rhs.asInstanceOf[java.lang.Long].longValue
        else
          lhs.equals(rhs)
      } else
        runtime.BoxesRunTime.equals2(lhs, rhs)
    }

    def noChange[B](i: Int, value: B): Boolean = {
      i >= 0 && (kvs(2 * i + 1) eq value.asInstanceOf[AnyRef])
    }

    def withPut(gen: Long, shift: Int, hash: Int, key: A, value: B, i: Int, contended: Boolean): Node[A, B] = {
      if (i < 0)
        withInsert(~i, hash, key, value).splitIfNeeded(gen, shift, contended: Boolean)
      else
        withUpdate(i, value)
    }

    def withBuildingPut(shift: Int, hash: Int, key: A, value: B, i: Int): BuildingNode[A, B] = {
      if (i < 0)
        withInsert(~i, hash, key, value).buildingSplitIfNeeded(shift)
      else
        withUpdate(i, value)
    }

    private def withUpdate(i: Int, value: B): Leaf[A, B] = {
      // reuse hashes
      val nkvs = kvs.clone
      nkvs(2 * i + 1) = value.asInstanceOf[AnyRef]
      new Leaf[A, B](hashes, nkvs)
    }

    private def withInsert(i: Int, hash: Int, key: A, value: B): Leaf[A, B] = {
      val z = newLeaf(hashes.length + 1)
      val j = hashes.length - i
      
      System.arraycopy(hashes, 0, z.hashes, 0, i)
      System.arraycopy(hashes, i, z.hashes, i + 1, j)
      z.hashes(i) = hash

      System.arraycopy(kvs, 0, z.kvs, 0, 2 * i)
      System.arraycopy(kvs, 2 * i, z.kvs, 2 * i + 2, 2 * j)
      z.setKey(i, key)
      z.setValue(i, value)

      z
    }

    def withRemove(i: Int): Leaf[A, B] = {
      if (i < 0)
        this
      else {
        val z = newLeaf(hashes.length - 1)
        if (z.hashes.length > 0) {
          val j = z.hashes.length - i

          System.arraycopy(hashes, 0, z.hashes, 0, i)
          System.arraycopy(hashes, i + 1, z.hashes, i, j)

          System.arraycopy(kvs, 0, z.kvs, 0, 2 * i)
          System.arraycopy(kvs, 2 * i + 2, z.kvs, 2 * i, 2 * j)
        }
        z
      }
    }

    def splitIfNeeded(gen: Long, shift: Int, contended: Boolean): Node[A, B] = {
      if (!shouldSplit(contended)) this else split(gen, shift)
    }

    def buildingSplitIfNeeded(shift: Int): BuildingNode[A, B] = if (!shouldSplit(false)) this else buildingSplit(shift)

    def shouldSplit(contended: Boolean): Boolean = {
      // if the hash function is bad we might be oversize but unsplittable
      (contended || hashes.length > MaxLeafCapacity) && hashes(hashes.length - 1) != hashes(0)
    }

    def split(gen: Long, shift: Int): Branch[A, B] = {
      val children = new Array[Node[A, B]](BF)
      splitInto(shift, children)

      // class manifests for classes that have type parameters are a bit
      // convoluted to construct, so it is better to do it only once per split
      implicit val cm = implicitly[ClassManifest[Node[A, B]]]

      val refs = new Array[Ref.View[Node[A, B]]](BF)
      var i = 0
      while (i < BF) {
        refs(i) = Ref(children(i)).single
        i += 1
      }
      new Branch[A, B](gen, false, refs)      
    }

    def buildingSplit(shift: Int): BuildingBranch[A, B] = {
      val children = new Array[BuildingNode[A, B]](BF)
      splitInto(shift, children)
      new BuildingBranch[A, B](children)
    }

    private def splitInto[L >: Leaf[A, B]](shift: Int, children: Array[L]) {
      val sizes = new Array[Int](BF)
      var i = 0
      while (i < hashes.length) {
        sizes(indexFor(shift, hashes(i))) += 1
        i += 1
      }
      i = 0
      while (i < BF) {
        children(i) = newLeaf(sizes(i))
        i += 1
      }
      i = hashes.length - 1
      while (i >= 0) {
        val slot = indexFor(shift, hashes(i))
        sizes(slot) -= 1
        val pos = sizes(slot)
        val dst = children(slot).asInstanceOf[Leaf[A, B]]
        dst.hashes(pos) = hashes(i)
        dst.setKey(pos, getKey(i))
        dst.setValue(pos, getValue(i))

        // If the hashes were very poorly distributed one leaf might get
        // everything.  We could resplit now, but it doesn't seem to be worth
        // it.  If we wait until the next insert we can never get more than
        // 32 / LogBF extra.
        //// if (pos == 0 && dst.shouldSplit)
        ////  children(slot).value = dst.split(gen, shift + LogBF)
        i -= 1
      }
    }

    private def newLeaf(n: Int): Leaf[A, B] = {
      if (n == 0)
        emptyLeaf.asInstanceOf[Leaf[A, B]]
      else
        new Leaf[A, B](new Array[Int](n), new Array[AnyRef](2 * n))
    }

    def keyForeach[U](f: A => U) {
      var i = 0
      while (i < hashes.length) {
        f(getKey(i))
        i += 1
      }
    }

    def mapForeach[U](f: ((A, B)) => U) {
      var i = 0
      while (i < hashes.length) {
        f(getKeyValue(i))
        i += 1
      }
    }

    def keyIterator: Iterator[A] = new Iterator[A] {
      var pos = 0
      def hasNext = pos < hashes.length
      def next: A = { val z = getKey(pos) ; pos += 1 ; z }
    }

    def valueIterator: Iterator[B] = new Iterator[B] {
      var pos = 0
      def hasNext = pos < hashes.length
      def next: B = { val z = getValue(pos) ; pos += 1 ; z }
    }

    def mapIterator: Iterator[(A, B)] = new Iterator[(A,B)] {
      var pos = 0
      def hasNext = pos < hashes.length
      def next: (A, B) = { val z = getKeyValue(pos) ; pos += 1 ; z }
    }
  }

  class BuildingBranch[A, B](val children: Array[BuildingNode[A, B]]) extends BuildingNode[A, B] {
    def endBuild: Node[A, B] = {
      val refs = new Array[Ref.View[Node[A, B]]](BF)
      var i = 0
      while (i < BF) {
        refs(i) = Ref(children(i).endBuild).single
        i += 1
      }
      new Branch(0L, false, refs)
    }
  }

  class Branch[A, B](val gen: Long, val frozen: Boolean, val children: Array[Ref.View[Node[A, B]]]) extends Node[A, B] {
    // size may only be called on a frozen branch, so we can cache the result
    private var _cachedSize = -1

    def cappedSize(cap: Int): Int = {
      val n0 = _cachedSize
      if (n0 >= 0) {
        n0
      } else {
        var n = 0
        var i = 0
        while (i < BF && n < cap) {
          n += children(i)().cappedSize(cap - n)
          i += 1
        }
        if (n < cap)
          _cachedSize = n // everybody tried their hardest
        n
      }
    }

    def txnIsEmpty(implicit txn: InTxn): Boolean = {
      var i = 0
      while (i < BF) {
        val c = children(i).ref.get
        if (!c.txnIsEmpty)
          return false
        i += 1
      }
      return true
    }

    def withFreeze: Branch[A, B] = new Branch(gen, true, children)

    def clone(newGen: Long): Branch[A, B] = {
      val cc = children.clone
      var i = 0
      while (i < cc.length) {
        cc(i) = Ref(cc(i)()).single
        i += 1
      }
      new Branch[A, B](newGen, false, cc)
    }

    def keyForeach[U](f: A => U) {
      var i = 0
      while (i < BF) {
        children(i)().keyForeach(f)
        i += 1
      }
    }

    def mapForeach[U](f: ((A, B)) => U) {
      var i = 0
      while (i < BF) {
        children(i)().mapForeach(f)
        i += 1
      }
    }

    private abstract class Iter[Z] extends Iterator[Z] {

      def childIter(c: Node[A, B]): Iterator[Z]

      private var pos = -1
      private var iter: Iterator[Z] = null
      advance()

      @tailrec private def advance(): Boolean = {
        if (pos == BF - 1) {
          iter = null
          false
        } else {
          pos += 1
          val c = children(pos)()
          if (c eq emptyLeaf)
            advance() // keep looking, nothing is here
          else {
            iter = childIter(c)
            iter.hasNext || advance() // keep looking if we got a dud
          }
        }
      }

      def hasNext = iter != null && iter.hasNext

      def next: Z = {
        val z = iter.next
        if (!iter.hasNext)
          advance()
        z
      }
    }

    def keyIterator: Iterator[A] = new Iter[A] {
      def childIter(c: Node[A, B]) = c.keyIterator
    }

    def valueIterator: Iterator[B] = new Iter[B] {
      def childIter(c: Node[A, B]) = c.valueIterator
    }

    def mapIterator: Iterator[(A, B)] = new Iter[(A,B)] {
      def childIter(c: Node[A, B]) = c.mapIterator
    }
  }

  //////////////// construction

  def emptySetNode[A]: SetNode[A] = emptyLeaf.asInstanceOf[SetNode[A]]
  def emptyMapNode[A, B]: Node[A, B] = emptyLeaf.asInstanceOf[Node[A, B]]

  def emptySetBuildingNode[A]: SetBuildingNode[A] = emptyLeaf.asInstanceOf[SetBuildingNode[A]]
  def emptyMapBuildingNode[A, B]: BuildingNode[A, B] = emptyLeaf.asInstanceOf[BuildingNode[A, B]]

  def buildingAdd[A](root: SetBuildingNode[A], x: A): SetBuildingNode[A] = buildingPut(root, 0, keyHash(x), x, null)
  def buildingPut[A, B](root: BuildingNode[A, B], k: A, v: B): BuildingNode[A, B] = buildingPut(root, 0, keyHash(k), k, v)

  private def buildingPut[A, B](current: BuildingNode[A, B], shift: Int, hash: Int, key: A, value: B): BuildingNode[A, B] = {
    current match {
      case leaf: Leaf[A, B] => {
        val i = leaf.find(hash, key)
        if (leaf.noChange(i, value)) leaf else leaf.withBuildingPut(shift, hash, key, value, i)
      }
      case branch: BuildingBranch[A, B] => {
        val i = indexFor(shift, hash)
        branch.children(i) = buildingPut(branch.children(i), shift + LogBF, hash, key, value)
        branch
      }
    }
  }
}

private[skel] abstract class TxnHashTrie[A, B](protected var root: Ref.View[TxnHashTrie.Node[A, B]]) {
  import TxnHashTrie._

  //////////////// txn contention tracking

  private final val pct = 10000
  private final val contentionThreshold = 1 * pct
  private var contentionEstimate = 0

  private def recordNoContention() {
    if (SimpleRandom.nextInt(32) == 0) {
      val e = contentionEstimate
      contentionEstimate = e - (e >> 4) // this is 15/16, applied every 32nd time, so about 99.8%
    }
  }

  private def recordContention() {
    val e = contentionEstimate
    contentionEstimate = e + ((100 * pct - e) >> 9) // 100 * pct is the max
  }

  private def isContended = contentionEstimate > contentionThreshold

  //////////////// whole-trie operations

  protected def frozenRoot: Node[A, B] = {
    root() match {
      case leaf: Leaf[A, B] => leaf // leaf is already immutable
      case branch: Branch[A, B] if branch.frozen => branch
      case branch: Branch[A, B] => {
        // If this CAS fails it means someone else already installed a frozen
        // branch, and we can benefit from their work.
        val b = branch.withFreeze
        root.compareAndSetIdentity(branch, b)
        b
      }
    }
  }

  protected def cloneRoot: Ref.View[Node[A, B]] = Ref(frozenRoot).single

  protected def setIterator: Iterator[A] = frozenRoot.keyIterator

  protected def mapIterator: Iterator[(A, B)] = frozenRoot.mapIterator
  protected def mapKeyIterator: Iterator[A] = frozenRoot.keyIterator
  protected def mapValueIterator: Iterator[B] = frozenRoot.valueIterator

  //////////////// whole-trie operations on Ref.View

  protected def singleIsEmpty: Boolean = impl.STMImpl.instance.dynCurrentOrNull match {
    case null => frozenRoot.cappedSize(1) == 0
    case txn => txnIsEmpty(txn)
  }

  protected def singleSize: Int = frozenRoot.cappedSize(Int.MaxValue)

  protected def singleSetForeach[U](f: A => U) {
    // don't freeze the root if we use .single in a txn
    impl.STMImpl.instance.dynCurrentOrNull match {
      case null => frozenRoot.keyForeach(f)
      case txn => txnSetForeach(f)(txn)
    }
  }

  protected def singleMapForeach[U](f: ((A, B)) => U) {
    impl.STMImpl.instance.dynCurrentOrNull match {
      case null => frozenRoot.mapForeach(f)
      case txn => txnMapForeach(f)(txn)
    }
  }

  //////// single-key operations for Ref.View

  protected def singleContains(key: A): Boolean = singleContains(null, root, 0, keyHash(key), key)

  @tailrec private def singleContains(rootNode: Node[A, B], n: Ref.View[Node[A, B]], shift: Int, hash: Int, key: A): Boolean = {
    n() match {
      case leaf: Leaf[A, B] => {
        if (shift != 0 && (rootNode ne root()))
          singleContains(null, root, 0, hash, key)
        else
          leaf.contains(hash, key)
      }
      case branch: Branch[A, B] => {
        val rn = if (shift == 0) branch else rootNode
        singleContains(rn, branch.children(indexFor(shift, hash)), shift + LogBF, hash, key)
      }
    }
  }

  protected def singleGetOrThrow(key: A): B = singleGetOrThrow(null, root, 0, keyHash(key), key)

  @tailrec private def singleGetOrThrow(rootNode: Node[A, B], n: Ref.View[Node[A, B]], shift: Int, hash: Int, key: A): B = {
    n() match {
      case leaf: Leaf[A, B] => {
        if (shift != 0 && (rootNode ne root()))
          singleGetOrThrow(null, root, 0, hash, key)
        else {
          val i = leaf.find(hash, key)
          if (i < 0)
            throw new NoSuchElementException("key not found: " + key)
          leaf.getValue(i)
        }
      }
      case branch: Branch[A, B] => {
        val rn = if (shift == 0) branch else rootNode
        singleGetOrThrow(rn, branch.children(indexFor(shift, hash)), shift + LogBF, hash, key)
      }
    }
  }

  protected def singleGet(key: A): Option[B] = singleGet(null, root, 0, keyHash(key), key)

  @tailrec private def singleGet(rootNode: Node[A, B], n: Ref.View[Node[A, B]], shift: Int, hash: Int, key: A): Option[B] = {
    n() match {
      case leaf: Leaf[A, B] => {
        if (shift != 0 && (rootNode ne root()))
          singleGet(null, root, 0, hash, key)
        else
          leaf.get(hash, key)
      }
      case branch: Branch[A, B] => {
        val rn = if (shift == 0) branch else rootNode
        singleGet(rn, branch.children(indexFor(shift, hash)), shift + LogBF, hash, key)
      }
    }
  }

  protected def singlePut(key: A, value: B): Option[B] = singleRootPut(keyHash(key), key, value, 0)

  @tailrec private def singleRootPut(hash: Int, key: A, value: B, failures: Int): Option[B] = {
    if (failures < 10) {
      root() match {
        case leaf: Leaf[A, B] => {
          val i = leaf.find(hash, key)
          if (leaf.noChange(i, value) || root.compareAndSetIdentity(leaf, leaf.withPut(0L, 0, hash, key, value, i, false)))
            leaf.get(i) // success, read from old leaf
          else
            singleRootPut(hash, key, value, failures + 1)
        }
        case branch: Branch[A, B] => {
          val b = if (!branch.frozen) branch else singleUnshare(branch.gen + 1, root, branch)
          if (b != null)
            singleChildPut(b, b.children(indexFor(0, hash)), LogBF, hash, key, value, 0)
          else
            singleRootPut(hash, key, value, failures + 1)
        }
      }
    } else
      failingPut(hash, key, value)
  }

  private def singleUnshare(rootGen: Long, current: Ref.View[Node[A, B]], branch: Branch[A, B]): Branch[A, B] = {
    val b = branch.clone(rootGen)
    if (current.compareAndSetIdentity(branch, b)) b else null
  }

  private def failingPut(hash: Int, key: A, value: B): Option[B] = {
    // running in a transaction guarantees that CAS won't fail
    atomic { implicit txn => txnRootPut(hash, key, value) }
  }

  @tailrec private def singleChildPut(rootNode: Branch[A, B],
                                      current: Ref.View[Node[A, B]],
                                      shift: Int,
                                      hash: Int,
                                      key: A,
                                      value: B,
                                      failures: Int): Option[B] = {
    if (failures < 10) {
      current() match {
        case leaf: Leaf[A, B] => {
          val i = leaf.find(hash, key)
          if (leaf.noChange(i, value) || atomic.compareAndSetIdentity(
                  root.ref, rootNode, rootNode, current.ref,
                  leaf, leaf.withPut(rootNode.gen, shift, hash, key, value, i, failures > 0)))
            leaf.get(i) // success
          else if (root() ne rootNode)
            failingPut(hash, key, value) // root retry
          else
            singleChildPut(rootNode, current, shift, hash, key, value, failures + 1) // local retry
        }
        case branch: Branch[A, B] => {
          val b = if (branch.gen == rootNode.gen) branch else singleUnshare(rootNode.gen, current, branch)
          if (b != null)
            singleChildPut(rootNode, b.children(indexFor(shift, hash)), shift + LogBF, hash, key, value, failures)
          else
            singleChildPut(rootNode, current, shift, hash, key, value, failures + 1) // failure, try again
        }
      }
    } else
      failingPut(hash, key, value)
  }

  protected def singleRemove(key: A): Option[B] = singleRootRemove(keyHash(key), key, 0)

  @tailrec private def singleRootRemove(hash: Int, key: A, failures: Int): Option[B] = {
    if (failures < 10) {
      root() match {
        case leaf: Leaf[A, B] => {
          val i = leaf.find(hash, key)
          if (i < 0 || root.compareAndSetIdentity(leaf, leaf.withRemove(i)))
            leaf.get(i) // success, read from old leaf
          else
            singleRootRemove(hash, key, failures + 1)
        }
        case branch: Branch[A, B] => {
          val i = indexFor(0, hash)
          if (branch.frozen && !singleContains(branch, branch.children(i), LogBF, hash, key))
            None
          else {
            val b = if (!branch.frozen) branch else singleUnshare(branch.gen + 1, root, branch)
            if (b != null)
              singleChildRemove(b, b.children(i), LogBF, hash, key, (b ne branch), 0)
            else
              singleRootRemove(hash, key, failures + 1)
          }
        }
      }
    } else
      failingRemove(hash, key)
  }

  private def failingRemove(hash: Int, key: A): Option[B] = {
    // running in a transaction guarantees that CAS won't fail
    atomic { implicit txn => txnRootRemove(hash, key) }
  }

  @tailrec private def singleChildRemove(rootNode: Branch[A, B],
                                         current: Ref.View[Node[A, B]],
                                         shift: Int,
                                         hash: Int,
                                         key: A,
                                         checked: Boolean,
                                         failures: Int): Option[B] = {
    if (failures < 10) {
      current() match {
        case leaf: Leaf[A, B] => {
          val i = leaf.find(hash, key)
          if (i < 0)
            None // no change, key wasn't present
          else if (atomic.compareAndSetIdentity(root.ref, rootNode, rootNode, current.ref, leaf, leaf.withRemove(i)))
            leaf.get(i) // success
          else if (root() ne rootNode)
            failingRemove(hash, key) // root retry
          else
            singleChildRemove(rootNode, current, shift, hash, key, checked, failures + 1) // local retry
        }
        case branch: Branch[A, B] => {
          val i = indexFor(shift, hash)
          if (!checked && branch.gen != rootNode.gen && !singleContains(rootNode, branch.children(i), shift + LogBF, hash, key))
            None // child is absent
          else {
            val b = if (branch.gen == rootNode.gen) branch else singleUnshare(rootNode.gen, current, branch)
            if (b != null)
              singleChildRemove(rootNode, b.children(i), shift + LogBF, hash, key, checked || (b ne branch), failures)
            else
              singleChildRemove(rootNode, current, shift, hash, key, checked, failures + 1)
          }
        }
      }
    } else
      failingRemove(hash, key)
  }


  //////////////// whole-trie operations when an InTxn is available

  // visitation doesn't need to freeze the root, because we know that the
  // entire visit is part of an atomic block

  protected def txnIsEmpty(implicit txn: InTxn): Boolean = root().txnIsEmpty

  protected def txnSetForeach[U](f: A => U)(implicit txn: InTxn) { root().keyForeach(f) }

  protected def txnMapForeach[U](f: ((A, B)) => U)(implicit txn: InTxn) { root().mapForeach(f) }

  //////////////// per-key operations when an InTxn is available

  protected def txnContains(key: A)(implicit txn: InTxn): Boolean = txnContains(root.ref, 0, keyHash(key), key)(txn)

  @tailrec private def txnContains(n: Ref[Node[A, B]], shift: Int, hash: Int, key: A)(implicit txn: InTxn): Boolean = {
    n() match {
      case leaf: Leaf[A, B] => leaf.contains(hash, key)
      case branch: Branch[A, B] => txnContains(branch.children(indexFor(shift, hash)).ref, shift + LogBF, hash, key)(txn)
    }
  }

  protected def txnGetOrThrow(key: A)(implicit txn: InTxn): B = txnGetOrThrow(root.ref, 0, keyHash(key), key)(txn)

  @tailrec private def txnGetOrThrow(n: Ref[Node[A, B]], shift: Int, hash: Int, key: A)(implicit txn: InTxn): B = {
    n() match {
      case leaf: Leaf[A, B] => {
        val i = leaf.find(hash, key)
        if (i < 0)
          throw new NoSuchElementException("key not found: " + key)
        leaf.getValue(i)
      }
      case branch: Branch[A, B] => txnGetOrThrow(branch.children(indexFor(shift, hash)).ref, shift + LogBF, hash, key)(txn)
    }
  }

  protected def txnGet(key: A)(implicit txn: InTxn): Option[B] = txnGet(root.ref, 0, keyHash(key), key)(txn)

  @tailrec private def txnGet(n: Ref[Node[A, B]], shift: Int, hash: Int, key: A)(implicit txn: InTxn): Option[B] = {
    n() match {
      case leaf: Leaf[A, B] => leaf.get(hash, key)
      case branch: Branch[A, B] => txnGet(branch.children(indexFor(shift, hash)).ref, shift + LogBF, hash, key)(txn)
    }
  }

  protected def txnPut(key: A, value: B)(implicit txn: InTxn): Option[B] = txnRootPut(keyHash(key), key, value)(txn)

  private def txnRootPut(hash: Int, key: A, value: B)(implicit txn: InTxn): Option[B] = {
    root() match {
      case leaf: Leaf[A, B] => {
        val i = leaf.find(hash, key)
        if (!leaf.noChange(i, value))
          set(root.ref, leaf.withPut(0L, 0, hash, key, value, i, isContended))
        leaf.get(i)
      }
      case branch: Branch[A, B] => {
        val b = if (!branch.frozen) branch else txnUnshare(branch.gen + 1, root.ref, branch)
        txnChildPut(b.gen, b.children(indexFor(0, hash)).ref, LogBF, hash, key, value)(txn)
      }
    }
  }

  private def set(ref: Ref[Node[A, B]], node: Node[A, B])(implicit txn: InTxn) {
    if (!ref.trySet(node)) {
      recordContention()
      ref() = node
    } else
      recordNoContention()
  }

  private def txnUnshare(rootGen: Long, current: Ref[Node[A, B]], branch: Branch[A, B])(implicit txn: InTxn): Branch[A, B] = {
    val b = branch.clone(rootGen)
    current() = b
    b
  }

  @tailrec private def txnChildPut(rootGen: Long, current: Ref[Node[A, B]], shift: Int, hash: Int, key: A, value: B
          )(implicit txn: InTxn): Option[B] = {
    current() match {
      case leaf: Leaf[A, B] => {
        val i = leaf.find(hash, key)
        if (!leaf.noChange(i, value))
          set(current, leaf.withPut(rootGen, shift, hash, key, value, i, isContended))
        leaf.get(i)
      }
      case branch: Branch[A, B] => {
        val b = if (branch.gen == rootGen) branch else txnUnshare(rootGen, current, branch)
        txnChildPut(rootGen, b.children(indexFor(shift, hash)).ref, shift + LogBF, hash, key, value)(txn)
      }
    }
  }

  protected def txnRemove(key: A)(implicit txn: InTxn): Option[B] = txnRootRemove(keyHash(key), key)(txn)

  private def txnRootRemove(hash: Int, key: A)(implicit txn: InTxn): Option[B] = {
    root() match {
      case leaf: Leaf[A, B] => {
        val i = leaf.find(hash, key)
        if (i >= 0)
          set(root.ref, leaf.withRemove(i))
        leaf.get(i)
      }
      case branch: Branch[A, B] => {
        val i = indexFor(0, hash)
        if (branch.frozen && !txnContains(branch.children(i).ref, LogBF, hash, key))
          None
        else {
          val b = if (!branch.frozen) branch else txnUnshare(branch.gen + 1, root.ref, branch)
          txnChildRemove(b.gen, b.children(i).ref, LogBF, hash, key, (b ne branch))(txn)
        }
      }
    }
  }

  @tailrec private def txnChildRemove(rootGen: Long, current: Ref[Node[A, B]], shift: Int, hash: Int, key: A, checked: Boolean
          )(implicit txn: InTxn): Option[B] = {
    current() match {
      case leaf: Leaf[A, B] => {
        val i = leaf.find(hash, key)
        if (i >= 0)
          set(current, leaf.withRemove(i))
        leaf.get(i)
      }
      case branch: Branch[A, B] => {
        val i = indexFor(shift, hash)
        if (!checked && branch.gen != rootGen && !txnContains(branch.children(i).ref, shift + LogBF, hash, key))
          None // child is absent
        else {
          val b = if (branch.gen == rootGen) branch else txnUnshare(rootGen, current, branch)
          txnChildRemove(rootGen, b.children(i).ref, shift + LogBF, hash, key, checked || (b ne branch))(txn)
        }
      }
    }
  }
}
