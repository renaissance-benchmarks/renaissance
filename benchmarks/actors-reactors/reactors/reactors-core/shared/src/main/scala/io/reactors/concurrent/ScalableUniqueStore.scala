package io.reactors
package concurrent



import io.reactors.common.concurrent.UidGenerator
import scala.annotation.tailrec
import scala.collection._



/** Stores `Identifiable` objects along with their unique names, in a scalable manner.
 *
 *  The UIDs of the objects stored in this data structure must always be unique for an
 *  instance of the data structure. Users may use `reserveId` to achieve this. The
 *  names of the objects need not be unique.
 */
final class ScalableUniqueStore[T >: Null <: Identifiable with AnyRef](
  val uniqueNamePrefix: String,
  val scalability: Int
) {
  private[reactors] val uidCounter = new UidGenerator(scalability)
  private[reactors] val byName = Platform.newSnapshotMap[String, T]

  /** Compute and return a unique id.
   */
  def reserveId(): Long = uidCounter.generate()

  /** Atomically returns the values in this unique store.
   */
  def values: Iterable[(Long, String, T)] = {
    for ((name, obj) <- byName.snapshot) yield (obj.uid, name, obj)
  }

  /** Proposes an unused name.
   */
  @tailrec
  final def proposeName(uid: Long): String = {
    val name = s"$uniqueNamePrefix-$uid"
    if (byName.contains(name)) proposeName(uid + 1)
    else name
  }

  /** Attempt to store the value `x` with the `proposedName`.
   *
   *  '''Note:''' the UID of `x` must be unique among all `x` ever stored in this
   *  data structure. Use `reserveId` to obtain a UID.
   *
   *  Returns the name under which `x` is stored. If the name is not available, returns
   *  `null` and does not store the object.
   *
   *  @param proposedName     proposed name, or `null` to assign any non-existing name
   *  @param x                object to store
   *  @return                 name under which `x` was stored, or `null` if proposed
   *                          name already existed (in which case, nothing was stored)
   */
  def tryStore(proposedName: String, x: T): String = {
    @tailrec def store(count: Long): String = {
      val suffix = if (count == 0) "" else s"-$count"
      val possibleName = s"$uniqueNamePrefix-${x.uid}$suffix"
      if (byName.putIfAbsent(possibleName, x) != None) store(count + 1)
      else possibleName
    }
    if (proposedName != null) {
      if (byName.putIfAbsent(proposedName, x) != None) null
      else proposedName
    } else {
      store(0L)
    }
  }

  /** Atomically replaces an existing entry in the unique store with a new one.
   *
   *  The new entry must be stored under an existing name, and it must have the same UID
   *  as the entry that is currently under that name.
   *
   *  @param existingName    the existing name
   *  @param ox              the expected old entry under the specified name
   *  @param nx              the new entry to store under the specified name
   *  @return                `true` if an existing entry was replaced, `false` otherwise
   */
  def tryReplace(existingName: String, ox: T, nx: T): Boolean = {
    byName.replace(existingName, ox, nx)
  }

  /** Attempts to release the specified name.
   *
   *  @param name            the name under which an object was stored
   *  @return                `true` if released, `false` otherwise
   */
  def tryRelease(name: String): Boolean = {
    byName.remove(name) match {
      case None =>
        false
      case Some(v) =>
        true
    }
  }

  /** Returns an object stored under the specified name, or `null`.
   */
  def forName(name: String): T = byName.get(name) match {
    case None => null
    case Some(x) => x
  }
}
