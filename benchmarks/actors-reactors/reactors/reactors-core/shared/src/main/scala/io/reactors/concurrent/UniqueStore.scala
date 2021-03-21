package io.reactors
package concurrent



import java.util.concurrent.ThreadLocalRandom
import java.util.concurrent.atomic._
import io.reactors.common.Monitor
import scala.annotation.tailrec
import scala.collection._



/** Stores `Identifiable` objects along with their unique names.
 */
final class UniqueStore[T >: Null <: Identifiable with AnyRef](
  val uniqueNamePrefix: String,
  val monitor: Monitor
) {
  private val idCounter = new AtomicLong(0L)
  private val byName = mutable.Map[String, T]()
  private val byId = mutable.Map[Long, String]()

  /** Compute and return a unique id.
   */
  def reserveId(): Long = idCounter.getAndIncrement()

  /** Atomically returns the values in this unique store.
   */
  def values: Iterable[(Long, String, T)] = monitor.synchronized {
    for ((id, name) <- byId) yield (id, name, byName(name))
  }

  /** Attempt to store the value `x` with the `proposedName`.
   *
   *  Returns the name under which `x` is stored. If the name is not available, returns
   *  `null` and does not store the object.
   *
   *  @param proposedName     the proposed name, or `null` to assign any name
   *  @param x                the object
   *  @return                 name under which `x` was stored
   *  @throws                 an `IllegalArgumentException` if the proposed name already
   *                          exists in the map
   */
  def tryStore(proposedName: String, x: T): String = monitor.synchronized {
    @tailrec def uniqueName(count: Long): String = {
      val suffix = if (count == 0) "" else s"-$count"
      val possibleName = s"$uniqueNamePrefix-${x.uid}$suffix"
      if (byName.contains(possibleName)) uniqueName(count + 1)
      else possibleName
    }
    val uname =
      if (proposedName != null) proposedName else uniqueName(0)
    if (byName.contains(uname)) {
      throw new IllegalArgumentException(s"Name $proposedName unavailable.")
    } else {
      byId(x.uid) = uname
      byName(uname) = x
      uname
    }
  }

  /** Attempts to release the specified name.
   *
   *  @param name            the name under which an object was stored
   *  @return                `true` if released, `false` otherwise
   */
  def tryRelease(name: String): Boolean = monitor.synchronized {
    if (!byName.contains(name)) false
    else {
      val x = byName(name)
      byName.remove(name)
      byId.remove(x.uid)
      true
    }
  }

  /** Releases the object under the specified id.
   *
   *  @param id              the unique id of the object
   *  @return                `true` if released, `false` otherwise
   */
  def tryReleaseById(id: Long): Boolean = monitor.synchronized {
    if (!byId.contains(id)) false
    else tryRelease(byId(id))
  }

  /** Returns an object stored under the specified name, or `null`.
   */
  def forName(name: String): T = monitor.synchronized {
    if (byName.contains(name)) byName(name) else null
  }
}
