package org.renaissance.kotlin.ktor.common

import java.util.concurrent.atomic.AtomicReference

/**
 * Represents a user in the chat system.
 *
 * @property id The unique identifier for the user.
 * @property name The display name of the user.
 */
data class User(val id: String) {
  // Needed for safe read/write access from any connection's coroutine.
  private val nameRef = AtomicReference(id)

  var name: String
    get() = nameRef.get()
    set(value) { nameRef.set(value) }

  /**
   * Renames this user (unless someone did it first).
   *
   * @return the name just before the rename, or null if a
   * concurrent rename was faster.
   */
  fun rename(newName: String): String? {
    val oldName = nameRef.get()
    return if (nameRef.compareAndSet(oldName, newName)) oldName else null
  }
}
