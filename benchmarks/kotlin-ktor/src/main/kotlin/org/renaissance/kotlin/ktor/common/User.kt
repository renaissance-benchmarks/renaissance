package org.renaissance.kotlin.ktor.common

/**
 * Represents a user in the chat system.
 *
 * @property userId The unique identifier for the user.
 * @property userName The display name of the user.
 */
data class User(val userId: String) {
  var userName: String = userId
}