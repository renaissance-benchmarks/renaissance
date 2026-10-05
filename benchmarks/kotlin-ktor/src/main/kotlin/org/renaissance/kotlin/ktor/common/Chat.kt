package org.renaissance.kotlin.ktor.common

import io.ktor.util.collections.*
import java.util.concurrent.ConcurrentLinkedDeque

open class Chat(val id: String) {
  val users = ConcurrentSet<User>()
  /**
   * A list of the latest messages sent to the server, so new members can have a bit context of what
   * other people was talking about before joining.
   */
  val lastMessages = ConcurrentLinkedDeque<String>()
}