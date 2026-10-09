package org.renaissance.kotlin.ktor.common

class DirectMessageChat(val userId1: String, val userId2: String, chatId: String): Chat(chatId) {
  companion object {
    fun hashForChat(userId1: String, userId2: String): String =
      if (userId1 < userId2) {
        "$userId1-$userId2"
      } else {
        "$userId2-$userId1"
      }
  }
}