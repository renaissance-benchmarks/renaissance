package org.renaissance.kotlin.ktor.client

import io.ktor.client.plugins.websocket.*
import io.ktor.serialization.*
import org.renaissance.kotlin.ktor.common.User
import org.renaissance.kotlin.ktor.common.command.CommandReply
import org.renaissance.kotlin.ktor.common.command.CreateDirectMessageChatCommand
import org.renaissance.kotlin.ktor.common.command.CreateDirectMessageChatCommandReply
import org.renaissance.kotlin.ktor.common.sendSerializedCommandNative
import kotlin.random.Random

class DirectMessageClientTask(
  private val recipientUserId: String,
  random: Random
) : SendMessageAndAwaitClientTask(random) {
  private lateinit var privateChatId: String

  override suspend fun run(session: DefaultClientWebSocketSession, user: User): Boolean {
    session.sendSerializedCommandNative(CreateDirectMessageChatCommand(recipientUserId))
    session.waitForMessage {
      val reply = kotlin.runCatching { session.converter!!.deserialize<CommandReply>(it) }.getOrNull()
      if (reply is CreateDirectMessageChatCommandReply) {
        privateChatId = reply.chatId
        true
      } else {
        false
      }
    }

    return session.sendMessageToChatAndAwait(privateChatId, user)
  }
}
