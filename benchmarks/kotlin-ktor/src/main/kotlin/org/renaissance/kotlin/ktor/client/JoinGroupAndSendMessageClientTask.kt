package org.renaissance.kotlin.ktor.client

import io.ktor.client.plugins.websocket.*
import org.renaissance.kotlin.ktor.common.command.JoinChatCommand
import org.renaissance.kotlin.ktor.common.sendSerialisedCommandNative
import kotlin.random.Random


class JoinGroupAndSendMessageClientTask(private val chatId: String, random: Random): SendMessageAndAwaitClientTask(random) {
  override suspend fun run(session: DefaultClientWebSocketSession) {
    session.sendSerialisedCommandNative(JoinChatCommand(chatId))
    session.sendMessageToChatAndAwait(chatId)
  }
}