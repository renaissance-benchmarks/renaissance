package org.renaissance.kotlin.ktor.client

import io.ktor.client.plugins.websocket.*
import io.ktor.util.*
import io.ktor.websocket.*
import org.renaissance.kotlin.ktor.common.Message
import org.renaissance.kotlin.ktor.common.command.RenameUserCommand
import org.renaissance.kotlin.ktor.common.sendSerialisedCommandNative
import java.util.concurrent.atomic.AtomicInteger
import kotlin.random.Random

abstract class SendMessageAndAwaitClientTask(
  private val random: Random,
  private val clientId: String = generateNonce()
) : ClientTask {
  private val messageId = AtomicInteger(0)

  protected suspend fun DefaultClientWebSocketSession.sendMessageToChatAndAwait(chatId: String) {
    val expectedMsg = "${messageId.getAndIncrement()}_${random.getRandomString(random.nextInt(1, MAX_MESSAGE_LENGTH))}"
    sendSerialisedCommandNative(RenameUserCommand("client$clientId"))
    sendSerialized(Message(chatId, expectedMsg))
    val expectedMessage = "[client$clientId] $expectedMsg"
    waitForMessage {
      val receivedText =  (it as? Frame.Text)?.readText() ?: return@waitForMessage false
      receivedText == expectedMessage
    }
  }
}

const val MAX_MESSAGE_LENGTH = 356