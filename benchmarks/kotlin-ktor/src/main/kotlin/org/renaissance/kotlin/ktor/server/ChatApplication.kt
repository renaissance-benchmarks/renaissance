package org.renaissance.kotlin.ktor.server

import io.ktor.serialization.*
import io.ktor.serialization.kotlinx.*
import io.ktor.server.application.*
import io.ktor.server.plugins.callloging.*
import io.ktor.server.plugins.defaultheaders.*
import io.ktor.server.routing.*
import io.ktor.server.util.*
import io.ktor.server.websocket.*
import io.ktor.websocket.*
import kotlinx.coroutines.channels.consumeEach
import org.renaissance.kotlin.ktor.common.Message
import org.renaissance.kotlin.ktor.common.command.*
import org.renaissance.kotlin.ktor.common.sendSerializedCommandReplyNative
import org.renaissance.kotlin.ktor.common.serializationFormat
import kotlin.random.Random

/**
 * This object and the server it configures are created once for the whole
 * benchmark run. The [setup] and [teardown] methods are called once per
 * repetition to provide reproducible initial state.
 */
class ChatApplication(initialChatCount: Int, initialSeed: Long) {
  private val server = ChatServer(initialChatCount, initialSeed)

  fun getAvailableChatIds(): ArrayList<String> {
    return ArrayList(server.chats.keys)
  }

  fun setup() = server.setup()

  fun teardown() = server.teardown()

  /**
   * Configures Ktor's [Application]: installs default headers, call logging,
   * and the WebSocket plugin (sharing [serializationFormat] with the client).
   * The application exposes a single `/ws/{userId}` path which provides an
   * entry point for users. Users can open multiple connections, so they are
   * registered along with the session. Commands sent by the client are
   * dispatched to [server].
   */
  fun Application.main() {
    install(DefaultHeaders)
    install(CallLogging)
    install(WebSockets) {
      contentConverter = KotlinxWebsocketSerializationConverter(serializationFormat)
    }

    routing {
      webSocket("/ws/{userId}") {
        // The pattern guarantees userId is non-null on match.
        val userId = call.parameters.getOrFail("userId")

        server.registerUser(userId, this)

        try {
          incoming.consumeEach { frame ->
            if (frame is Frame.Text) {
              receivedMessage(userId, frame)
            }
          }
        } finally {
          // Always remove the user from the server's connection tracking.
          server.disconnectUserSocket(userId, this)
        }
      }
    }
  }

  private suspend fun DefaultWebSocketServerSession.receivedMessage(userId: String, frame: Frame.Text) {
    val deserializedCommand = kotlin.runCatching { converter!!.deserialize<Command>(frame) }.getOrNull()
    when (deserializedCommand) {
      is RenameUserCommand -> {
        server.renameUser(userId, deserializedCommand.newName)
      }

      is JoinChatCommand -> {
        server.joinChat(deserializedCommand.chatId, userId)
      }

      is CreateDirectMessageChatCommand -> {
        val createdChat = server.createDirectMessageChat(
          userId,
          deserializedCommand.inviteeUserId,
        )
        sendSerializedCommandReplyNative(CreateDirectMessageChatCommandReply(createdChat))
      }

      // Handle a normal message.
      else -> server.sendMessage(userId, converter!!.deserialize<Message>(frame))
    }
  }
}
