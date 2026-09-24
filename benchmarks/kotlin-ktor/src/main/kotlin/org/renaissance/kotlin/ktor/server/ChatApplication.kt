package org.renaissance.kotlin.ktor.server

import io.ktor.serialization.*
import io.ktor.serialization.kotlinx.*
import io.ktor.server.application.*
import io.ktor.server.plugins.callloging.*
import io.ktor.server.plugins.defaultheaders.*
import io.ktor.server.routing.*
import io.ktor.server.websocket.*
import io.ktor.websocket.*
import kotlinx.coroutines.channels.consumeEach
import org.renaissance.kotlin.ktor.common.Message
import org.renaissance.kotlin.ktor.common.command.*
import org.renaissance.kotlin.ktor.common.sendSerialisedCommandReplyNative
import org.renaissance.kotlin.ktor.common.serializationFormat
import org.slf4j.event.Level

/**
 * In this case, we have a class holding our application state so it is not global and can be tested easier.
 */
class ChatApplication(numberOfChatsToSetup: Int) {
  /**
   * This class handles the logic of a [ChatServer].
   * With the standard handlers [ChatServer.registerUser] or [ChatServer.disconnectUserSocket] and operations like
   * sending messages to everyone or to specific people connected to the server.
   */
  private val server = ChatServer(numberOfChatsToSetup)

  fun getAvailableChatIds(): List<String> {
    return server.chats.keys().toList()
  }

  fun setup() {
    server.setupChats()
  }

  /**
   * This is the main method of application in this class.
   */
  fun Application.main() {
    /**
     * First, we install the plugins we need.
     * They are bound to the whole application
     * since this method has an implicit [Application] receiver that supports the [install] method.
     */
    // This adds Date and Server headers to each response, and would allow you to configure
    // additional headers served to each response.
    install(DefaultHeaders)
    // This uses the logger to log every call (request/response)
    install(CallLogging) {
      level = Level.TRACE
    }
    // This installs the WebSockets plugin to be able to establish a bidirectional configuration
    // between the server and the client
    install(WebSockets) {
      contentConverter = KotlinxWebsocketSerializationConverter(serializationFormat)
    }

    /**
     * Now we are going to define routes to handle specific methods + URLs for this application.
     */
    routing {

      // Defines a websocket `/ws` route that allows a protocol upgrade to convert a HTTP request/response request
      // into a bidirectional packetized connection.
      webSocket("/ws/{userId}") { // this: WebSocketSession ->

        // First of all we get the user id
        val userId = call.parameters["userId"]

        // We check that we actually have a userId. We should always have one,
        // since we have defined an interceptor before to set one.
        if (userId == null) {
          close(CloseReason(CloseReason.Codes.VIOLATED_POLICY, "No userId"))
          return@webSocket
        }

        // We notify that a member joined by calling the server handler [memberJoin].
        // This allows associating the session ID to a specific WebSocket connection.
        server.registerUser(userId, this)

        try {
          // We start receiving messages (frames).
          // Since this is a coroutine, it is suspended until receiving frames.
          // Once the connection is closed, this consumeEach will finish and the code will continue.
          incoming.consumeEach { frame ->
            // Frames can be [Text], [Binary], [Ping], [Pong], [Close].
            // We are only interested in textual messages, so we filter it.
            if (frame is Frame.Text) {
              // Now it is time to process the text sent from the user.
              // At this point, we have context about this connection,
              // the session, the text and the server.
              // So we have everything we need.
              receivedMessage(userId, frame)
            }
          }
        } finally {
          // Either if there was an error, or if the connection was closed gracefully,
          // we notified the server that the member had left.
          server.disconnectUserSocket(userId, this)
        }
      }
    }
  }

  /**
   * We received a message. Let's process it.
   */
  private suspend fun DefaultWebSocketServerSession.receivedMessage(userId: String, frame: Frame.Text) {
    val deserializedCommand = kotlin.runCatching { converter!!.deserialize<Command>(frame) }.getOrNull()
    when (deserializedCommand) {
      is RenameUserCommand -> {
        server.renameUser(userId, deserializedCommand.newName)
      }

      is JoinChatCommand -> {
        server.joinChat(deserializedCommand.chatId, userId)
      }

      is CreateChatCommand -> {
        val createdChatId = server.createChat(userId)
        sendSerialisedCommandReplyNative(CreateChatCommandReply(createdChatId))
      }

      is CreateDirectMessageChatCommand -> {
        val createdChat = server.createDirectMessageChat(
          userId,
          deserializedCommand.inviteeUserId,
        )
        sendSerialisedCommandReplyNative(CreateDirectMessageChatCommandReply(createdChat))
      }

      // Handle a normal message.
      else -> server.sendMessage(userId, converter!!.deserialize<Message>(frame))
    }
  }
}