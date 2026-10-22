package org.renaissance.kotlin.ktor.common

import io.ktor.serialization.*
import io.ktor.serialization.kotlinx.*
import io.ktor.websocket.*
import kotlinx.coroutines.test.runTest
import org.renaissance.kotlin.ktor.common.command.Command
import org.renaissance.kotlin.ktor.common.command.CommandReply
import org.renaissance.kotlin.ktor.common.command.CreateDirectMessageChatCommand
import org.renaissance.kotlin.ktor.common.command.CreateDirectMessageChatCommandReply
import org.renaissance.kotlin.ktor.common.command.JoinChatCommand
import org.renaissance.kotlin.ktor.common.command.RenameUserCommand
import kotlin.test.Test
import kotlin.test.assertEquals

//
// When decoding a Command or CommandReply fails, the benchmark keeps running:
// ChatApplication catches the exception and decodes the frame as a Message,
// which only produces a misleading error. These tests check the encoding and
// decoding directly.
//
class SerializationTest {
  @Test
  fun roundTripsMessageThroughConverter() = runTest {
    val converter = KotlinxWebsocketSerializationConverter(serializationFormat)
    val message = Message(chatId = "chat-1", content = "hi")

    val encoded = serializationFormat.encodeToString(message)
    val decoded = converter.deserialize<Message>(Frame.Text(encoded))

    assertEquals(message, decoded)
  }

  @Test
  fun roundTripsEachCommandSubtype() = runTest {
    val converter = KotlinxWebsocketSerializationConverter(serializationFormat)
    val commands = listOf(
      JoinChatCommand("chat-1"),
      RenameUserCommand("alice"),
      CreateDirectMessageChatCommand("bob")
    )

    for (command in commands) {
      val encoded = serializationFormat.encodeToString<Command>(command)
      val decoded = converter.deserialize<Command>(Frame.Text(encoded))
      assertEquals(command, decoded)
    }
  }

  @Test
  fun roundTripsCommandReply() = runTest {
    val converter = KotlinxWebsocketSerializationConverter(serializationFormat)
    val reply = CreateDirectMessageChatCommandReply("chat-1")

    val encoded = serializationFormat.encodeToString<CommandReply>(reply)
    val decoded = converter.deserialize<CommandReply>(Frame.Text(encoded))

    assertEquals(reply, decoded)
  }
}
