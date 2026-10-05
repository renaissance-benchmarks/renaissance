package org.renaissance.kotlin.ktor.common

import io.ktor.websocket.*
import kotlinx.serialization.PolymorphicSerializer
import org.renaissance.kotlin.ktor.common.command.Command
import org.renaissance.kotlin.ktor.common.command.CommandReply

// we are using embedded version of a serialization plugin with limited reflection capabilities
// so we have to explicitly specify type serializer
internal suspend fun <T: Command> WebSocketSession.sendSerializedCommandNative(cmd: T) {
  send(serializationFormat.encodeToString(PolymorphicSerializer(Command::class), cmd))
}

internal suspend fun <T: CommandReply> WebSocketSession.sendSerializedCommandReplyNative(cmd: T) {
  send(serializationFormat.encodeToString(PolymorphicSerializer(CommandReply::class), cmd))
}
