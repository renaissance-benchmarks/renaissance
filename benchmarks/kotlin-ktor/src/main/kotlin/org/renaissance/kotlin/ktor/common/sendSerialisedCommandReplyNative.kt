package org.renaissance.kotlin.ktor.common

import io.ktor.websocket.*
import kotlinx.serialization.PolymorphicSerializer
import org.renaissance.kotlin.ktor.common.command.CommandReply

internal suspend inline fun <reified T: CommandReply> WebSocketSession.sendSerialisedCommandReplyNative(cmd: T) {
  send(serializationFormat.encodeToString(PolymorphicSerializer(CommandReply::class), cmd))
}