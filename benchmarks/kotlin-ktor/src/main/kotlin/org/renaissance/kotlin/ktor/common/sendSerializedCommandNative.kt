package org.renaissance.kotlin.ktor.common

import io.ktor.websocket.*
import kotlinx.serialization.PolymorphicSerializer
import org.renaissance.kotlin.ktor.common.command.Command

// we are using embedded version of a serialization plugin with limited reflection capabilities
// so we have to explicitly specify type serializer
internal suspend inline fun <reified T: Command> WebSocketSession.sendSerialisedCommandNative(cmd: T) {
  send(serializationFormat.encodeToString(PolymorphicSerializer(Command::class), cmd))
}