package org.renaissance.kotlin.ktor.common

import io.ktor.websocket.*
import kotlinx.serialization.json.Json
import org.renaissance.kotlin.ktor.common.command.Command
import org.renaissance.kotlin.ktor.common.command.CommandReply

// Client and server must use the same format.
val serializationFormat: Json = Json

//
// The type parameter of encodeToString needs to be fixed to force the use of
// the generic serializer for the Command and CommandReply interfaces. Having
// the compiler infer the type would use the serializer for the concrete class,
// sending only the class data without type information.
//
internal suspend fun WebSocketSession.sendSerializedCommandNative(cmd: Command) {
  send(serializationFormat.encodeToString<Command>(cmd))
}

internal suspend fun WebSocketSession.sendSerializedCommandReplyNative(cmd: CommandReply) {
  send(serializationFormat.encodeToString<CommandReply>(cmd))
}
