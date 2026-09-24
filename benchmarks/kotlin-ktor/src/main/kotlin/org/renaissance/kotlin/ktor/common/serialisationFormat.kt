package org.renaissance.kotlin.ktor.common

import kotlinx.serialization.json.Json
import kotlinx.serialization.modules.SerializersModule
import kotlinx.serialization.modules.polymorphic
import kotlinx.serialization.modules.subclass
import org.renaissance.kotlin.ktor.common.command.*

internal val serializationFormat = Json {
  serializersModule = SerializersModule {
    polymorphic(Command::class) {
      subclass(CreateChatCommand::class)
      subclass(CreateDirectMessageChatCommand::class)
      subclass(JoinChatCommand::class)
      subclass(AddUserToChatCommand::class)
      subclass(RenameUserCommand::class)
    }
    polymorphic(CommandReply::class) {
      subclass(CreateDirectMessageChatCommandReply::class)
    }
  }
}
