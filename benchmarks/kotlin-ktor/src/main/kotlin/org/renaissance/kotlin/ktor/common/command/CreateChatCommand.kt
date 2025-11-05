package org.renaissance.kotlin.ktor.common.command

import kotlinx.serialization.SerialName
import kotlinx.serialization.Serializable

@Suppress("PLUGIN_IS_NOT_ENABLED")
@Serializable
@SerialName("create_chat")
data object CreateChatCommand : Command {}

@Suppress("PLUGIN_IS_NOT_ENABLED")
@Serializable
@SerialName("create_chat_reply")
data class CreateChatCommandReply(val chatId: String) : CommandReply