package org.renaissance.kotlin.ktor.common.command

import kotlinx.serialization.SerialName
import kotlinx.serialization.Serializable

@Suppress("PLUGIN_IS_NOT_ENABLED")
@Serializable
@SerialName("create_direct_message_chat")
data class CreateDirectMessageChatCommand(val inviteeUserId: String) : Command

@Suppress("PLUGIN_IS_NOT_ENABLED")
@Serializable
@SerialName("create_direct_message_chat_reply")
data class CreateDirectMessageChatCommandReply(val chatId: String) : CommandReply