package org.renaissance.kotlin.ktor.common.command

import kotlinx.serialization.SerialName
import kotlinx.serialization.Serializable

@Serializable
@SerialName("create_direct_message_chat")
data class CreateDirectMessageChatCommand(val inviteeUserId: String) : Command

@Serializable
@SerialName("create_direct_message_chat_reply")
data class CreateDirectMessageChatCommandReply(val chatId: String) : CommandReply