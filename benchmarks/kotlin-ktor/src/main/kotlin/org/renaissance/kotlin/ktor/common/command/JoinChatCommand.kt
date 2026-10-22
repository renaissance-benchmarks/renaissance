package org.renaissance.kotlin.ktor.common.command

import kotlinx.serialization.SerialName
import kotlinx.serialization.Serializable

@Serializable
@SerialName("join_chat")
data class JoinChatCommand(val chatId: String): Command {}
