package org.renaissance.kotlin.ktor.common.command

import kotlinx.serialization.SerialName
import kotlinx.serialization.Serializable

@Suppress("PLUGIN_IS_NOT_ENABLED")
@Serializable
@SerialName("add_user_to_chat")
data class AddUserToChatCommand(val userId: String, val chatId: String) : Command {}
