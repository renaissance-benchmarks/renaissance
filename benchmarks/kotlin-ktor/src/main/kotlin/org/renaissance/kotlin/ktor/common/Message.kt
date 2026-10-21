package org.renaissance.kotlin.ktor.common

import kotlinx.serialization.Serializable

@Serializable
data class Message(val chatId: String, val content: String)
