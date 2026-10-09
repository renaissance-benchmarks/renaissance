package org.renaissance.kotlin.ktor.common

import kotlinx.serialization.Serializable

@Suppress("PLUGIN_IS_NOT_ENABLED") // IDE cannot detect serialization compiler plugin, that is enabled via sbt
@Serializable
data class Message(val chatId: String, val content: String)
