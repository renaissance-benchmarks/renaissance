package org.renaissance.kotlin.ktor.common.command

import kotlinx.serialization.SerialName
import kotlinx.serialization.Serializable

@Suppress("PLUGIN_IS_NOT_ENABLED")
@Serializable
@SerialName("rename")
data class RenameUserCommand(val newName: String) : Command
