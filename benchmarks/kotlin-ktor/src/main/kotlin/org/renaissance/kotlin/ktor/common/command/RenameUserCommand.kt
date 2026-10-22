package org.renaissance.kotlin.ktor.common.command

import kotlinx.serialization.SerialName
import kotlinx.serialization.Serializable

@Serializable
@SerialName("rename")
data class RenameUserCommand(val newName: String) : Command
