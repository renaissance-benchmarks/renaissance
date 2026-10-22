package org.renaissance.kotlin.ktor.client

import io.ktor.client.plugins.websocket.DefaultClientWebSocketSession
import org.renaissance.kotlin.ktor.common.User
import org.renaissance.kotlin.ktor.common.command.RenameUserCommand
import org.renaissance.kotlin.ktor.common.sendSerializedCommandNative

/**
 * Sets this client's display name.
 */
class RenameClientTask : ClientTask {
  override suspend fun run(session: DefaultClientWebSocketSession, user: User): Boolean {
    session.sendSerializedCommandNative(RenameUserCommand(user.name))
    return true
  }
}
