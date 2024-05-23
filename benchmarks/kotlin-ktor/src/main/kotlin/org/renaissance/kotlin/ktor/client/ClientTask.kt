package org.renaissance.kotlin.ktor.client

import io.ktor.client.plugins.websocket.*

interface ClientTask {
  suspend fun setup(session: DefaultClientWebSocketSession) {}
  suspend fun run(session: DefaultClientWebSocketSession) {}
}