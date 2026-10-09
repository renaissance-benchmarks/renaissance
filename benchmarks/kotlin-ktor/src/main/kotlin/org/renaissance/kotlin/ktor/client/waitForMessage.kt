package org.renaissance.kotlin.ktor.client

import io.ktor.client.plugins.websocket.*
import io.ktor.websocket.*

internal suspend fun DefaultClientWebSocketSession.waitForMessage(match: suspend (Frame) -> Boolean) {
  for (frame in incoming) {
    if (match(frame)) {
      break
    }
  }
}