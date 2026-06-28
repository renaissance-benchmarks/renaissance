package org.renaissance.kotlin.ktor.client

import io.ktor.client.plugins.websocket.*
import io.ktor.websocket.*
import kotlinx.coroutines.withTimeout
import kotlin.time.Duration
import kotlin.time.Duration.Companion.seconds

internal suspend fun DefaultClientWebSocketSession.waitForMessage(
  timeout: Duration = 30.seconds,
  match: suspend (Frame) -> Boolean
) {
  withTimeout(timeout) {
    for (frame in incoming) {
      if (match(frame)) {
        break
      }
    }
  }
}
