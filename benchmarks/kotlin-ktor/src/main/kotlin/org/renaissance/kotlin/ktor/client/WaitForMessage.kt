package org.renaissance.kotlin.ktor.client

import io.ktor.client.plugins.websocket.*
import io.ktor.websocket.*
import kotlinx.coroutines.withTimeout
import kotlin.time.Duration
import kotlin.time.Duration.Companion.seconds

/**
 * Waits for a matching frame, up to [timeout].
 *
 * @return `true` if a matching frame arrived, `false` if the incoming channel
 *   closed before one did.
 * @throws kotlinx.coroutines.TimeoutCancellationException if no response was
 *   received within the [timeout].
 */
internal suspend fun DefaultClientWebSocketSession.waitForMessage(
  timeout: Duration = 30.seconds,
  match: suspend (Frame) -> Boolean
): Boolean {
  return withTimeout(timeout) {
    for (frame in incoming) {
      if (match(frame)) {
        return@withTimeout true
      }

      // Silently skips non-matching frames.
    }
    false
  }
}
