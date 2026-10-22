package org.renaissance.kotlin.ktor.server

import io.ktor.websocket.*
import kotlinx.coroutines.CancellationException
import kotlinx.coroutines.channels.ClosedSendChannelException
import kotlinx.coroutines.currentCoroutineContext
import kotlinx.coroutines.isActive
import java.io.IOException

/**
 * Sends a [frame] to every socket in [this] list. Sockets that are already
 * closed ([ClosedSendChannelException]) or broken ([IOException]) are skipped
 * but not closed, because closing them is up to the code that opened them.
 * Any other exception propagates to the caller.
 *
 * A [CancellationException] needs to be handled separately, because sending
 * to a [WebSocketSession] cancelled by a different coroutine also throws it.
 * The exception is skipped only if the calling coroutine is still active.
 * Otherwise it comes from cancelling the calling coroutine and needs to
 * propagate.
 */
suspend fun List<WebSocketSession>.sendToEach(frame: Frame) {
  forEach { session ->
    try {
      session.send(frame.copy())
    } catch (_: ClosedSendChannelException) {
      // already gone; nothing to do here
    } catch (_: IOException) {
      // transport broken; nothing to do here
    } catch (t: CancellationException) {
      if (!currentCoroutineContext().isActive) throw t
      // session cancelled by a different coroutine; nothing to do here
    }
  }
}
