package org.renaissance.kotlin.ktor.client

import io.ktor.websocket.*
import kotlinx.coroutines.TimeoutCancellationException
import kotlinx.coroutines.channels.Channel
import kotlinx.coroutines.channels.ReceiveChannel
import kotlinx.coroutines.channels.SendChannel
import kotlinx.coroutines.test.runTest
import kotlin.coroutines.CoroutineContext
import kotlin.coroutines.EmptyCoroutineContext
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertFailsWith
import kotlin.time.Duration.Companion.milliseconds

/**
 * A minimal [WebSocketSession] that provides [incoming] frames from a channel
 * controlled by the test. [waitForMessage] uses no other member.
 */
private class FakeIncomingSession(
  override val incoming: ReceiveChannel<Frame>
) : WebSocketSession {
  override val coroutineContext: CoroutineContext = EmptyCoroutineContext
  override var masking: Boolean = false
  override var maxFrameSize: Long = Long.MAX_VALUE
  override val outgoing: SendChannel<Frame> get() = throw UnsupportedOperationException()
  override val extensions: List<WebSocketExtension<*>> = emptyList()
  override suspend fun send(frame: Frame): Unit = throw UnsupportedOperationException()
  override suspend fun flush() = Unit
  @Suppress("OVERRIDE_DEPRECATION")
  override fun terminate() = Unit
}

class WaitForMessageTest {
  /**
   * Creates a session with [frames] already queued in the incoming channel.
   * The channel is then closed, as it would be when a real connection ends,
   * unless [leaveOpen] is set, which makes receiving wait indefinitely.
   */
  private fun sessionOf(vararg frames: Frame, leaveOpen: Boolean = false): FakeIncomingSession {
    val channel = Channel<Frame>(capacity = 10)
    frames.forEach { channel.trySend(it) }
    if (!leaveOpen) channel.close()
    return FakeIncomingSession(channel)
  }

  @Test
  fun returnsTrueWhenMatchingFrameArrives() = runTest {
    val session = sessionOf(Frame.Text("no"), Frame.Text("yes"))

    val result = session.waitForMessage { (it as Frame.Text).readText() == "yes" }

    assertEquals(true, result)
  }

  @Test
  fun returnsFalseWhenChannelClosesBeforeMatch() = runTest {
    val session = sessionOf(Frame.Text("no"), Frame.Text("also no"))

    val result = session.waitForMessage { (it as Frame.Text).readText() == "yes" }

    assertEquals(false, result)
  }

  @Test
  fun throwsOnTimeoutWhenNothingArrives() = runTest {
    val session = sessionOf(leaveOpen = true)

    assertFailsWith<TimeoutCancellationException> {
      session.waitForMessage(timeout = 10.milliseconds) { true }
    }
  }
}
