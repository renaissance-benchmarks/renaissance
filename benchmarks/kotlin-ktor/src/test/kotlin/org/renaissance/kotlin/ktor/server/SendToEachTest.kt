package org.renaissance.kotlin.ktor.server

import io.ktor.websocket.*
import kotlinx.coroutines.CancellationException
import kotlinx.coroutines.channels.ClosedSendChannelException
import kotlinx.coroutines.channels.ReceiveChannel
import kotlinx.coroutines.channels.SendChannel
import kotlinx.coroutines.job
import kotlinx.coroutines.launch
import kotlinx.coroutines.test.runTest
import kotlin.coroutines.CoroutineContext
import kotlin.coroutines.EmptyCoroutineContext
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertFailsWith
import kotlin.test.assertTrue

/**
 * A minimal [WebSocketSession] that passes each sent frame to [onSend], so
 * that a test can make sending fail or record the sent frames. [sendToEach]
 * uses no other member.
 */
private class FakeSendSession(
  private val onSend: suspend (Frame) -> Unit
) : WebSocketSession {
  override val coroutineContext: CoroutineContext = EmptyCoroutineContext
  override var masking: Boolean = false
  override var maxFrameSize: Long = Long.MAX_VALUE
  override val incoming: ReceiveChannel<Frame> get() = throw UnsupportedOperationException()
  override val outgoing: SendChannel<Frame> get() = throw UnsupportedOperationException()
  override val extensions: List<WebSocketExtension<*>> = emptyList()
  override suspend fun send(frame: Frame) = onSend(frame)
  override suspend fun flush() = Unit
  @Suppress("OVERRIDE_DEPRECATION")
  override fun terminate() = Unit
}

class SendToEachTest {
  @Test
  fun skipsAlreadyClosedSocket() = runTest {
    val received = mutableListOf<Frame>()
    val closed = FakeSendSession { throw ClosedSendChannelException("already closed") }
    val healthy = FakeSendSession { received += it }

    listOf(closed, healthy).sendToEach(Frame.Text("hi"))

    assertEquals(1, received.size)
  }

  @Test
  fun skipsSocketWithBrokenTransport() = runTest {
    val received = mutableListOf<Frame>()
    val broken = FakeSendSession { throw java.io.IOException("connection reset") }
    val healthy = FakeSendSession { received += it }

    listOf(broken, healthy).sendToEach(Frame.Text("hi"))

    assertEquals(1, received.size)
  }


  //
  // The next two tests cover the two outcomes of catching a
  // CancellationException in sendToEach: skipping the exception and sending
  // to the remaining sockets, or stopping and propagating the exception.
  // Two things to keep in mind:
  //
  // - Both tests call sendToEach inside a coroutine (provided by runTest or
  //   started by launch), so currentCoroutineContext() in sendToEach refers
  //   to that coroutine.
  // - A coroutine is marked cancelled before the resulting
  //   CancellationException is thrown, so isActive cannot be true while
  //   catching a CancellationException caused by cancelling that coroutine.
  //

  @Test
  fun skipsCancellationThatIsNotOurs() = runTest {
    //
    // Nothing cancels the test coroutine, so it is still active when
    // sendToEach catches the CancellationException from the first socket.
    // The exception is therefore skipped and the frame is still sent to the
    // second socket.
    //
    val received = mutableListOf<Frame>()
    val cancelled = FakeSendSession { throw CancellationException("channel cancelled") }
    val healthy = FakeSendSession { received += it }

    listOf(cancelled, healthy).sendToEach(Frame.Text("hi"))

    assertEquals(1, received.size)
  }

  @Test
  fun rethrowsCancellationThatIsOurs() = runTest {
    //
    // The send callback of the first socket cancels the coroutine that calls
    // sendToEach and then throws the CancellationException that sending on a
    // cancelled channel would throw. The coroutine is no longer active, so
    // sendToEach needs to stop sending and propagate the exception, and the
    // send callback of the second socket must never be called.
    //
    var secondSocketReached = false

    val job = launch {
      val cancelling = FakeSendSession {
        this@launch.coroutineContext.job.cancel()
        throw CancellationException("channel cancelled")
      }
      val healthy = FakeSendSession { secondSocketReached = true }
      listOf(cancelling, healthy).sendToEach(Frame.Text("hi"))
    }

    job.join()

    assertTrue(job.isCancelled)
    assertEquals(false, secondSocketReached)
  }

  @Test
  fun propagatesUnexpectedException() = runTest {
    val broken = FakeSendSession { throw IllegalStateException("bug") }

    assertFailsWith<IllegalStateException> {
      listOf(broken).sendToEach(Frame.Text("hi"))
    }
  }
}
