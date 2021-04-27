package io.reactors
package remote



import java.io.DataInputStream
import java.net._
import io.reactors.Reactor.ReactorThread
import io.reactors.test.ExtendedProperties
import org.scalacheck.Prop.forAllNoShrink
import org.scalacheck.Properties
import scala.concurrent.Await
import scala.concurrent.Promise
import scala.concurrent.duration.Duration
import scala.sys.process._
import scala.util.Success
import org.scalatest.funsuite.AnyFunSuite



class TcpImplementationTests extends AnyFunSuite {
  test("local tcp connection established") {
    val proc = Seq(
      "java", "-cp", sys.props("java.class.path"),
      "io.reactors.remote.TcpImplementationTest"
    ).run()
    Thread.sleep(3000)
    val socket = new Socket("localhost", 9500)
    val bufferSize = TcpImplementationTest.bufferSize
    val totalBatches = 1000000
    val buffer = new Array[Byte](bufferSize)
    try {
      var j = 0
      while (j < totalBatches) {
        val os = socket.getOutputStream
        var i = 0
        while (i < bufferSize) {
          buffer(i) = 1
          i += 1
        }
        os.write(buffer, 0, bufferSize)
        j += 1
      }
    } finally {
      println("producer: sent all the batches")
      Thread.sleep(3000)
      proc.destroy()
    }
    assert(true)
  }
}


object TcpImplementationTest {
  val bufferSize = 50000

  def main(args: Array[String]) {
    val serverSocket = new ServerSocket(9500)
    val clientSocket = serverSocket.accept()
    val is = clientSocket.getInputStream
    val buffer = new Array[Byte](bufferSize)
    val check_period = 50000
    var round = 0L
    var count = 0
    val startTime = System.nanoTime()
    do {
      count = is.read(buffer, 0, bufferSize)
      round += 1
      if (round % check_period == 0) {
        val totalTime = (System.nanoTime() - startTime) / 1000000.0
        println(s"time: ${round * bufferSize / totalTime} bytes/ms")
      }
    } while (count > 0)
  }
}


class TcpRemoteTest extends AnyFunSuite {
  val system = ReactorSystem.default("test-system")

  test("data chunk pool reallocates the same chunk") {
    val tcp = new TcpTransport(system)
    val buffer = new TcpTransport.SendBuffer(tcp, null, null)
    val data8 = tcp.dataPool.allocate(buffer, 3)
    assert(data8.totalSize == 8)
    data8.startPos = 2
    tcp.dataPool.deallocate(data8)
    val data8again = tcp.dataPool.allocate(buffer, 5)
    assert(data8 eq data8again)
    assert(data8again.startPos == 0)
  }

  test("data chunk pool returns correct sizes") {
    val tcp = new TcpTransport(system)
    val buffer = new TcpTransport.SendBuffer(tcp, null, null)
    val data8 = tcp.dataPool.allocate(buffer, 1)
    assert(data8.totalSize == 8)
    val data16 = tcp.dataPool.allocate(buffer, 10)
    assert(data16.totalSize == 16)
    val data32 = tcp.dataPool.allocate(buffer, 24)
    assert(data32.totalSize == 32)
    val data64 = tcp.dataPool.allocate(buffer, 41)
    assert(data64.totalSize == 64)
    val data128 = tcp.dataPool.allocate(buffer, 101)
    assert(data128.totalSize == 128)
    val data1024 = tcp.dataPool.allocate(buffer, 513)
    assert(data1024.totalSize == 1024)
    val data2048 = tcp.dataPool.allocate(buffer, 2048)
    assert(data2048.totalSize == 2048)
  }

  test("tcp channel marshals an object correctly") {
    val result = Promise[Boolean]()
    val serverSocket = new ServerSocket(0)
    val receiver = new Thread {
      setDaemon(true)
      override def run(): Unit = {
        val clientSocket = serverSocket.accept()
        val inputStream = new DataInputStream(clientSocket.getInputStream)
        val bytes = new Array[Byte](1024)
        var pos = 0
        while (pos < 68) {
          pos += inputStream.read(bytes, pos, 1024 - pos)
          // println(pos)
        }
        // println(bytes.mkString(", "))
        val buffer = new DataBuffer.Linked(1)
        buffer.rawInput = new DataBuffer.LinkedData(buffer, bytes)
        buffer.rawInput.startPos = 0
        buffer.rawInput.endPos = 1024
        assert(RuntimeMarshaler.unmarshal[String](buffer, false) == "test")
        assert(RuntimeMarshaler.unmarshal[String](buffer, false) == "main")
        assert(RuntimeMarshaler.unmarshal[String](buffer, true) == "hello")
        result.success(true)
      }
    }
    receiver.start()
    val sender = new ReactorThread {
      override def run() = {
        val tcp = new TcpTransport(system)
        val sysUrl = SystemUrl("tcp", "localhost", serverSocket.getLocalPort)
        val reactorUrl = ReactorUrl(sysUrl, "test")
        val channelUrl = ChannelUrl(reactorUrl, "main")
        val ch = tcp.newChannel[String](channelUrl)
        ch.send("hello")
        Reactor.onContextSwitch()
      }
    }
    sender.start()
    receiver.join()
    sender.join()
    assert(result.future.value == Some(Success(true)))
  }
}


class TcpRemoteCheck
extends Properties("TcpRemote") with ExtendedProperties {
  val sizes = detChoose(0, 1000)
  val smallSizes = detChoose(0, 100)
  val depths = detChoose(0, 12)

  def expectedSizeFor(size: Int) = {
    if (size <= 8) 8
    else if (size <= 16) 16
    else if (size <= 32) 32
    else if (size <= 64) 64
    else if (size <= 128) 128
    else if (size <= 256) 256
    else if (size <= 512) 512
    else if (size <= 1024) 1024
    else sys.error("unexpected size: " + size)
  }

  property("data pool chunking works correctly") = forAllNoShrink(sizes) { size =>
    val system = ReactorSystem.default("test-system")
    val tcp = new TcpTransport(system)
    val buffer = new TcpTransport.SendBuffer(tcp, null, null)
    try {
      val data = tcp.dataPool.allocate(buffer, if (size == 0) 1 else size)
      assert(data.totalSize == expectedSizeFor(size))
    } finally {
      system.shutdown()
    }
    true
  }
}
