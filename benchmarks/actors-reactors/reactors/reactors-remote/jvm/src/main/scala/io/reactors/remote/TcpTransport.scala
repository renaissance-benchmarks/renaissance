package io.reactors
package remote



import java.io.IOException
import java.net.Socket
import java.util.concurrent.locks.ReentrantLock
import io.reactors
import io.reactors.DataBuffer.LinkedData
import io.reactors.Reactor.ReactorThread
import io.reactors.common.Monitor
import scala.annotation.tailrec
import scala.collection.concurrent.TrieMap



class TcpTransport(val system: ReactorSystem) extends Remote.Transport {
  private[reactors] val dataPool = new TcpTransport.VariablePool(
    system.config.int("transport.tcp.data-chunk-pool.parallelism")
  )
  private[reactors] val staging = new TcpTransport.Staging(this)

  override def newChannel[@spec(Int, Long, Double) T: Arrayable](
    url: ChannelUrl
  ): Channel[T] = {
    new TcpTransport.TcpChannel[T](this, url)
  }

  override def schema: String = "tcp"

  override def port: Int = system.bundle.urlMap(schema).url.port

  override def shutdown(): Unit = {
  }
}


object TcpTransport {
  private[reactors] val MAX_GROUPS = 8
  private[reactors] val MIN_SIZE = 8

  private[reactors] class FreeList {
    private var head: LinkedData = null
    // Aligning so that the free list is alone in the cache line.
    private val padding0 = 0L
    private val padding1 = 0L
    private val padding2 = 0L
    private val padding3 = 0L
    private val padding4 = 0L
    private val padding5 = 0L

    def allocate(buffer: SendBuffer): LinkedData = this.synchronized {
      val h = head
      if (h == null) null
      else {
        head = h.next
        h.buffer = buffer
        h.startPos = 0
        h.endPos = 0
        h
      }
    }

    def deallocate(data: LinkedData): Unit = this.synchronized {
      data.next = head
      data.buffer = null
      head = data
    }
  }

  private[reactors] abstract class FixedPool {
    def allocate(buffer: SendBuffer): LinkedData
    def deallocate(data: LinkedData): Unit
  }

  private[reactors] class FreeListFixedPool(val dataSize: Int, val parallelism: Int)
  extends FixedPool {
    private val freeLists = new Array[FreeList](parallelism)
    for (i <- 0 until parallelism) freeLists(i) = new FreeList

    def allocate(buffer: SendBuffer): LinkedData = {
      val initial = Thread.currentThread.getId.toInt % parallelism
      var slot = initial
      do {
        slot = (slot + 1) % parallelism
        val data = freeLists(slot).allocate(buffer)
        if (data != null) return data
      } while (slot != initial)
      new LinkedData(buffer, dataSize)
    }

    def deallocate(data: LinkedData): Unit = {
      val slot = Thread.currentThread.getId.toInt % parallelism
      freeLists(slot).deallocate(data)
    }
  }

  private[reactors] class HeapPool(val dataSize: Int) extends FixedPool {
    override def allocate(buffer: SendBuffer): LinkedData = {
      return new LinkedData(buffer, dataSize)
    }

    override def deallocate(data: LinkedData): Unit = {}
  }

  private[reactors] class VariablePool(val parallelism: Int) {
    private[reactors] val fixedPools = Array.tabulate(MAX_GROUPS) {
      i => new FreeListFixedPool(MIN_SIZE << i, parallelism)
    }

    private[reactors] def fixedPool(minNextSize: Int): FixedPool = {
      val highbit = Integer.highestOneBit(if (minNextSize > 0) minNextSize else 1)
      require((highbit << 1) != 0)
      val size = if (highbit == minNextSize) highbit else highbit << 1
      val correctedSize = math.max(MIN_SIZE, size)
      val group = Integer.numberOfTrailingZeros(correctedSize / MIN_SIZE)
      if (group < fixedPools.length) fixedPools(group)
      else new HeapPool(correctedSize)
    }

    def allocate(buffer: SendBuffer, minNextSize: Int): LinkedData = {
      fixedPool(minNextSize).allocate(buffer)
    }

    def deallocate(old: LinkedData): Unit = {
      require(old.totalSize == Integer.highestOneBit(old.totalSize))
      fixedPool(old.totalSize).deallocate(old)
    }
  }

  private[reactors] class SendBuffer(
    val tcp: TcpTransport,
    var destination: Destination,
    var channel: TcpChannel[_]
  ) extends DataBuffer.Linked(128) {
    def attachTo(newChannel: TcpChannel[_]) = {
      channel = newChannel
      destination = tcp.staging.resolve(channel.channelUrl.reactorUrl.systemUrl)
    }

    protected[reactors] override def allocateData(minNextSize: Int): LinkedData = {
      tcp.dataPool.allocate(this, minNextSize)
    }

    protected[reactors] override def deallocateData(old: LinkedData): Unit = {
      // The data chunk is dispatched to the connection pool,
      // and must be deallocated by the connection pool.
    }

    protected[reactors] override def onWriteNext(old: LinkedData): Unit = {
      super.onWriteNext(old)
      rawInput = old.next
      old.next = null
      destination.send(old)
    }

    protected[reactors] override def onReadNext(old: LinkedData): Unit = {
      sys.error("Unsupported operation exception.")
    }

    override def flush(): Unit = {
      assert(rawInput == rawOutput)
      if (rawInput.remainingReadSize > 0) {
        rawOutput.writeNext(rawOutput.totalSize / 2)
      }
    }
  }

  private[reactors] class TcpChannel[@spec(Int, Long, Double) T](
    @transient var tcp: TcpTransport,
    val channelUrl: ChannelUrl
  ) extends Channel[T] {
    def send(x: T): Unit = {
      val reactorThread = Reactor.currentReactorThread
      if (reactorThread.isInstanceOf[ReactorThread]) {
        // val context = reactorThread.marshalContext
        var dataBuffer = reactorThread.dataBuffer

        // Initialize data buffer if necessary.
        if (dataBuffer == null) {
          reactorThread.dataBuffer = new SendBuffer(tcp, null, null)
          dataBuffer = reactorThread.dataBuffer
        }

        // Check if the data buffer refers to this channel.
        val sendBuffer = dataBuffer.asInstanceOf[SendBuffer]
        if (sendBuffer.channel ne this) {
          sendBuffer.attachTo(this)
        }

        // Use the runtime marshaler to serialize the object.
        RuntimeMarshaler.marshal(channelUrl.reactorUrl.name, sendBuffer, false)
        RuntimeMarshaler.marshal(channelUrl.anchor, sendBuffer, false)
        RuntimeMarshaler.marshal(x, sendBuffer, true)
      } else {
        ???
      }
    }
  }

  private[reactors] class Staging(val tcp: TcpTransport) {
    private[reactors] val destinations = TrieMap[SystemUrl, Destination]()

    def resolve(systemUrl: SystemUrl): Destination = {
      val dst = destinations.lookup(systemUrl)
      if (dst != null) dst
      else {
        destinations.getOrElseUpdate(systemUrl, new Destination(systemUrl, tcp))
      }
    }
  }

  private[reactors] class Destination(
    val url: SystemUrl,
    val tcp: TcpTransport
  ) {
    object dataQueue {
      private val monitor = new Monitor
      private var head: LinkedData = null
      private var tail: LinkedData = null

      def enqueue(data: LinkedData) = monitor.synchronized {
        if (head == null) {
          head = data
          tail = data
        } else {
          tail.next = data
          tail = data
        }
      }

      def dequeue(): LinkedData = monitor.synchronized {
        if (tail == null) {
          null
        } else {
          val result = head
          head = head.next
          if (head == null) tail = null
          result.next = null
          result
        }
      }
    }

    object connection {
      private val lock: ReentrantLock = new ReentrantLock
      private var socket: Socket = null

      @tailrec def repeatFlush(): Unit = {
        val data = dataQueue.dequeue()
        if (data == null) return

        try {
          if (socket == null) {
            socket = new Socket(url.host, url.port)
          }
          socket.getOutputStream.write(data.raw, data.startPos, data.remainingReadSize)
          data.startPos += data.remainingReadSize
        } catch {
          case NonLethal(_) =>
            if (socket != null) {
              try {
                socket.close()
              } catch {
                case NonLethal(_) =>
              } finally {
                socket = null
              }
            }
            return
        }
        repeatFlush()
      }

      def flush() = {
        if (lock.tryLock()) {
          try repeatFlush()
          finally lock.unlock()
        }
      }
    }

    def send(data: LinkedData) = {
      dataQueue.enqueue(data)
      connection.flush()
    }
  }

}
