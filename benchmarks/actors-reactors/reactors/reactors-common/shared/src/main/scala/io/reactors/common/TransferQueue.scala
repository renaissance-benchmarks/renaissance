package io.reactors
package common






class TransferQueue[T: Arrayable](val monitor: AnyRef) {
  private val queue = new UnrolledRing[T]

  def isEmpty: Boolean = monitor.synchronized {
    queue.isEmpty
  }

  def waitUntilDequeue(): T = monitor.synchronized {
    while (queue.isEmpty) monitor.wait()
    queue.dequeue()
  }

  def enqueue(x: T): Unit = monitor.synchronized {
    queue.enqueue(x)
    monitor.notifyAll()
  }
}
