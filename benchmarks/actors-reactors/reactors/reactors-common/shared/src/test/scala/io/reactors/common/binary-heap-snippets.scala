package io.reactors.common



import org.scalatest._
import org.scalatest.matchers.should.Matchers



trait BinaryHeapSnippets extends Matchers {

  def testEnqueueDequeue(size: Int) {
    val heap = new BinaryHeap[Int]

    for (x <- 0 until size) {
      heap.enqueue(x)
      heap.isEmpty should equal (false)
    }
    heap.size should equal (size)
    for (x <- 0 until size) {
      heap.isEmpty should equal (false)
      heap.dequeue() should equal (x)
    }
    heap.isEmpty should equal (true)
  }

  def testTraverseElements(size: Int) {
    import scala.collection._
    val heap = new BinaryHeap[Int]
    val check = mutable.Set[Int]()

    for (x <- 0 until size) heap.enqueue(x)
    for (x <- heap) check += x

    check should equal ((0 until size).toSet)
  }

  def testSort(size: Int) {
    val shuffled = scala.util.Random.shuffle((0 until 1500).toList)
    val heap = new BinaryHeap[Int]

    for (x <- shuffled) heap.enqueue(x)

    for (x <- 0 until size) heap.dequeue() should equal (x)
  }

}




