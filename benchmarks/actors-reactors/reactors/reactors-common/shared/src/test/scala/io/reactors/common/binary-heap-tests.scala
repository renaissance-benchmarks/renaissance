package io.reactors.common



import org.scalatest._
import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers



class BinaryHeapSpec extends AnyFlatSpec with Matchers with BinaryHeapSnippets {

  "BinaryHeap" should "be empty" in {
    val heap = new BinaryHeap[Int]

    heap.isEmpty should be (true)
    heap.nonEmpty should be (false)
  }

  it should "enqueue and dequeue an element" in {
    val heap = new BinaryHeap[Int]

    heap.enqueue(111)
    heap.isEmpty should be (false)
    heap.head should be (111)
    heap.dequeue() should be (111)
    heap.isEmpty should be (true)
  }

  it should "enqueue and dequeue many elements" in {
    testEnqueueDequeue(150)
    testEnqueueDequeue(1500)
  }

  it should "traverse elements" in {
    testTraverseElements(10)
    testTraverseElements(50)
    testTraverseElements(1500)
  }

  it should "sort elements" in {
    testSort(150)
    testSort(1500)
  }

}
