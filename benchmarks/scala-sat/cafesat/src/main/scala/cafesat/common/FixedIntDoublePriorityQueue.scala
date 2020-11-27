package cafesat.common

/** Represents a queue of Int values sorted according to a score value.
  *
  * Scores are Double value and initialized to 0, while the elements are initialized
  * from 0 to length-1.
  *
  * Elements are fixed, taking value from 0 to maxSize-1.
  *
  * When an element is removed, the queue remembers its score, it is still
  * possible to augment its score, and when the element is added back, it
  * takes a position according to its current score.
  */
class FixedIntDoublePriorityQueue(val maxSize: Int) {

  private var _size = maxSize

  def size: Int = _size

  //uses 1-indexed arrays, this makes the parent/child relationship simpler and more efficient to compute
  private val heapScores: Array[Double] = new Array(1+size)
  private val heapElements: Array[Int] = new Array(1+size)

  //index is still 0-indexed
  private val index: Array[Int] = new Array(size)

  def apply(id: Int) = heapElements(id)

  //and so are elements
  for(i <- 1 to size) {
    heapElements(i) = i-1
    index(i-1) = i
  }

  //careful, should not modify heap(0) since it is used by caller
  private def siftUp(pos: Int, score: Double): Unit = {
    val element = heapElements(pos)

    var i = pos
    while(i != 1 && heapScores(i/2) < score) {
      heapScores(i) = heapScores(i/2)
      val parentElement = heapElements(i/2)
      heapElements(i) = parentElement
      index(parentElement) = i
      i = i/2
    }

    heapScores(i) = score
    heapElements(i) = element
    index(element) = i
  }

   def siftDown(pos: Int, score: Double): Unit = {
    val element = heapElements(pos)

    var i = pos
    var correctPos = false
    do {
      val left = 2*i
      val right = left + 1
      if(right <= size) { //two children
        val scoreLeft = heapScores(left)
        val scoreRight = heapScores(right)
        if(scoreLeft > score || scoreRight > score) {
          if(scoreLeft > scoreRight) {
            heapScores(i) = scoreLeft
            val parentElement = heapElements(left)
            heapElements(i) = parentElement
            index(parentElement) = i
            i = left
          } else {
            heapScores(i) = scoreRight
            val parentElement = heapElements(right)
            heapElements(i) = parentElement
            index(parentElement) = i
            i = right
          }
        } else { //keep element in place
          correctPos = true
        }
      } else if(left <= size) {//only left child
        val scoreLeft = heapScores(left)
        if(score < scoreLeft) {
          heapScores(i) = scoreLeft
          val parentElement = heapElements(left)
          heapElements(i) = parentElement
          index(parentElement) = i
          i = left
        } else {
          correctPos = true
        }
      } else { //element is a leaf
        correctPos = true
      }
    } while(!correctPos)

    heapScores(i) = score
    heapElements(i) = element
    index(element) = i
  }

  /** Increments the score of an element in the queue.
    *
    * @param el the element whose score should be incremented
    * @param offset the increment value, should be positive
    * @return the new score of the element
    * @throws IllegalArgumentException if offset < 0
    */
  def incScore(el: Int, offset: Double): Double = {
    require(offset >= 0)
    val pos = index(el)
    val newScore = heapScores(pos) + offset
    if(pos <= size)
      siftUp(pos, newScore)
    else
      heapScores(pos) = newScore
    newScore
  }

  /** Rescales every score by the factor
    *
    * This does not impact the ordering of the queue.
    *
    * @param factor the factor to multiply each score with
    */
  def rescaleScores(factor: Double): Unit = {
    var i = 0
    while(i < maxSize) {
      heapScores(i) *= factor
      i += 1
    }
  }

  def isEmpty: Boolean = _size == 0

  def max: Int = heapElements(1)

  def deleteMax: Int = {
    if(size == 1) {
      _size -= 1
      heapElements(1)
    } else {
      val maxElement = heapElements(1)
      heapScores(0) = heapScores(1)
      heapElements(1) = heapElements(_size)
      val score = heapScores(_size)
      index(heapElements(1)) = 1
      heapElements(_size) = maxElement
      heapScores(_size) = heapScores(0)
      index(maxElement) = _size
      _size -= 1
      siftDown(1, score)
      maxElement
    }
  }

  //insert will simply ignore if el is already in the heap
  //it keeps the element at its current position and score
  def insert(el: Int) = {
    val pos = index(el)
    if(pos == size + 1) {
      //then already at correct position for sifting up
      _size += 1
      siftUp(pos, heapScores(pos))
    } else if(pos > size + 1) {
      //make space for the new leaf
      heapScores(0) = heapScores(size+1)
      heapElements(0) = heapElements(size+1)

      _size += 1
      heapElements(size) = heapElements(pos)
      siftUp(size, heapScores(pos))

      heapScores(pos) = heapScores(0)
      heapElements(pos) = heapElements(0)
      index(heapElements(pos)) = pos
    }
  }

  def remove(el: Int) = {
    val pos = index(el)
    require(pos <= size)
    if(pos == size) {
      _size -= 1
    } else {
      heapScores(0) = heapScores(pos)
      heapElements(pos) = heapElements(size)
      val score = heapScores(size)
      _size -= 1
      if(score > heapScores(pos/2))
        siftUp(pos, score)
      else
        siftDown(pos, score)
      heapElements(size + 1) = el
      heapScores(size + 1) = heapScores(0)
      index(heapElements(size+1)) = size+1
    }
  }


  /*
   * Verifies that the invariant is true.
   * Meant to be called internally by the testing framework
   * Not efficient!
   */
  def invariant: Boolean = {
    var valid = true
    for(i <- 1 to size) {
      var left = i*2
      var right = i*2+1
      valid &&= (left > size || heapScores(left) <= heapScores(i))
      valid &&= (right > size || heapScores(right) <= heapScores(i))
      valid &&= (index(heapElements(i)) == i)
    }
    valid
  }

  /*
   * Meant to be called internally for debugging purpose
   * Not efficient!
   */
  override def toString = {
    heapScores.tail.mkString("Scores: [", ", ", "]\n") +
    heapElements.tail.mkString("Elements: [", ", ", "]\n") +
    index.mkString("Index: [", ", ", "]\n")
  }

}
