package cafesat.common

/** Implements a stack of Int of fixed maximum size.
  *
  * This is an efficient data structure for representing the trail
  * in a SAT solver. Though it can be used to represent a stack of
  * Int with a fixed maximum size.
  *
  * The interface should only export efficient operations, to avoid
  * people accidently using operations (such as map or takeWhile) that
  * are conveninent but not necessarly very fast. The rational is mostly
  * to avoid overhead (creating a closure, dynamic allocation, etc), if an
  * operation is O(n) (such as the contains operator) it is fine to be
  * provided as this does not involve extra overhead.
  *
  * @constructor Initializes an empty stack with space to grow up to maxSize
  * @param maxSize the maximum size the stack can grow. Should be positive
  * @throws IllegalArgumentException if maxSize < 0
  */
class FixedIntStack(maxSize: Int) {
  require(maxSize >= 0)

  private val stack: Array[Int] = new Array(maxSize)
  private var topIndex: Int = -1

  def push(el: Int): Unit = {
    topIndex += 1
    stack(topIndex) = el
  }
  def pop(): Int = {
    val res = stack(topIndex)
    topIndex -= 1
    res
  }
  def top: Int = stack(topIndex)
  def isEmpty: Boolean = topIndex == -1
  def contains(el: Int): Boolean = {
    var i = topIndex
    while(i >= 0) {
      if(stack(i) == el)
        return true
      i -= 1
    }
    false
  }

  /** Provides checked access to an element in the stack.
    *
    * Will throw an exception if the element is outside the actual
    * content of the stack.
    *
    * @param i the index of the element in the stack, starting at 0
    */
  def get(i: Int): Int = {
    assert(i >= 0 && i <= topIndex)
    stack(i)
  }

  /** Provides unchecked access to an element in the stack.
    *
    * The access is unchecked in the sense that we do not make sure the
    * element is not outside the current range of the stack, and could
    * return a random value if it is bigger than this.size but smaller than
    * maxSize.
    * 
    * @param i the index of the element in the stack, starting at 0
    */
  def apply(i: Int): Int = stack(i)

  def size: Int = topIndex + 1

}
