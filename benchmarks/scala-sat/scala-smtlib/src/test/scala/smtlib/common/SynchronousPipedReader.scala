package smtlib
package common

import java.io.Reader
import scala.collection.mutable.ArrayBuffer
import scala.collection.mutable.Queue


/*
 * Implements Java Reader class and crash on any blocking call.
 * It is meant to be used to make sure the Lexer is not doing any
 * read call when not enough data is available.
 *
 * It provides method for directly writing to the pipe.
 */
class SynchronousPipedReader extends Reader {

  private val buffy = new Queue[Int]()

  override def close(): Unit = {}

  override def read(chars: Array[Char], off: Int, len: Int): Int = {
    var i = 0
    while(i < len) {
      chars(i + off) = buffy.dequeue().toChar
      i += 1
    }
    len
  }

  override def ready(): Boolean = buffy.nonEmpty

  def write(i: Int): Unit = {
    buffy.enqueue(i)
  }

  def write(str: String): Unit = str.toCharArray.foreach(this.write(_))

}
