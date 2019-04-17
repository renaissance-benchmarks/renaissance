/* scala-stm - (c) 2009-2011, Stanford University, PPL */

package stmbench7.scalastm

import scala.concurrent.stm._
import scala.collection.immutable.WrappedString
import scala.annotation.tailrec
import stmbench7.core._

class ManualImpl(id: Int, title0: String, text0: String) extends Manual {
  val title = Ref(title0).single
  val text = Ref(text0).single
  val module = Ref(null : Module).single

  def getId = id
  def getTitle = title()
  def getText = text()
  def getModule = module()

  def setModule(v: Module) { module() = v }

  def countOccurences(ch: Char): Int = countOccurrences(ch)
  def countOccurrences(ch: Char): Int = countOccurrences(text(), ch, 0, 0)
  @tailrec private def countOccurrences(s: String, c: Char, pos: Int, n: Int): Int = {
    val i = s.indexOf(c, pos)
    if (i < 0) n else countOccurrences(s, c, i + 1, n + 1)
  }

  def checkFirstLastCharTheSame = {
    val t = text()
    if (t.charAt(0) == t.charAt(t.length - 1)) 1 else 0
  }

  def startsWith(ch: Char) = text().charAt(0) == ch

  def replaceChar(from: Char, to: Char) = {
    text.transform(_.replace(from, to))
    countOccurences(to)
  }
}
