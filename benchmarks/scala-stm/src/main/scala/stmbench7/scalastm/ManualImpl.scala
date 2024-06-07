/* scala-stm - (c) 2009-2011, Stanford University, PPL */

package stmbench7.scalastm

import scala.annotation.tailrec

import scala.concurrent.stm.Ref

import stmbench7.core.Manual
import stmbench7.core.Module

class ManualImpl(id: Int, title0: String, text0: String) extends Manual {
  private val title = Ref(title0).single
  private val text = Ref(text0).single
  private val module = Ref(null: Module).single

  override def getId: Int = id
  override def getTitle: String = title()
  override def getText: String = text()
  override def getModule: Module = module()

  override def setModule(v: Module): Unit = { module() = v }

  override def countOccurences(ch: Char): Int = countOccurrences(text(), ch, 0, 0)

  @tailrec private def countOccurrences(s: String, c: Char, pos: Int, n: Int): Int = {
    val i = s.indexOf(c, pos)
    if (i < 0) n else countOccurrences(s, c, i + 1, n + 1)
  }

  override def checkFirstLastCharTheSame: Int = {
    val t = text()
    if (t.charAt(0) == t.charAt(t.length - 1)) 1 else 0
  }

  override def startsWith(ch: Char): Boolean = text().charAt(0) == ch

  override def replaceChar(from: Char, to: Char): Int = {
    text.transform(_.replace(from, to))
    countOccurences(to)
  }
}
