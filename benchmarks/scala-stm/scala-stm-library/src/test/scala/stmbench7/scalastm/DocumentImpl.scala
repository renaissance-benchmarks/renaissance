/* scala-stm - (c) 2009-2011, Stanford University, PPL */

package stmbench7.scalastm

import scala.annotation.tailrec
import scala.concurrent.stm._
import stmbench7.core._

class DocumentImpl(id: Int, title: String, text0: String) extends Document {
  val text = Ref(text0).single
  val part = Ref(null : CompositePart).single

  def getDocumentId = id
  def getTitle = title

  def getCompositePart = part()
  def setPart(v: CompositePart) { part() = v }

  def nullOperation() {}

  def getText = text()
  def searchText(symbol: Char): Int = searchText(text(), symbol, 0, 0)
  @tailrec private def searchText(s: String, c: Char, pos: Int, n: Int): Int = {
    val i = s.indexOf(c, pos)
    if (i < 0) n else searchText(s, c, i + 1, n + 1)
  }
  def replaceText(from: String, to: String) = {
    val f = text transformIfDefined {
      case s if s.startsWith(from) => s.replaceFirst(from, to)
    }
    if (f) 1 else 0
  }
  def textBeginsWith(prefix: String) = text().startsWith(prefix)
}
