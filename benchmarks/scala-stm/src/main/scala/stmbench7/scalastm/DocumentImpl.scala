/* scala-stm - (c) 2009-2011, Stanford University, PPL */

package stmbench7.scalastm

import scala.annotation.tailrec

import scala.concurrent.stm.Ref

import stmbench7.core.CompositePart
import stmbench7.core.Document

class DocumentImpl(id: Int, title: String, text0: String) extends Document {
  private val text = Ref(text0).single
  private val part = Ref(null: CompositePart).single

  override def getDocumentId: Int = id
  override def getTitle: String = title

  override def getCompositePart: CompositePart = part()
  override def setPart(v: CompositePart): Unit = { part() = v }

  override def nullOperation(): Unit = {}

  override def getText: String = text()
  override def searchText(symbol: Char): Int = searchText(text(), symbol, 0, 0)

  @tailrec private def searchText(s: String, c: Char, pos: Int, n: Int): Int = {
    val i = s.indexOf(c, pos)
    if (i < 0) n else searchText(s, c, i + 1, n + 1)
  }

  override def replaceText(from: String, to: String): Int = {
    val f = text transformIfDefined {
      case s if s.startsWith(from) => s.replaceFirst(from, to)
    }
    if (f) 1 else 0
  }

  override def textBeginsWith(prefix: String): Boolean = text().startsWith(prefix)
}
