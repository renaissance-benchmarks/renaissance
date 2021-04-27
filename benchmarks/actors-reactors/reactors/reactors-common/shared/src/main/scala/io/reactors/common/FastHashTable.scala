package io.reactors
package common






/** Support hash table for fast operations.
 */
class FastHashTable[M >: Null <: AnyRef] {
  protected[reactors] var table = new Array[Ref[M]](16)
  protected[reactors] var size = 0
  protected[reactors] var threshold = 4

  private def index(h: Int) = h & (table.length - 1)

  private def findEntryImpl(mux: M): Ref[M] = {
    var h = index(mux.hashCode)
    var entry = table(h)
    while (null != entry && entry.get != mux) {
      h = (h + 1) % table.length
      entry = table(h)
    }
    entry
  }

  def addEntry(mux: M) : Boolean = {
    var h = index(mux.hashCode)
    var entry = table(h)
    while (null != entry) {
      if (entry.get == mux) return false
      h = (h + 1) % table.length
      entry = table(h)
    }
    table(h) = new Ref(mux)
    size = size + 1
    if (size >= threshold) growTable()
    true
  }

  protected[reactors] def removeEntryAt(idx: Int, mux: M): Boolean = {
    def precedes(i: Int, j: Int) = {
      val d = table.length >> 1
      if (i <= j) j - i < d
      else i - j > d
    }
    var h = idx
    var entry = table(h)
    while (null != entry) {
      if (entry.get == mux) {
        var h0 = h
        var h1 = (h0 + 1) % table.length
        var found = false
        while (!found) {
          val elem = if (table(h1) == null) null else table(h1).get
          if (elem != null) {
            val h2 = index(elem.hashCode)
            if (h2 != h1 && precedes(h2, h0)) {
              table(h0) = table(h1)
              h0 = h1
            }
            h1 = (h1 + 1) % table.length
          } else found = true
        }
        table(h0) = null
        size -= 1
        return true
      }
      h = (h + 1) % table.length
      entry = table(h)
    }
    false
  }

  def removeEntry(mux: M): Boolean = {
    val h = index(mux.hashCode)
    removeEntryAt(h, mux)
  }

  def invalidateEntry(mux: M) {
    val w = findEntryImpl(mux)
    if (w != null) w.clear()
  }

  private def growTable() {
    val oldtable = table
    table = new Array[Ref[M]](table.length * 2)
    size = 0
    threshold = (table.length * 0.45).toInt
    var i = 0
    while (i < oldtable.length) {
      val entry = oldtable(i)
      if (null != entry && null != entry.get) addEntry(entry.get)
      i += 1
    }
  }

  override def toString =
    getClass.getSimpleName + table.filter(_ != null).map(_.get).mkString("(", ", ", ")")
}
