/* scala-stm - (c) 2009-2012, Stanford University, PPL */

package scala.concurrent.stm

/** This trait implements methods that can be used to examine the content of
 *  transactional data structures in a debugger with minimal modification to
 *  the behavior of the program.  Normal transactional reads would add to an
 *  atomic block's read set, which could reduce the number of valid program
 *  execution orders.  `dbgStr` and `dbgValue` perform transactional reads,
 *  but then erase them from the enclosing transaction (if any).
 *
 *  You can use these methods from an IDE debugger manually, by watching
 *  `x.dbgStr` or `x.dbgValue` rather than `x`.
 *
 *  If you use Eclipse, you can make this method the default view by going to
 *  ''Window->Preferences->Java[+]->Debug[+]->Detail Formatters'' and
 *  entering the code snippet `dbgStr()` (or `dbgValue()`) for instances of
 *  `scala.concurrent.stm.TxnDebuggable`.
 *
 *  If you use IntelliJ IDEA, go to
 *  ''File->Settings...->Debugger->Data Type Renderers'' and create a new
 *  renderer for `scala.concurrent.stm.TxnDebuggable` that uses
 *  `dbgStr()` for rendering and `dbgValue()` for node expansion.
 *
 *  @author Nathan Bronson
 */
trait TxnDebuggable {

  /** Returns a string representation of the transactional value in this
   *  instance for debugging convenience.  The `Ref` reads (and writes)
   *  performed while constructing the result will be discarded before
   *  returning.  This method works fine outside a transaction.
   *
   *  If this method is called from within a transaction that is already
   *  doomed (status `Txn.Rolledback`), a string describing the reason
   *  for the outer transaction's rollback will be returned.
   */
  def dbgStr: String

  /** Returns some value that is suitable for examination in a debugger,
   *  or returns a `Txn.RollbackCause` if called from inside a doomed atomic
   *  block.
   */
  def dbgValue: Any

  /** Helper function for generating `dbgStr` of a transactional type that
   *  can produce an iterable view.
   */
  private[stm] def mkStringPrefix(typeName: String, values: Iterable[_], unabbrevLen: Int = 1000): String = {
    val buf = new StringBuilder(typeName + "[size=" + values.size + "](")
    val iter = values.iterator
    while (iter.hasNext && buf.length < unabbrevLen - 1) {
      buf.append(iter.next())
      if (iter.hasNext)
        buf.append(", ")
    }
    if (iter.hasNext)
      buf.append("...")
    buf.append(")")
    buf.toString()
  }
}