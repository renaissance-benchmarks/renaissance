/* scala-stm - (c) 2009-2016, Stanford University, PPL */

package scala.concurrent.stm

import org.scalatest.FunSuite


class WriteSkewSuite extends FunSuite {
  val IncrCount = 1000000

  test("write skew test 1K") { runTest(1000) }
  test("write skew test 1M", Slow) { runTest(1000000) }

  def runTest(incrCount: Int) {
    // Two threads, each of which increments its own Ref if the other Ref is
    // even.  Neither thread should ever observe that both Refs are odd.
    // MVCC STMs will require the addition of something like Clojure's "ensure"
    // or SQL's "select for update" to avoid the write skew. 
    val refs = Array(Ref(0), Ref(0))
    val threads = new Array[Thread](2)

    @volatile var failure: Throwable = null
    for (id <- 0 to 1) {
      threads(id) = new Thread("write skew #" + id) {
        val self = refs(id)
        val other = refs(1 - id)

        override def run {
          try {
            for (i <- 0 until incrCount) {
              if (null != failure)
                return
              atomic { implicit t =>
                if ((other() % 2) != 0) {
                  if ((self() % 2) != 0)
                    fail("refs=" + refs.map(_.get))
                  retry
                }
                self() = self() + 1
              }
            }
          } catch {
            case x: Throwable => {
              if (null == failure)
                failure = x
            }
          }
        }
      }
    }

    val begin = System.currentTimeMillis
    for (t <- threads) t.start
    for (t <- threads) t.join

    if (null != failure)
      throw failure
    val elapsed = System.currentTimeMillis - begin
    println("writeSkew(" + (2 * incrCount) + "): " + elapsed + " millis total")
  }
}
