/* scala-stm - (c) 2009-2011, Stanford University, PPL */

package scala.concurrent.stm

import org.scalatest.FunSuite
import skel.SimpleRandom

class ContentionSuite extends FunSuite {
  // probability that two txns of size M touch the same element out of N
  // (M substantially less than N) is about 1 - (1 - M/N)^M

  var count = 0
  for (numRefs <- List(1000, 100000)) {
    for (readPct <- List(80)) {
      for (numThreads <- List(4, 32)) {
        for (txnSize <- List(8, 64, 16)) {
          for (nested <- List(false, true)) {
            val opsPerThread = 20000000 / numThreads
            val numReads = opsPerThread * readPct / 100
            val numWrites = opsPerThread - numReads
            val name = "%d refs, %d %% read, %d threads, %d ops/txn, nested=%s".format(
                numRefs, readPct, numThreads, txnSize, nested)
            if (count < 4) {
              test("small " + name) {
                runTest(numRefs, numReads / 10, numWrites / 10, numThreads, txnSize, nested, "small " + name)
              }
            }
            test(name, Slow) {
              runTest(numRefs, numReads, numWrites, numThreads, txnSize, nested, name)
            }
            count += 1
          }
        }
      }
    }
  }

  /** Runs one thread per element of `txnSizes`. */
  def runTest(numRefs: Int, numReads: Int, numWrites: Int, numThreads: Int, txnSize: Int, nested: Boolean, name: String) {
    val values = (0 until 37) map { i => "foo" + i }

    val refs = Array.tabulate(numRefs) { _ => Ref(values(0)) }

    val threads = for (t <- 0 until numThreads) yield new Thread {
      override def run {
        var rand = new SimpleRandom(hashCode)
        var i = 0
        while (i < numReads + numWrites) {
          val body: (InTxn => SimpleRandom) = { implicit txn =>
            val r = rand.clone
            var j = 0
            while (j < txnSize) {
              val key = r.nextInt(numRefs)
              val pct = r.nextInt(numReads + numWrites)
              if (pct < numReads)
                refs(key)()
              else
                refs(key)() = values(r.nextInt(values.length))
              j += 1
            }
            if (r.nextInt(100) < 10) {
              Txn.whilePreparing { _ => }
              Txn.whileCommitting { _ => }
              Txn.setExternalDecider(new Txn.ExternalDecider { def shouldCommit(implicit txn: InTxnEnd) = true })
            }
            r
          }
          if (!nested)
            rand = atomic(body)
          else {
            rand = atomic { implicit txn =>
              atomic(body) orAtomic { implicit txn => throw new Error("execution should not reach here") }
            }
          }
          i += txnSize
        }
      }
    }

    val begin = System.currentTimeMillis
    for (t <- threads) t.start()
    for (t <- threads) t.join()
    val elapsed = System.currentTimeMillis - begin

    val nanosPerOp = elapsed * 1000000L / ((numReads + numWrites) * 1L * numThreads)
    printf("ContentionSuite: %s, %d nanos/op aggregate throughput\n", name, nanosPerOp)
  }

  test("starving elder small") { runElderTest(8, 10) }
  test("starving elder large", Slow) { runElderTest(32, 100) }

  def runElderTest(writerCount: Int, numElders: Int) {
    val writersStarted = Ref(0) // elder can't run until all writers are started
    val refs = Array.tabulate(1000) { i => Ref(i.toString) }
    val eldersLeft = Ref(numElders) // writers end after all elders are done

    val writers = for(i <- 0 until writerCount) yield new Thread("writer " + i) {
      override def run {
        writersStarted.single += 1

        val rand = new skel.SimpleRandom
        while (true) {
          val a = refs(rand.nextInt(refs.length))
          val b = refs(rand.nextInt(refs.length))
          val pct = rand.nextInt(100)
          if (pct < 70) {
            // swap in a txn
            atomic { implicit txn =>
              if (eldersLeft() == 0)
                return

              a() = b.swap(a())
            }
          } else {
            if (eldersLeft.single() == 0)
              return

            // swap using DCAS or DCASI
            var done = false
            while (!done) {
              val a0 = a.single()
              val b0 = b.single()
              if (pct < 85)
                done = atomic.compareAndSet(a, a0, b0, b, b0, a0)
              else
                done = atomic.compareAndSetIdentity(a, a0, b0, b, b0, a0)
            }
          }
        }
      }
    }

    for (w <- writers) w.start()

    while (eldersLeft.single() > 0) {
      var tries = 0
      val sum = atomic { implicit txn =>
        tries += 1
        if (writersStarted() < writerCount)
          retry
        refs.foldLeft(0) { _ + _.get.toInt }
      }
      val n = refs.length
      assert(sum === n * (n - 1) / 2)
      eldersLeft.single -= 1
      println("elder ran " + tries + " times")
    }

    for (w <- writers) w.join()
  }

  test("colliding trySet") {
    val x = Ref(0)
    val total = Ref(0)
    val threads = for (t <- 0 until 10) yield new Thread {
      override def run {
        var failures = 0
        for (i <- 0 until 1000000) {
          if (!x.single.trySet(t))
            failures += 1
        }
        total.single += failures
      }
    }
    for (t <- threads) t.start
    for (t <- threads) t.join
    assert(total.single() > 0)
    println(total.single() + " rejected trySet-s")
  }
}