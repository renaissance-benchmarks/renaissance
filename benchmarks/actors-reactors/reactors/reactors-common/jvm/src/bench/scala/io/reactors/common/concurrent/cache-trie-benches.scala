package io.reactors.common.concurrent



import java.util.concurrent.ConcurrentHashMap
import java.util.concurrent.ConcurrentSkipListMap
import org.scalameter.api._
import org.scalameter.execution.LocalExecutor
import org.scalameter.japi.JBench
import org.scalatest.FunSuite
import scala.collection.concurrent.TrieMap
import scala.util.Random



class CacheTrieFootprintBenches extends JBench.OfflineReport {
  override def measurer = new Executor.Measurer.MemoryFootprint

  override def defaultConfig = Context(
    exec.minWarmupRuns -> 1,
    exec.maxWarmupRuns -> 1,
    exec.benchRuns -> 4,
    exec.independentSamples -> 1,
    verbose -> true
  )

  val numElems = 2000000

  val sizes = Gen.range("size")(100000, numElems, 200000)

  case class Wrapper(value: Int) extends Comparable[Wrapper] {
    def compareTo(that: Wrapper): Int = that.value - this.value
  }

  val elems = (0 until numElems).map(i => Wrapper(i)).toArray

  @gen("sizes")
  @benchmark("cache-trie.size")
  @curve("chm")
  def chmSize(size: Int) = {
   val chm = new ConcurrentHashMap[Wrapper, Wrapper]
   var i = 0
   while (i < size) {
     val v = elems(i)
     chm.put(v, v)
     i += 1
   }
   chm
  }

  @gen("sizes")
  @benchmark("cache-trie.size")
  @curve("skiplist")
  def skipListSize(size: Int) = {
   val skiplist = new ConcurrentSkipListMap[Wrapper, Wrapper]
   var i = 0
   while (i < size) {
     val v = elems(i)
     skiplist.put(v, v)
     i += 1
   }
   skiplist
  }

  @gen("sizes")
  @benchmark("cache-trie.size")
  @curve("ctrie")
  def ctrieSize(size: Int) = {
   val trie = new TrieMap[Wrapper, Wrapper]
   var i = 0
   while (i < size) {
     val v = elems(i)
     trie.put(v, v)
     i += 1
   }
   trie
  }

  @gen("sizes")
  @benchmark("cache-trie.size")
  @curve("cachetrie")
  def cachetrieSize(size: Int) = {
    val trie = new CacheTrie[Wrapper, Wrapper]
    var i = 0
    while (i < size) {
      val v = elems(i)
      trie.insert(v, v)
      i += 1
    }
    i = 0
    while (i < size) {
      val v = elems(i)
      trie.lookup(v)
      i += 1
    }
    trie
  }
}


class CacheTrieBenches extends JBench.OfflineReport {
  override def historian =
    org.scalameter.reporting.RegressionReporter.Historian.Complete()

  override def defaultConfig = Context(
    exec.minWarmupRuns -> 40,
    exec.maxWarmupRuns -> 60,
    exec.independentSamples -> 1,
    exec.jvmflags -> List("-server", "-verbose:gc", "-Xmx6092m", "-Xms6092m"),
    verbose -> true
  )

  case class Wrapper(value: Int) extends Comparable[Wrapper] {
    def compareTo(that: Wrapper) = this.value - that.value
  }

  val maxElems = 500000

  @transient
  lazy val elems = Random.shuffle((0 until maxElems).toVector)
    .map(i => Wrapper(i)).toArray

  val sizes = Gen.range("size")(50000, maxElems, 100000)

  val pars = Gen.exponential("pars")(1, 8, 2)

  val parElems = 100000

  val parCachetries = for (p <- pars) yield {
    val trie = new CacheTrie[Wrapper, Wrapper]
    for (i <- 0 until parElems) trie.insert(elems(i), elems(i))
    (p, trie)
  }

  val parChms = for (p <- pars) yield {
    val chm = new ConcurrentHashMap[Wrapper, Wrapper]
    for (i <- 0 until parElems) chm.put(elems(i), elems(i))
    (p, chm)
  }

  val parSkiplists = for (p <- pars) yield {
    val skiplist = new ConcurrentSkipListMap[Wrapper, Wrapper]
    for (i <- 0 until parElems) skiplist.put(elems(i), elems(i))
    (p, skiplist)
  }

  val parCtries = for (p <- pars) yield {
    val ctrie = new TrieMap[Wrapper, Wrapper]
    for (i <- 0 until parElems) ctrie.put(elems(i), elems(i))
    (p, ctrie)
  }

  val chms = for (size <- sizes) yield {
    val chm = new ConcurrentHashMap[Wrapper, Wrapper]
    for (i <- 0 until size) chm.put(elems(i), elems(i))
    (size, chm)
  }

  val skiplists = for (size <- sizes) yield {
    val skiplist = new ConcurrentSkipListMap[Wrapper, Wrapper]
    for (i <- 0 until size) skiplist.put(elems(i), elems(i))
    (size, skiplist)
  }

  val ctries = for (size <- sizes) yield {
    val trie = new TrieMap[Wrapper, Wrapper]
    for (i <- 0 until size) trie.put(elems(i), elems(i))
    (size, trie)
  }

  val cachetries = for (size <- sizes) yield {
    val trie = new CacheTrie[Wrapper, Wrapper]
    for (i <- 0 until size) {
      trie.insert(elems(i), elems(i))
    }
    for (i <- 0 until size) {
      trie.lookup(elems(i))
    }
    for (i <- 0 until size) {
      trie.lookup(elems(i))
    }
    (size, trie)
  }

  @gen("chms")
  @benchmark("cache-trie.apply")
  @curve("CHM")
  def chmLookup(sc: (Int, ConcurrentHashMap[Wrapper, Wrapper])): Int = {
   val (size, chm) = sc
   var i = 0
   var sum = 0
   while (i < size) {
     sum += chm.get(elems(i)).value
     i += 1
   }
   sum
  }

  @gen("skiplists")
  @benchmark("cache-trie.apply")
  @curve("skiplist")
  def skiplistLookup(sc: (Int, ConcurrentSkipListMap[Wrapper, Wrapper])): Int = {
   val (size, skiplist) = sc
   var i = 0
   var sum = 0
   while (i < size) {
     sum += skiplist.get(elems(i)).value
     i += 1
   }
   sum
  }

  // @gen("cachetries")
  // @benchmark("cache-trie.apply")
  // @curve("cachetrie-slow-path")
  // def cachetrieSlowLookup(sc: (Int, CacheTrie[Wrapper, Wrapper])): Int = {
  //  val (size, trie) = sc
  //  var i = 0
  //  var sum = 0
  //  while (i < size) {
  //    sum += trie.slowLookup(elems(i)).value
  //    i += 1
  //  }
  //  sum
  // }

  @gen("ctries")
  @benchmark("cache-trie.apply")
  @curve("ctrie")
  def ctrie(sc: (Int, TrieMap[Wrapper, Wrapper])): Int = {
   val (size, trie) = sc
   var i = 0
   var sum = 0
   while (i < size) {
     sum += trie.lookup(elems(i)).value
     i += 1
   }
   sum
  }

  @gen("cachetries")
  @benchmark("cache-trie.apply")
  @curve("cachetrie")
  def cachetrieLookup(sc: (Int, CacheTrie[Wrapper, Wrapper])): Int = {
    val (size, trie) = sc
    var i = 0
    var sum = 0
    while (i < size) {
      sum += trie.lookup(elems(i)).value
      i += 1
    }
    // println(trie.debugPerLevelDistribution)
    // println(trie.debugCacheStats)
    sum
  }

  @gen("sizes")
  @benchmark("cache-trie.insert")
  @curve("chm")
  def chmInsert(size: Int) = {
    val chm = new ConcurrentHashMap[Wrapper, Wrapper]
    var i = 0
    while (i < size) {
      val v = elems(i)
      chm.put(v, v)
      i += 1
    }
    chm
  }

  @gen("sizes")
  @benchmark("cache-trie.insert")
  @curve("skiplist")
  def skiplistInsert(size: Int) = {
    val skiplist = new ConcurrentSkipListMap[Wrapper, Wrapper]
    var i = 0
    while (i < size) {
      val v = elems(i)
      skiplist.put(v, v)
      i += 1
    }
    skiplist
  }

  @gen("sizes")
  @benchmark("cache-trie.insert")
  @curve("ctrie")
  def ctrieInsert(size: Int) = {
    val trie = new TrieMap[Wrapper, Wrapper]
    var i = 0
    while (i < size) {
      val v = elems(i)
      trie.put(v, v)
      i += 1
    }
    trie
  }

  @gen("sizes")
  @benchmark("cache-trie.insert")
  @curve("cachetrie")
  def cachetrieInsert(size: Int) = {
    val trie = new CacheTrie[Wrapper, Wrapper]
    var i = 0
    while (i < size) {
      val v = elems(i)
      trie.insert(v, v)
      i += 1
    }
    // println(trie.debugCacheStats)
    trie
  }

  @gen("pars")
  @benchmark("cache-trie.par.insert")
  @curve("chm")
  def chmParInsert(p: Int) = {
    val chm = new ConcurrentHashMap[Wrapper, Wrapper]
    val threads = for (k <- 0 until p) yield new Thread {
      override def run(): Unit = {
        var i = 0
        while (i < parElems / p) {
          val v = elems(k * parElems / p + i)
          chm.put(v, v)
          i += 1
        }
      }
    }
    threads.foreach(_.start())
    threads.foreach(_.join())
    chm
  }

  @gen("pars")
  @benchmark("cache-trie.par.insert")
  @curve("ctrie")
  def ctrieParInsert(p: Int) = {
    val ctrie = new TrieMap[Wrapper, Wrapper]
    val threads = for (k <- 0 until p) yield new Thread {
      override def run(): Unit = {
        var i = 0
        while (i < parElems / p) {
          val v = elems(k * parElems / p + i)
          ctrie.put(v, v)
          i += 1
        }
      }
    }
    threads.foreach(_.start())
    threads.foreach(_.join())
    ctrie
  }

  @gen("pars")
  @benchmark("cache-trie.par.insert")
  @curve("skiplist")
  def skiplistParInsert(p: Int) = {
    val skiplist = new ConcurrentSkipListMap[Wrapper, Wrapper]
    val threads = for (k <- 0 until p) yield new Thread {
      override def run(): Unit = {
        var i = 0
        while (i < parElems / p) {
          val v = elems(k * parElems / p + i)
          skiplist.put(v, v)
          i += 1
        }
      }
    }
    threads.foreach(_.start())
    threads.foreach(_.join())
    skiplist
  }

  @gen("pars")
  @benchmark("cache-trie.par.insert")
  @curve("cachetrie")
  def cachetrieParInsert(p: Int) = {
    val trie = new CacheTrie[Wrapper, Wrapper]
    val threads = for (k <- 0 until p) yield new Thread {
      override def run(): Unit = {
        var i = 0
        while (i < parElems / p) {
          val v = elems(k * parElems / p + i)
          trie.insert(v, v)
          i += 1
        }
      }
    }
    threads.foreach(_.start())
    threads.foreach(_.join())
    // println(trie.debugCacheStats)
    trie
  }

  @gen("parChms")
  @benchmark("cache-trie.par.lookup")
  @curve("chm")
  def chmParLookup(t: (Int, ConcurrentHashMap[Wrapper, Wrapper])) = {
    val (p, xs) = t
    val threads = for (k <- 0 until p) yield new Thread {
      override def run(): Unit = {
        var i = 0
        while (i < parElems / p) {
          val v = elems(k * parElems / p + i)
          xs.get(v)
          i += 1
        }
      }
    }
    threads.foreach(_.start())
    threads.foreach(_.join())
    xs
  }

  @gen("parCtries")
  @benchmark("cache-trie.par.lookup")
  @curve("ctrie")
  def ctrieParLookup(t: (Int, TrieMap[Wrapper, Wrapper])) = {
    val (p, xs) = t
    val threads = for (k <- 0 until p) yield new Thread {
      override def run(): Unit = {
        var i = 0
        while (i < parElems / p) {
          val v = elems(k * parElems / p + i)
          xs.lookup(v)
          i += 1
        }
      }
    }
    threads.foreach(_.start())
    threads.foreach(_.join())
    xs
  }

  @gen("parSkiplists")
  @benchmark("cache-trie.par.lookup")
  @curve("skiplist")
  def skiplistParLookup(t: (Int, ConcurrentSkipListMap[Wrapper, Wrapper])) = {
    val (p, xs) = t
    val threads = for (k <- 0 until p) yield new Thread {
      override def run(): Unit = {
        var i = 0
        while (i < parElems / p) {
          val v = elems(k * parElems / p + i)
          xs.get(v)
          i += 1
        }
      }
    }
    threads.foreach(_.start())
    threads.foreach(_.join())
    xs
  }

  @gen("parCachetries")
  @benchmark("cache-trie.par.lookup")
  @curve("cachetrie")
  def cachetrieParLookup(t: (Int, CacheTrie[Wrapper, Wrapper])) = {
    val (p, xs) = t
    val threads = for (k <- 0 until p) yield new Thread {
      override def run(): Unit = {
        var i = 0
        while (i < parElems / p) {
          val v = elems(k * parElems / p + i)
          xs.lookup(v)
          i += 1
        }
      }
    }
    threads.foreach(_.start())
    threads.foreach(_.join())
    // println(xs.debugCacheStats)
    xs
  }
}


class BirthdaySimulations extends FunSuite {
  test("run birthday simulations") {
    birthday(4, 1)
    birthday(16, 1)
    birthday(16, 2)
    birthday(32, 1)
    birthday(32, 2)
    birthday(256, 1)
    birthday(4096, 1)
    birthday(4096, 2)
    birthday(1 << 16, 1)
    birthday(1 << 20, 1)
  }

  def birthday(days: Int, collisions: Int): Unit = {
    var sum = 0L
    val total = 1000
    for (k <- 1 to total) {
      val slots = new Array[Int](days)
      var i = 1
      while (i <= days) {
        val day = Random.nextInt(days)
        if (slots(day) == collisions) {
          sum += i - 1
          i = days + 2
        }
        slots(day) += 1
        i += 1
      }
      if (i == days + 1) {
        sum += i
      }
    }
    println(s"For $days, collisions $collisions, average: ${(1.0 * sum / total)}")
  }

  def debugPerLevelDistribution(sz: Int): Unit = {
    val trie = new CacheTrie[String, String]
    var i = 0
    while (i < sz) {
      trie.insert(i.toString + "/" + sz.toString, i.toString)
      i += 1
    }
    for (i <- 0 until 512) trie.lookup(i.toString)
    println(trie.debugPerLevelDistribution)
  }

  test("per level distribution") {
    debugPerLevelDistribution(1000)
    debugPerLevelDistribution(2000)
    debugPerLevelDistribution(3000)
    debugPerLevelDistribution(5000)
    debugPerLevelDistribution(10000)
    debugPerLevelDistribution(20000)
    debugPerLevelDistribution(30000)
    debugPerLevelDistribution(50000)
    debugPerLevelDistribution(100000)
    debugPerLevelDistribution(200000)
    debugPerLevelDistribution(300000)
    debugPerLevelDistribution(400000)
    debugPerLevelDistribution(500000)
    debugPerLevelDistribution(650000)
    debugPerLevelDistribution(800000)
    debugPerLevelDistribution(1000000)
    debugPerLevelDistribution(1200000)
    debugPerLevelDistribution(1500000)
    debugPerLevelDistribution(1800000)
    debugPerLevelDistribution(2000000)
    debugPerLevelDistribution(2200000)
    debugPerLevelDistribution(2500000)
    debugPerLevelDistribution(3000000)
  }

  def debugLoadFactor(sz: Int): Unit = {
    val trie = new CacheTrie[String, String]
    var i = 0
    while (i < sz) {
      trie.insert(i.toString + "/" + sz.toString, i.toString)
      i += 1
    }
    println(f"$sz%5d ${trie.debugLoadFactor}%s")
  }

  test("load factor") {
    debugLoadFactor(500)
    debugLoadFactor(1000)
    debugLoadFactor(2000)
    debugLoadFactor(3000)
    debugLoadFactor(4000)
    debugLoadFactor(5000)
    debugLoadFactor(6000)
    debugLoadFactor(7000)
    debugLoadFactor(8000)
    debugLoadFactor(9000)
    debugLoadFactor(10000)
    debugLoadFactor(15000)
    debugLoadFactor(20000)
    debugLoadFactor(30000)
    debugLoadFactor(50000)
    debugLoadFactor(70000)
    debugLoadFactor(100000)
    debugLoadFactor(200000)
    debugLoadFactor(500000)
    debugLoadFactor(1000000)
    debugLoadFactor(2000000)
  }
}
