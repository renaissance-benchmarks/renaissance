package io.reactors.common



import scala.collection._
import Conc._
import org.scalameter.api._



trait ConcUtils extends Bench.OfflineReport {

  override def historian =
    org.scalameter.reporting.RegressionReporter.Historian.Complete()

  def sizes(from: Int, until: Int) = Gen.range("size")(from, until, (until - from) / 4)

  def concs(from: Int, until: Int) = for {
    size <- sizes(from, until)
  } yield {
    var xs: Conc[Int] = Empty
    for (x <- 0 until size) xs <>= new Single(x)
    xs
  }

  def ropes(k: Int, from: Int, until: Int) = for {
    size <- sizes(from, until)
  } yield {
    val xs = new ConcBuffer[Int](k)
    for (x <- 0 until size) xs += x
    xs.extractConc()
  }

  def arraybuffers(from: Int, until: Int) = for {
    size <- sizes(from, until)
  } yield {
    val b = mutable.ArrayBuffer[Int]()
    for (x <- 0 until size) b += x
    b
  }

  def conqueues(k: Int, from: Int, until: Int) = for {
    size <- sizes(from, until)
  } yield {
    val xs = new ConqueueBuffer[Int](k)
    for (x <- 0 until size) xs += x
    xs.extractConqueue()
  }

  def lists(from: Int, until: Int) = for {
    size <- sizes(from, until)
  } yield (0 until size).toList

  def vectors(from: Int, until: Int) = for {
    size <- sizes(from, until)
  } yield (0 until size).toVector

}


class ConcTimeBenches extends ConcUtils {
  val opts = Context(
    exec.minWarmupRuns -> 60,
    exec.maxWarmupRuns -> 120,
    exec.independentSamples -> 3
  )

  performance of "foreach" config(opts) in {
    using(concs(30000, 150000)) curve("ConcList") in { conc =>
      conc.foreach(x => {})
    }

    using(lists(30000, 150000)) curve("List") in { list =>
      list.foreach(x => {})
    }

    using(vectors(300000, 1500000)) curve("Vector") in { vector =>
      vector.foreach(x => {})
    }

    using(ropes(128, 300000, 1500000)) curve("Conc.Buffer(128)") in { rope =>
      rope.foreach(x => {})
    }

    using(ropes(128, 300000, 1500000)) curve("Conqueue.Buffer(128)") in { rope =>
      rope.foreach(x => {})
    }
  }

  performance of "append" config(opts) in {
    using(sizes(30000, 150000)) curve("ConcList") in { sz =>
      var xs: Conc[String] = Empty
      var i = 0
      while (i < sz) {
        xs = xs rappend ""
        i += 1
      }
      xs
    }

    using(sizes(30000, 150000)) curve("Vector") in { sz =>
      var xs: Vector[String] = Vector()
      var i = 0
      while (i < sz) {
        xs = xs :+ ""
        i += 1
      }
      xs
    }

    using(sizes(30000, 150000)) curve("Conqueue") in { sz =>
      var xs = Conqueue.empty[Int]
      var i = 0
      while (i < sz) {
        xs = xs :+ i
        i += 1
      }
      xs
    }

    using(sizes(300000, 1500000)) curve("Conc.Buffer(128)") in { sz =>
      val xs = new ConcBuffer[Int](128)
      var i = 0
      while (i < sz) {
        xs += i
        i += 1
      }
      xs
    }

    using(sizes(300000, 1500000)) curve("ConqueueBuffer(128)") in { sz =>
      val xs = new ConqueueBuffer[Int](128)
      var i = 0
      while (i < sz) {
        xs += i
        i += 1
      }
      xs
    }

    using(sizes(300000, 1500000)) curve("ArrayBuffer") in { sz =>
      val xs = new collection.mutable.ArrayBuffer[String]()
      var i = 0
      while (i < sz) {
        xs += ""
        i += 1
      }
      xs
    }

    using(sizes(300000, 1500000)) curve("VectorBuilder") in { sz =>
      val xs = new collection.immutable.VectorBuilder[String]()
      var i = 0
      while (i < sz) {
        xs += ""
        i += 1
      }
      xs
    }

  }

  performance of "prepend" config(opts) in {
    using(sizes(30000, 150000)) curve("List") in { sz =>
      var xs: List[String] = Nil
      var i = 0
      while (i < sz) {
        xs = "" :: xs
        i += 1
      }
      xs
    }

    using(sizes(30000, 150000)) curve("Vector") in { sz =>
      var xs: Vector[String] = Vector()
      var i = 0
      while (i < sz) {
        xs = "" +: xs
        i += 1
      }
      xs
    }

    using(sizes(30000, 150000)) curve("Conqueue") in { sz =>
      var xs = Conqueue.empty[Int]
      var i = 0
      while (i < sz) {
        xs = i +: xs
        i += 1
      }
      xs
    }

    using(sizes(30000, 150000)) curve("ConqueueBuffer(128)") in { sz =>
      val xs = new ConqueueBuffer[Int](128)
      var i = 0
      while (i < sz) {
        i +=: xs
        i += 1
      }
      xs
    }
  }

  performance of "concat" config(opts) in {
    using(
      concs(300000, 1500000) zip concs(3000, 300000).rename("size" -> "thatSize")
    ) curve("ConcList") in { case (conc, thatConc) =>
      var i = 0
      while (i < 10000) {
        conc <> thatConc
        i += 1
      }
    }

    using(
      ropes(128, 300000, 1500000) zip ropes(128, 3000, 300000).rename(
        "size" -> "thatSize")) curve("Conc.Buffer(128)"
    ) in { case (rope, thatRope) =>
      var i = 0
      while (i < 10000) {
        rope <> thatRope
        i += 1
      }
    }

    using(
      conqueues(128, 300000, 1500000) zip conqueues(128, 3000, 300000).rename(
        "size" -> "thatSize")
    ) curve("Conqueue.Buffer(128)") in { case (conq, thatConq) =>
      var i = 0
      while (i < 10000) {
        conq <> thatConq
        i += 1
      }
    }

    using(
      vectors(300, 1500) zip vectors(30, 150).rename("size" -> "thatSize")
    ) curve("Vector") config(
      exec.minWarmupRuns -> 1,
      exec.maxWarmupRuns -> 1,
      exec.benchRuns -> 2,
      exec.independentSamples -> 1
    ) in { case (vector, thatVector) =>
      var i = 0
      while (i < 10000) {
        vector ++ thatVector
        i += 1
      }
    }
  }

  performance of "apply" config(
    opts ++ Context(
      exec.benchRuns -> 10,
      exec.independentSamples -> 1
    )
  ) in {
    using(concs(3000, 150000)) curve("ConcList") in { conc =>
      var i = 0
      while (i < conc.size) {
        conc(i)
        i += 1
      }
    }

    using(vectors(3000, 150000)) curve("Vector") in { vector =>
      var i = 0
      while (i < vector.size) {
        vector(i)
        i += 1
      }
    }

    using(arraybuffers(3000, 150000)) curve("ArrayBuffer") in { arraybuffer =>
      var i = 0
      while (i < arraybuffer.size) {
        arraybuffer(i)
        i += 1
      }
    }

    using(conqueues(128, 3000, 150000)) curve("Conqueue.Buffer(128)") in { conq =>
      var i = 0
      while (i < conq.size) {
        conq(i)
        i += 1
      }
    }
  }

  performance of "update" config(opts) in {
    using(concs(30000, 150000)) curve("ConcList") in { conc =>
      var i = 0
      while (i < conc.size) {
        conc(i) = 0
        i += 1
      }
    }

    using(vectors(30000, 150000)) curve("Vector") in { vector =>
      var v = vector
      var i = 0
      while (i < vector.size) {
        v.updated(i, 0)
        i += 1
      }
    }

    using(arraybuffers(30000, 150000)) curve("ArrayBuffer") in { arraybuffer =>
      var i = 0
      while (i < arraybuffer.size) {
        arraybuffer(i) = 0
        i += 1
      }
    }
  }

}


class ConcMemoryBenches extends ConcUtils {

  override def measurer = new Executor.Measurer.MemoryFootprint

  val memoryOpts = Context(
    exec.independentSamples -> 3,
    exec.benchRuns -> 3
  )

  performance of "memory" config(memoryOpts) in {
    using(concs(30000, 150000)) curve("ConcList") in { conc =>
      conc
    }

    using(lists(30000, 150000)) curve("List") in { list =>
      list.map(x => "")
    }

    using(vectors(300000, 1500000)) curve("Vector") in { vector =>
      vector.map(x => "")
    }

    using(ropes(128, 300000, 1500000)) curve("Conc.Buffer(128)") in { rope =>
      rope
    }

    using(conqueues(128, 300000, 1500000)) curve("Conqueue.Buffer(128)") in { conq =>
      conq
    }
  }
}


class ConcBenches extends Bench.Group {
  include(new ConcTimeBenches {})
  include(new ConcMemoryBenches {})
}






