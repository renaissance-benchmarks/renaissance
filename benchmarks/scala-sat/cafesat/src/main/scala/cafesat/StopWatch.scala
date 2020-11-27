package cafesat

import scala.collection.mutable.HashMap

/*
 * would be cool to have a notion of nested stopwatch, so that the percent
 * could make more sense
 */

object StopWatch {

  private val stopWatches: HashMap[String, StopWatch] = new HashMap

  def apply(tag: String): StopWatch = stopWatches.get(tag) match {
    case Some(sw) => sw
    case None => {
      val sw = new StopWatch(tag)
      stopWatches(tag) = sw
      sw
    }
  }

  //need to handle "nested" timer
  def percents: Map[String, Double] = {
    val total: Double = stopWatches.foldLeft(0d)((a, p) => a + p._2.seconds)
    stopWatches.map(p => (p._1, p._2.seconds/total*100)).toMap
  }

}

class StopWatch private (tag: String) {

  private var elapsed: Long = 0

  def time[A](code: => A): A = {
    val timeBegin = System.nanoTime
    val res: A = code
    val timeElapsed = System.nanoTime - timeBegin
    elapsed += timeElapsed
    res
  }

  def seconds: Double = elapsed/1e9
  def nano: Long = elapsed

  def reset() : Unit = {
    elapsed = 0
  }

}
