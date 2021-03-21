package io.reactors
package debugger



import io.reactors.common.UnrolledRing
import io.reactors.concurrent.Frame
import io.reactors.json._
import scala.collection._
import scalajson.ast._



class DeltaDebugger(val system: ReactorSystem, val sessionuid: String) {
  private val monitor = system.monitor
  private val oldstate = new DeltaDebugger.State()
  private var oldtimestamp = 0L
  private var curstate: DeltaDebugger.State = null
  private var curtimestamp = 0L
  private val deltas = new UnrolledRing[DeltaDebugger.Delta]
  private var pendingSends = mutable.Map[(Long, Long), Long]()
  private val windowSize =
    system.bundle.config.int("debug-api.delta-debugger.window-size")

  {
    monitor.synchronized {
      for ((id, name, _) <- system.frames.values) {
        oldstate.reactors(id) = name
      }
    }
    curstate = oldstate.copy()
  }

  private def commitPendingSends() = monitor.synchronized {
    if (pendingSends.nonEmpty) {
      val delta = DeltaDebugger.EventsSent(pendingSends.toList.toMap)
      deltas.enqueue(delta)
      delta.apply(curstate)
      curtimestamp += 1
      pendingSends.clear()
    }
  }

  private def enqueue(delta: DeltaDebugger.Delta) {
    monitor.synchronized {
      commitPendingSends()
      deltas.enqueue(delta)
      delta.apply(curstate)
      curtimestamp += 1
      while (deltas.size > windowSize) {
        val oldestdelta = deltas.dequeue()
        oldestdelta.apply(oldstate)
        oldtimestamp += 1
      }
    }
  }

  def state(suid: String, reqts: Long): JObject = {
    monitor.synchronized {
      commitPendingSends()
      if (suid != sessionuid || reqts < oldtimestamp) {
        DeltaDebugger.toJson(sessionuid, curtimestamp, Some(curstate.copy()), None)
      } else {
        val newdeltas = mutable.Buffer[DeltaDebugger.Delta]()
        var ts = oldtimestamp
        for (delta <- deltas) {
          ts += 1
          if (ts > reqts) newdeltas += delta
        }
        DeltaDebugger.toJson(sessionuid, curtimestamp, None, Some(newdeltas))
      }
    }
  }

  def isEnabled = true

  def eventSent[@spec(Int, Long, Double) T](c: Channel[T], x: T) {
    monitor.synchronized {
      val f = Reactor.currentFrame
      val cuid = c match {
        case c: Channel.Local[_] => Some(c.frame.uid)
        case _ => None
      }
      if (f != null && cuid.nonEmpty) {
        val senderUid = f.uid
        val targetUid = cuid.get
        val pair = (senderUid, targetUid)
        val count = pendingSends.getOrElse(pair, 0L)
        pendingSends(pair) = count + 1
      }
    }
  }

  def eventDelivered[@spec(Int, Long, Double) T](c: Channel[T], x: T) {}

  def reactorStarted(f: Frame) = enqueue(DeltaDebugger.ReactorStarted(f))

  def reactorScheduled(r: Reactor[_]) {}

  def reactorPreempted(r: Reactor[_]) {}

  def reactorDied(r: Reactor[_]) = enqueue(DeltaDebugger.ReactorDied(r))

  def reactorTerminated(r: Reactor[_]) = enqueue(DeltaDebugger.ReactorTerminated(r))

  def connectorOpened[T](c: Connector[T]) = enqueue(DeltaDebugger.ConnectorOpened(c))

  def connectorSealed[T](c: Connector[T]) = enqueue(DeltaDebugger.ConnectorSealed(c))

  def log(x: Any) {}
}


object DeltaDebugger {
  def toJson(
    suid: String, ts: Long, state: Option[State], deltas: Option[Seq[Delta]]
  ): JObject = json"""{
    "ts": $ts,
    "suid": $suid,
    "state": ${state.map(_.toJson)},
    "deltas": ${deltas.map(_.map(_.toJson))}
  }""".asJObject

  private def sendTriplets(sends: Map[(Long, Long), Long]): Iterable[List[Long]] =
    sends.map {
      case (pair, count) => List(pair._1, pair._2, count)
    }

  class State() {
    val reactors = mutable.Map[Long, String]()
    val sends = mutable.Map[(Long, Long), Long]()
    def copy(): State = {
      val s = new State()
      for ((id, name) <- reactors) s.reactors(id) = name
      for ((pair, count) <- sends) s.sends(pair) = count
      s
    }
    def toJson: JValue = {
      val rs = for ((uid, r) <- reactors) yield json"""{
        "uid": $uid,
        "name": $r
      }"""
      json"""{
        "reactors": $rs,
        "sends": ${sendTriplets(sends)}
      }"""
    }
  }

  abstract class Delta {
    def toJson: JValue
    def apply(s: State): Unit
  }

  case class ReactorStarted(f: Frame) extends Delta {
    def toJson = json"""["start", ${f.uid}, ${f.name}]"""
    def apply(s: State) {
      s.reactors(f.uid) = f.name
    }
  }

  case class ReactorDied(r: Reactor[_]) extends Delta {
    def toJson = json"""["die", ${r.uid}]"""
    def apply(s: State) {
    }
  }

  case class ReactorTerminated(r: Reactor[_]) extends Delta {
    def toJson = json"""["term", ${r.uid}]"""
    def apply(s: State) {
      s.reactors.remove(r.uid)
    }
  }

  case class ConnectorOpened(c: Connector[_]) extends Delta {
    def toJson = json"""["open", ${c.uid}]"""
    def apply(s: State) {
    }
  }

  case class ConnectorSealed(c: Connector[_]) extends Delta {
    def toJson = json"""["seal", ${c.uid}]"""
    def apply(s: State) {
    }
  }

  case class EventsSent(sends: Map[(Long, Long), Long]) extends Delta {
    def toJson = {
      val sendsArray = sendTriplets(sends)
      json"""["sent", $sendsArray]"""
    }
    def apply(s: State) {
      for ((pair, count) <- sends) {
        val current = s.sends.getOrElse(pair, 0L)
        s.sends(pair) = current + count
      }
    }
  }
}
