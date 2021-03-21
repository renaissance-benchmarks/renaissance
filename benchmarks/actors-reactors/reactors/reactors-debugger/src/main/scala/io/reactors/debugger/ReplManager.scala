package io.reactors
package debugger



import io.reactors.common.Uid
import io.reactors.debugger.repl.ScalaRepl
import java.util.TimerTask
import java.util.concurrent.atomic.AtomicLong
import scala.collection._
import scala.concurrent.Future
import scala.concurrent.ExecutionContext.Implicits.global
import scala.tools.nsc.Settings
import scala.tools.nsc.interpreter._



class ReplManager(val system: ReactorSystem) {
  val expirationCheckSeconds =
    system.bundle.config.int("debug-api.repl.expiration-check-period")
  val expirationSeconds =
    system.bundle.config.int("debug-api.repl.expiration")
  val monitor = system.monitor
  val uidCount = new AtomicLong
  val repls = mutable.Map[String, ReplManager.Session]()
  val replFactory = mutable.Map[String, ReactorSystem => Repl]()

  {
    // Start expiration checker.
    system.globalTimer.schedule(new TimerTask {
      def run() = checkExpired()
    }, expirationCheckSeconds * 1000)

    // Add known repls.
    replFactory("Scala") = system => new ScalaRepl(system)
  }

  private def checkExpired() {
    monitor.synchronized {
      val now = System.currentTimeMillis()
      var dead = List[String]()
      for ((id, s) <- repls) {
        if (algebra.time.diff(now, s.lastActivityTime) > expirationSeconds * 1000) {
          s.repl.shutdown()
          dead ::= id
        }
      }
      for (id <- dead) repls.remove(id)
    }
  }

  private def repl(uid: String, tpe: String, create: Boolean): Option[(String, Repl)] =
    monitor.synchronized {
      repls.get(uid) match {
        case Some(s) =>
          s.ping()
          Some((uid, s.repl))
        case None =>
          if (create) {
            replFactory.get(tpe) match {
              case Some(f) =>
                val s = new ReplManager.Session(f(system))
                val nuid = Uid.string()
                repls(nuid) = s
                Some((nuid, s.repl))
              case None =>
                None
            }
          } else {
            None
          }
      }
    }

  def createRepl(tpe: String): Future[(String, Repl)] = {
    repl("", tpe, true) match {
      case Some((nuid, r)) => r.started.map(_ => (nuid, r))
      case None => Future.failed(new Exception("Could not start REPL."))
    }
  }

  def getRepl(uid: String): Future[(String, Repl)] = {
    repl(uid, "", false) match {
      case Some((uid, r)) => r.started.map(_ => (uid, r))
      case None => Future.failed(new Exception("REPL not found."))
    }
  }

  def closeRepl(uid: String): Unit = monitor.synchronized {
    repl(uid, "", false) match {
      case Some((uid, r)) =>
        repls.remove(uid)
        r.shutdown()
      case _ =>
    }
  }

  def pendingOutputs(repluids: List[String]): List[(String, String)] = {
    monitor.synchronized {
      for (ruid <- repluids; s <- repls.get(ruid)) yield (ruid, s.repl.flush())
    }
  }

  def log(x: Any) {
    monitor.synchronized {
      for ((_, s) <- repls) s.repl.log(x)
    }
  }
}


object ReplManager {
  class Session(val repl: Repl) {
    private var rawLastActivityTime = System.currentTimeMillis()

    def lastActivityTime: Long = rawLastActivityTime

    def ping() = rawLastActivityTime = System.currentTimeMillis()
  }
}
