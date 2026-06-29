package org.renaissance.actors

import akka.actor.ActorSystem
import com.typesafe.config.{Config, ConfigFactory}
import scala.util.Properties.propOrNone

/**
 * Creates Akka actor systems with a fixed configuration.
 *
 * The configuration is built eagerly at construction time so that any
 * misconfiguration is detected before the first iteration runs.
 */
final class AkkaSystemFactory(mailboxType: String) {

  private val config: Config = {
    val corePoolSize = workerCount("actors.corePoolSize", 4)
    val maxPoolSize = workerCount("actors.maxPoolSize", corePoolSize)

    val customConf = ConfigFactory.parseString(s"""
      akka {
        log-dead-letters-during-shutdown = off
        log-dead-letters = off

        actor {
          creation-timeout = 6000s
          default-dispatcher {
            fork-join-executor {
              parallelism-min = $corePoolSize
              parallelism-max = $maxPoolSize
              parallelism-factor = 1.0
            }
          }
          default-mailbox {
            mailbox-type = $mailboxType
          }
          prio-dispatcher {
            mailbox-type = $mailboxType
          }
          typed {
            timeout = 10000s
          }
        }
      }
    """)

    ConfigFactory.load(customConf)
  }

  def newActorSystem(name: String): ActorSystem = ActorSystem(name, config)

  private def workerCount(propertyName: String, minNumThreads: Int): Int =
    intProp(propertyName)
      .filter(_ > 0)
      .getOrElse {
        val byCores = Runtime.getRuntime.availableProcessors() * 2
        if (byCores > minNumThreads) byCores else minNumThreads
      }

  private def intProp(propName: String): Option[Int] =
    try propOrNone(propName).map(_.toInt)
    catch {
      case _: SecurityException | _: NumberFormatException => None
    }

}
