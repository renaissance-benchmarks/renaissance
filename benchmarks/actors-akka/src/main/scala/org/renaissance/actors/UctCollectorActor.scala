package org.renaissance.actors

import akka.actor.Actor
import akka.actor.DeadLetter
import akka.actor.UnhandledMessage

/**
 * Collects the benchmark messages carried by the [[DeadLetter]] and [[UnhandledMessage]]
 * events it receives, so that the validation can check that no message went astray. On
 * request, it hands over the messages collected so far and starts collecting anew.
 */
private[actors] final class UctCollectorActor extends Actor {

  /** The collected messages, the most recent first. */
  private var messages = List.empty[UctMessage]

  def receive: Receive = {
    case DeadLetter(message: UctMessage, _, _) =>
      messages = message :: messages

    case UnhandledMessage(message: UctMessage, _, _) =>
      messages = message :: messages

    case LocalTakeCollectedMessagesMessage(result) =>
      result.success(messages.reverse)
      messages = Nil
  }

}
