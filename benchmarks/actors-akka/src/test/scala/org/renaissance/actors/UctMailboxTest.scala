package org.renaissance.actors

import akka.actor.ActorRef
import akka.dispatch.Envelope
import org.scalatest.funsuite.AnyFunSuite

final class UctMailboxTest extends AnyFunSuite {

  test("the benchmark mailbox delivers the urgent update before requests queued earlier") {
    val system = new AkkaSystemFactory(AkkaUct.MailboxType).newActorSystem("UctMailboxTest")
    try {
      val queue = system.mailboxes
        .lookup("akka.actor.default-mailbox")
        .create(None, Some(system))

      val requests = Iterator
        .iterate(MeasurementId.First)(_.next)
        .take(3)
        .map(MeasureTemperatureMessage(_))
        .toList

      val update = UrgentUpdateTemperatureMessage(1.0)

      (requests :+ update).foreach { message =>
        queue.enqueue(system.deadLetters, Envelope(message, ActorRef.noSender, system))
      }

      val delivered = Iterator
        .continually(queue.dequeue())
        .takeWhile(_ != null)
        .map(_.message)
        .toList

      assert(delivered == update +: requests)
    } finally system.terminate()
  }

}
