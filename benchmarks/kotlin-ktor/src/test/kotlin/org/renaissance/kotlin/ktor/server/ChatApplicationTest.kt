package org.renaissance.kotlin.ktor.server

import kotlin.test.Test
import kotlin.test.assertEquals

class ChatApplicationTest {
  @Test
  fun setupProducesTheRequestedNumberOfChats() {
    val application = ChatApplication(initialChatCount = 10, initialSeed = 1L)
    application.setup()

    assertEquals(10, application.getAvailableChatIds().size)
  }

  @Test
  fun sameSeedProducesTheSameChatIds() {
    val a = ChatApplication(initialChatCount = 10, initialSeed = 42L)
    val b = ChatApplication(initialChatCount = 10, initialSeed = 42L)
    a.setup()
    b.setup()

    assertEquals(a.getAvailableChatIds().toSet(), b.getAvailableChatIds().toSet())
  }

  @Test
  fun differentSeedsProduceDifferentChatIds() {
    val a = ChatApplication(initialChatCount = 10, initialSeed = 1L)
    val b = ChatApplication(initialChatCount = 10, initialSeed = 2L)
    a.setup()
    b.setup()

    assertEquals(false, a.getAvailableChatIds().toSet() == b.getAvailableChatIds().toSet())
  }

  @Test
  fun chatIdsAreTheSameAcrossRepetitions() {
    val application = ChatApplication(initialChatCount = 10, initialSeed = 1L)

    application.setup()
    val first = application.getAvailableChatIds().toSet()
    application.teardown()

    application.setup()
    val second = application.getAvailableChatIds().toSet()

    assertEquals(first, second)
  }
}
