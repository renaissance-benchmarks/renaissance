package org.renaissance.kotlin.ktor.common

import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertNotEquals

class DirectMessageChatTest {
  @Test
  fun hashForChatIsOrderIndependent() {
    assertEquals(
      DirectMessageChat.hashForChat("alice", "bob"),
      DirectMessageChat.hashForChat("bob", "alice")
    )
  }

  @Test
  fun hashForChatDiffersForDifferentPairs() {
    assertNotEquals(
      DirectMessageChat.hashForChat("alice", "bob"),
      DirectMessageChat.hashForChat("alice", "carol")
    )
  }

  @Test
  fun hashForChatIsWellDefinedForMessagingSelf() {
    assertEquals(
      DirectMessageChat.hashForChat("alice", "alice"),
      DirectMessageChat.hashForChat("alice", "alice")
    )
  }
}
