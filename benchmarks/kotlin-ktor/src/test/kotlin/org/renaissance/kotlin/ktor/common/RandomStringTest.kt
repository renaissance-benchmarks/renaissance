package org.renaissance.kotlin.ktor.common

import kotlin.random.Random
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertTrue

class RandomStringTest {
  @Test
  fun getRandomStringHasRequestedLength() {
    val result = Random(1).getRandomString(37)
    assertEquals(37, result.length)
  }

  @Test
  fun getRandomStringIsEmptyForZeroLength() {
    assertEquals("", Random(1).getRandomString(0))
  }

  @Test
  fun getRandomStringUsesOnlyAlphanumericChars() {
    val result = Random(1).getRandomString(500)
    assertTrue(result.all { it.isLetterOrDigit() && it.code < 128 })
  }

  @Test
  fun getRandomStringIsReproducibleForTheSameSeed() {
    assertEquals(
      Random(42).getRandomString(20),
      Random(42).getRandomString(20)
    )
  }

  //

  @Test
  fun getRandomDigitsHasRequestedLength() {
    val result = Random(1).getRandomDigits(base = 16, length = 16)
    assertEquals(16, result.length)
  }

  @Test
  fun getRandomDigitsBase10UsesOnlyDecimalDigits() {
    val result = Random(1).getRandomDigits(base = 10, length = 500)
    assertTrue(result.all { it in '0'..'9' })
  }

  @Test
  fun getRandomDigitsBase16UsesOnlyLowercaseHexDigits() {
    val result = Random(1).getRandomDigits(base = 16, length = 500)
    assertTrue(result.all { it in '0'..'9' || it in 'a'..'f' })
  }

  @Test
  fun getRandomDigitsIsReproducibleForTheSameSeed() {
    assertEquals(
      Random(42).getRandomDigits(base = 16, length = 16),
      Random(42).getRandomDigits(base = 16, length = 16)
    )
  }
}
