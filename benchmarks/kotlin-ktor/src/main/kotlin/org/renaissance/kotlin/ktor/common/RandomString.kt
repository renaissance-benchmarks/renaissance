package org.renaissance.kotlin.ktor.common

import kotlin.random.Random

private val allowedChars = ('A'..'Z') + ('a'..'z') + ('0'..'9')
internal fun Random.getRandomString(length: Int) : String {
  return (1..length)
    .map { allowedChars.random(this) }
    .joinToString("")
}

internal fun Random.getRandomDigits(base: Int, length: Int): String {
  return (1..length)
    .map { Character.forDigit(nextInt(base), base) }
    .joinToString("")
}
