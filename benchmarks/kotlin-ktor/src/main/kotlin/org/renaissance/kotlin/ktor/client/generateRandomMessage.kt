package org.renaissance.kotlin.ktor.client

import kotlin.random.Random

private val allowedChars = ('A'..'Z') + ('a'..'z') + ('0'..'9')
internal fun Random.getRandomString(length: Int) : String {
  return (1..length)
    .map { allowedChars.random(this) }
    .joinToString("")
}