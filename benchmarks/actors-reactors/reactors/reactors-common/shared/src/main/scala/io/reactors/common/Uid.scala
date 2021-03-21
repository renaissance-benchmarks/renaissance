package io.reactors.common



import java.util.UUID
import java.util.concurrent.atomic.AtomicLong



object Uid {
  private val countId = new AtomicLong

  def string(timestamp: Long): String =
    UUID.randomUUID().toString + ":" + long() + ":" + timestamp

  def string(): String = string(System.currentTimeMillis())

  def long(): Long = countId.getAndIncrement()
}
