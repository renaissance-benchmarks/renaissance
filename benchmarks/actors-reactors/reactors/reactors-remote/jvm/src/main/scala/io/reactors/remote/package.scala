package io.reactors



import io.reactors.remote.macros.Synthesizer



package object remote {
  import scala.language.experimental.macros

  implicit class ChannelOps[T](val ch: Channel[T]) extends AnyVal {
    def !(x: T): Unit = macro Synthesizer.synthesizeSend
  }
}
