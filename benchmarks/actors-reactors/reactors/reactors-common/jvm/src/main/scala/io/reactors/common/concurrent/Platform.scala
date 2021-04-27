package io.reactors.common.concurrent



import sun.misc.Unsafe



object Platform {
  val unsafe = {
    val unsafeInstanceField = classOf[Unsafe].getDeclaredField("theUnsafe")
    unsafeInstanceField.setAccessible(true)
    unsafeInstanceField.get(null).asInstanceOf[Unsafe]
  }
}
