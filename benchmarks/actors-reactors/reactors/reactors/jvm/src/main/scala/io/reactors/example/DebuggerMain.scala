package io.reactors
package example



import io.reactors.debugger._



object DebuggerMain {
  def main(args: Array[String]) {
    val config = ReactorSystem.customConfig("""
      debug-level = 1
      debug-api = {
        name = "io.reactors.debugger.WebDebugger"
      }
    """)
    val bundle = ReactorSystem.Bundle.default(JvmScheduler.default, config)
    val system = new ReactorSystem("web-debugger", bundle)
    system.names.resolve
  }
}
