package io.reactors



import org.rapidoid.http._



package object debugger {
  implicit class handler1(f: Req => Object) extends ReqHandler {
    def execute(x: Req): Object = f(x)
  }
}
