package io.reactors






package concurrent {

  class AnonymousReactor[T](body: Reactor[T] => Unit) extends Reactor[T] {
    body(this)
  }

}


package object concurrent {

}
