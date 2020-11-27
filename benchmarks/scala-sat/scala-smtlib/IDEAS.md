# Ideas

## DSL

First we would define the notion of an `Emitter` that can
process commands in some way (printing, executing):

    trait Emitter {
      def emit(cmd: Command): Unit
    }

    trait Interpreter extends Emitter

    
Then most DSL functions would take an implicit emitter:

    def var[A](prefix: String)(implicit emitter: Emitter) = ???

To actually use the DSL, we need to start from a concrete emitter:

    z3Interpreter.execute(implicit z3 => {
      val x = var[Int]("x")
      val y = var[Int]("y")
      assert(x < y)
    })
