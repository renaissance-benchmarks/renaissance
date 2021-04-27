package io.reactors



import org.scalatest._



class ScalaJsPlatformTest extends FunSuite {
  test("configuration parser") {
    def test(content: String)(b: Configuration => Unit) {
      val config = Platform.configurationFactory.parse(content)
      b(config)
    }

    test("""
      string = "foo"
    """) { c =>
      assert(c.string("string") == "foo")
    }

    test("""
      string = "foobar"

      int = 17

      double = 0.15
    """) { c =>
      assert(c.string("string") == "foobar")
      assert(c.int("int") == 17)
      assert(c.double("double") == 0.15)
    }

    test("""
      pickler = "io.reactors.pickle.JavaSerialization"
      remote = {
        udp = {
          schema = "udp"
          transport = "io.reactors.remote.Udp"
          host = "localhost"
          port = 17771
        }
        tcp = {
          schema = "reactor.tcp"
          transport = "io.reactors.remote.Tcp"
          host = "localhost"
          port = 17775
        }
      }
      scheduler = {
        spindown = {
          initial = 10
          min = 10
          max = 1600
          cooldown-rate = 8
          mutation-rate = 0.15
          test-threshold = 32
          test-iterations = 3
        }
        default = {
          budget = 50
          unschedule-count = 50
        }
      }
    """) { c =>
      assert(c.string("pickler") == "io.reactors.pickle.JavaSerialization")
      assert(c.string("remote.udp.schema") == "udp")
      assert(c.int("remote.udp.port") == 17771)
      assert(c.int("scheduler.spindown.initial") == 10)
      assert(c.double("scheduler.spindown.mutation-rate") == 0.15)
      assert(c.children("remote.udp") == Seq())
      val remotes = c.children("remote")
      assert(remotes(0).string("schema") == "udp")
      assert(remotes(0).string("transport") == "io.reactors.remote.Udp")
      assert(remotes(0).string("host") == "localhost")
      assert(remotes(0).int("port") == 17771)
      assert(remotes(1).string("schema") == "reactor.tcp")
      assert(remotes(1).string("transport") == "io.reactors.remote.Tcp")
      assert(remotes(1).string("host") == "localhost")
      assert(remotes(1).int("port") == 17775)
    }
  }

  test("configuration parser fallback") {
    val c1 = Platform.configurationFactory.parse("remote = { a = 11 }")
    val c2 = Platform.configurationFactory.parse("remote = { a = 7 c = 3 }")
    val config = c1.withFallback(c2)
    assert(config.int("remote.a") == 11)
    assert(config.int("remote.c") == 3)
  }
}
