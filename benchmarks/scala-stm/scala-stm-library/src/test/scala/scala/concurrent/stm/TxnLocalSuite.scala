/* scala-stm - (c) 2009-2012, Stanford University, PPL */

package scala.concurrent.stm

import org.scalatest.FunSuite


class TxnLocalSuite extends FunSuite {
  test("default initial value") {
    val tl = TxnLocal[String]()
    atomic { implicit txn =>
      assert(tl() === null)
      tl() = "hello"
    }
    atomic { implicit txn =>
      assert(tl() === null)
    }
    atomic { implicit txn =>
      tl() = "transient"
    }
    atomic { implicit txn =>
      assert(tl() === null)
      tl() = "world"
    }
  }

  test("initialize with init") {
    val tl = TxnLocal("hello")
    for (i <- 0 until 100) {
      atomic { implicit txn =>
        assert(tl() === "hello")
        tl() = "goodbye"
      }
    }
  }

  test("initialize with initialValue") {
    val tl = TxnLocal[Int](
      initialValue = { txn => txn.rootLevel.## }
    )
    atomic { implicit txn =>
      assert(tl() === txn.rootLevel.##)
    }
    atomic { implicit txn =>
      assert(tl() === txn.rootLevel.##)
    }
  }

  test("initialValue overrides init") {
    val x = Ref("abc")
    val tl = TxnLocal("hello", initialValue = { implicit txn => x() })
    for (i <- 0 until 100) {
      atomic { implicit txn =>
        assert(tl() === "abc")
        tl() = "goodbye"
      }
    }
  }

  test("use in afterCompletion handler") {
    val tl = TxnLocal("default")
    atomic { implicit txn =>
      Txn.afterCompletion { status =>
        atomic { implicit txn =>
          assert(tl() === "default")
        }
      }
      tl() = "set once"
      Txn.afterCompletion { status =>
        atomic { implicit txn =>
          assert(tl() === "default")
        }
      }
    }
  }

  test("partial rollback restores previous value") {
    val tl = TxnLocal("default")
    atomic { implicit txn =>
      tl() = "outer"
      intercept[RuntimeException] {
        atomic { implicit txn =>
          assert(tl.swap("inner") === "outer")
          throw new RuntimeException
        }
      }
      assert(tl() === "outer")
    }
  }

  test("partial rollback triggers new initialization") {
    val x = Ref(0)
    val tl = TxnLocal( { x.single() } )
    atomic { implicit txn =>
      x() = 1
      assert(!tl.isInitialized)
      intercept[RuntimeException] {
        atomic { implicit txn =>
          assert(!tl.isInitialized)
          x() = 2
          assert(tl() === 2)
          assert(tl.isInitialized)
          throw new RuntimeException
        }
      }
      assert(!tl.isInitialized)
      assert(tl() === 1)
      assert(tl.isInitialized)
    }
  }

  test("all RefLike operations") {
    val tl = TxnLocal(init = 10)
    atomic { implicit txn =>
      assert(tl.get === 10)
      assert(tl() === 10)
      assert(tl.getWith( _ + 5 ) === 15)
      assert(tl.relaxedGet( _ == _ ) === 10)
      tl.set(15)
      assert(tl() === 15)
      tl() = 20
      assert(tl() === 20)
      assert(tl.trySet(25))
      assert(tl() === 25)
      assert(tl.swap(30) === 25)
      tl.transform( _ + 7 )
      assert(tl() === 37)
      assert(tl.transformIfDefined {
        case x if x > 20 => x + 1
      })
      assert(tl() === 38)
      assert(!tl.transformIfDefined {
        case x if x < 20 => x + 1
      })
    }
  }

  test("first init in whilePreparing handler") {
    val tl = TxnLocal(10)
    atomic { implicit txn =>
      Txn.whilePreparing { implicit txn =>
        assert(tl() == 10)
        tl() = 20
      }
      Txn.whilePreparing { implicit txn =>
        assert(tl() == 20)
      }
    }
  }

  test("first initialValue in beforeCommit handler") {
    val tl = TxnLocal(initialValue = { _ => 10 })
    atomic { implicit txn =>
      Txn.beforeCommit { implicit txn =>
        assert(tl() == 10)
        tl() = 20
      }
      Txn.beforeCommit { implicit txn =>
        assert(tl() == 20)
      }
    }
  }

  test("first initialValue in whilePreparing handler") {
    val tl = TxnLocal(initialValue = { _ => 10 })
    val x = Ref("abc")
    intercept[IllegalStateException] {
      atomic { implicit txn =>
        x() = "def"
        Txn.whilePreparing { implicit txn =>
          assert(tl() == 10)
          tl() = 20
        }
      }
    }
    assert(x.single() === "abc")
  }

  test("first initialValue in whileCommitting handler") {
    val tl = TxnLocal(initialValue = { _ => 10 })
    var failure: Throwable = null
    val handler = { (s: Txn.Status, x: Throwable) => failure = x }
    val x = Ref("abc")
    atomic.withPostDecisionFailureHandler(handler) { implicit txn =>
      x() = "def"
      Txn.whileCommitting { implicit txn =>
        assert(tl() == 10)
        tl() = 20
      }
    }
    assert(x.single() === "def")
    assert(failure != null && failure.isInstanceOf[IllegalStateException])
  }

  test("auto-register beforeCommit") {
    val x = Ref(0)
    lazy val tl: TxnLocal[Int] = TxnLocal(10, beforeCommit = { implicit txn =>
      assert(Txn.status === Txn.Active)
      x() = tl()
    })
    atomic { implicit txn =>
      tl() = 20
    }
    assert(x.single() === 20)
  }

  test("auto-register whilePreparing") {
    var result: Int = 0
    lazy val tl: TxnLocal[Int] = TxnLocal(10, whilePreparing = { implicit txn =>
      assert(Txn.status === Txn.Preparing)
      assert(result === 0)
      tl += 10
      result = tl()
    })
    atomic { implicit txn =>
      tl() = 20
    }
    assert(result === 30)
  }

  test("auto-register whileCommitting") {
    var result: Int = 0
    lazy val tl: TxnLocal[Int] = TxnLocal(10, whileCommitting = { implicit txn =>
      assert(Txn.status === Txn.Committing)
      assert(result === 0)
      tl += 10
      result = tl()
    })
    atomic { implicit txn =>
      tl() = 20
    }
    assert(result === 30)
  }

  test("auto-register afterCommit") {
    var result: Int = 0
    val tl = TxnLocal(10, afterCommit = { (v: Int) => result = v })
    atomic { implicit txn =>
      tl() = 20
    }
    assert(result === 20)
  }

  test("auto-register afterRollback") {
    var result: Txn.Status = null
    val tl = TxnLocal(10, afterRollback = { result = _ })
    intercept[ArrayIndexOutOfBoundsException] {
      atomic { implicit txn =>
        tl() = 20
        throw new ArrayIndexOutOfBoundsException(-1)
      }
    }
    assert(result != null && result.isInstanceOf[Txn.RolledBack])
  }

  test("auto-register afterCompletion - commit") {
    var result: Txn.Status = null
    val tl = TxnLocal(10, afterCompletion = { result = _ })
    atomic { implicit txn =>
      tl() = 20
    }
    assert(result === Txn.Committed)
  }

  test("auto-register afterCompletion - rollback") {
    var result: Txn.Status = null
    val tl = TxnLocal(10, afterCompletion = { result = _ })
    intercept[ArrayIndexOutOfBoundsException] {
      atomic { implicit txn =>
        tl() = 20
        throw new ArrayIndexOutOfBoundsException(-1)
      }
    }
    assert(result != null && result.isInstanceOf[Txn.RolledBack])
  }

  test("auto-register everything") {
    var ran = Set.empty[String]
    val tl = TxnLocal(
      init = "init",
      initialValue = { implicit txn => ran += "initialValue" ; "initialValue" },
      beforeCommit = { implicit txn => assert(txn.status === Txn.Active) ; ran += "beforeCommit" },
      whilePreparing = { implicit txn => assert(txn.status === Txn.Preparing) ; ran += "whilePreparing" },
      whileCommitting = { implicit txn => assert(txn.status === Txn.Committing) ; ran += "whileCommitting" },
      afterCommit = { (v: String) => assert(v === "initialValue") ; ran += "afterCommit" },
      afterRollback = { status => assert(false) },
      afterCompletion = { status => assert(status === Txn.Committed) ; ran += "afterCompletion" }
    )
    atomic { implicit txn =>
      assert(tl() === "initialValue")
    }
    assert(ran === Set("initialValue", "beforeCommit", "whilePreparing", "whileCommitting", "afterCommit", "afterCompletion"))
  }

  test("isolation") {
    val barrier = new java.util.concurrent.CyclicBarrier(2)
    val tl = TxnLocal("init")
    var failure: Throwable = null
    new Thread {
      override def run() {
        try {
          atomic { implicit txn =>
            barrier.await
            assert(tl() === "init")
            barrier.await
            tl() = "thread"
            barrier.await
            assert(tl() === "thread")
            barrier.await
          }
        } catch {
          case x: Throwable => failure = x
        }
        barrier.await
      }
    }.start()

    atomic { implicit txn =>
      barrier.await
      assert(tl() === "init")
      barrier.await
      tl() = "main"
      barrier.await
      assert(tl() === "main")
      barrier.await
    }
    barrier.await

    if (failure != null)
      throw failure
  }
}
