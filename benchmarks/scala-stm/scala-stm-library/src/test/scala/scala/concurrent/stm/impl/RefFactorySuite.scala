/* scala-stm - (c) 2009-2010, Stanford University, PPL */

package scala.concurrent.stm
package impl

import org.scalatest.FunSuite
import java.lang.String

class RefFactorySuite extends FunSuite {

  private case class Fact(expected: String) extends skel.StubSTMImpl with RefFactory {

    private def called(w: String) = {
      assert(w === expected)
      null
    }

    override def newRef(v0: Boolean): Ref[Boolean] = called("Boolean")
    override def newRef(v0: Byte): Ref[Byte] = called("Byte")
    override def newRef(v0: Short): Ref[Short] = called("Short")
    override def newRef(v0: Char): Ref[Char] = called("Char")
    override def newRef(v0: Int): Ref[Int] = called("Int")
    override def newRef(v0: Float): Ref[Float] = called("Float")
    override def newRef(v0: Long): Ref[Long] = called("Long")
    override def newRef(v0: Double): Ref[Double] = called("Double")
    override def newRef(v0: Unit): Ref[Unit] = called("Unit")
    override def newRef[T](v0: T)(implicit m: ClassManifest[T]): Ref[T] = called("Any")
  }

  object TestRef extends RefCompanion {
    var factory: RefFactory = null
  }

  test("signature specialization") {
    TestRef.factory = Fact("Boolean")
    TestRef(false)

    TestRef.factory = Fact("Byte")
    TestRef(0 : Byte)

    TestRef.factory = Fact("Short")
    TestRef(0 : Short)

    TestRef.factory = Fact("Char")
    TestRef(0 : Char)

    TestRef.factory = Fact("Int")
    TestRef(0 : Int)

    TestRef.factory = Fact("Float")
    TestRef(0 : Float)

    TestRef.factory = Fact("Long")
    TestRef(0 : Long)

    TestRef.factory = Fact("Double")
    TestRef(0 : Double)

    TestRef.factory = Fact("Unit")
    TestRef(())

    TestRef.factory = Fact("Any")
    TestRef("abc")
    TestRef(null)
    TestRef(0.asInstanceOf[AnyRef])
    val x: Any = 0
    TestRef(x)
  }

  test("missing manifest TestRef.apply") {
    TestRef.factory = Fact("Any")

    def go[T](x: T) = TestRef(x)

    go(123)
    go(1.23)
    go(null)
    go("abc")
  }

  test("dynamic specialization") {
    def go[T : ClassManifest](v0: T, which: String) {
      TestRef.factory = Fact(which)
      TestRef(v0)
    }
    
    go(false, "Boolean")
    go(0 : Byte, "Byte") 
    go(0 : Short, "Short") 
    go(0 : Char, "Char")
    go(0 : Int, "Int")
    go(0 : Float, "Float") 
    go(0 : Long, "Long") 
    go(0 : Double, "Double") 
    go((), "Unit")
    go("abc", "Any")
    go(null, "Any")
    go(0.asInstanceOf[AnyRef], "Any")
    val x: Any = 0
    go(x, "Any")
  }

  test("default value specialization") {
    def go[T : ClassManifest](default: T, which: String) {
      TestRef.factory = Fact(which)
      TestRef.make[T]()
      //assert(x.single() == default)
    }

    go(false, "Boolean")
    go(0 : Byte, "Byte")
    go(0 : Short, "Short")
    go(0 : Char, "Char")
    go(0 : Int, "Int")
    go(0 : Float, "Float")
    go(0 : Long, "Long")
    go(0 : Double, "Double")
    go((), "Unit")
    go[String](null, "Any")
    go[AnyRef](null, "Any")
    go[Null](null, "Any")
    go[Any](null, "Any")
  }

  test("missing manifest TestRef.make") {
    TestRef.factory = Fact("Any")

    def go[T]() = TestRef.make[T]()

    go[Boolean]()
    go[Byte]()
    go[Short]()
    go[Char]()
    go[Int]()
    go[Float]()
    go[Long]()
    go[Double]()
    go[Unit]()
    go[String]()
    go[AnyRef]()
    go[Null]()
    go[Any]()
  }

}
