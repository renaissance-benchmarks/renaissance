/* scala-stm - (c) 2009-2014, Stanford University, PPL */

package scala.concurrent.stm

import org.scalatest.FunSuite
import java.util.concurrent.TimeUnit


/** Performs single-threaded tests of `Ref`. */
class IsolatedRefSuite extends FunSuite {

  // Ref factories produces Ref from an initial value

  object PrimitiveIntFactory extends (Int => Ref[Int]) {
    def apply(v0: Int) = Ref(v0)
    override def toString() = "Primitive"
  }

  class KnownGenericFactory[A : ClassManifest] extends (A => Ref[A]) {
    def apply(v0: A) = Ref(v0)
    override def toString() = "KnownGeneric"
  }

  class UnknownGenericFactory[A] extends (A => Ref[A]) {
    def apply(v0: A) = Ref(v0)
    override def toString() = "UnknownGeneric"
  }

  class ArrayElementFactory[A : ClassManifest] extends (A => Ref[A]) {
    def apply(v0: A) = {
      val ref = TArray.ofDim[A](10).refs(5)
      ref.single() = v0
      ref
    }
    override def toString() = "ArrayElement"
  }


  // This implements Ref.View, but requires a surrounding InTxn context and
  // forwards to Ref's methods.
  class DynamicView[A](val ref: Ref[A]) extends Ref.View[A] {
    implicit def txn = Txn.findCurrent.get

    def get: A = ref.get
    def getWith[Z](f: A => Z): Z = ref.getWith(f)
    def relaxedGet(equiv: (A, A) => Boolean): A = ref.relaxedGet(equiv)
    def await(f: A => Boolean) { if (!f(get)) retry }
    def tryAwait(timeout: Long, unit: TimeUnit)(f: A => Boolean): Boolean = f(get) || { retryFor(timeout, unit) ; false }
    def set(v: A) { ref.set(v) }
    def trySet(v: A) = ref.trySet(v)
    def swap(v: A): A = ref.swap(v)
    def compareAndSet(before: A, after: A): Boolean = {
      if (get == before) { set(after) ; true } else false
    }
    def compareAndSetIdentity[B <: A with AnyRef](before: B, after: A): Boolean = {
      if (before eq get.asInstanceOf[AnyRef]) { set(after) ; true } else false
    }
    def transform(f: A => A) { ref.transform(f) }
    def getAndTransform(f: A => A): A = ref.getAndTransform(f)
    def transformAndGet(f: A => A): A = ref.transformAndGet(f)
    override def transformAndExtract[B](f: A => (A,B)): B = ref.transformAndExtract(f)
    def transformIfDefined(pf: PartialFunction[A, A]): Boolean = ref.transformIfDefined(pf)

    override def +=(rhs: A)(implicit num: Numeric[A]) { ref += rhs }
    override def -=(rhs: A)(implicit num: Numeric[A]) { ref -= rhs }
    override def *=(rhs: A)(implicit num: Numeric[A]) { ref *= rhs }
    override def /=(rhs: A)(implicit num: Numeric[A]) { ref /= rhs }

    override def hashCode: Int = ref.hashCode
    override def equals(rhs: Any): Boolean = ref == rhs
  }

  abstract class TestingView[A](innerDepth: Int, val ref: Ref[A]) extends Ref.View[A] {
    private def wrap[Z](block: => Z): Z = nest(innerDepth, block)
    private def nest[Z](d: Int, block: => Z): Z = {
      if (d == 0)
        block
      else
        atomic { implicit txn => nest(d - 1, block) }
    }

    protected def view: Ref.View[A]

    def get: A = wrap { view.get }
    def getWith[Z](f: A => Z): Z = wrap { view.getWith(f) }
    def relaxedGet(equiv: (A, A) => Boolean): A = wrap { view.relaxedGet(equiv) }
    def await(f: (A) => Boolean) { wrap { view.await(f) } }
    def tryAwait(timeout: Long, unit: TimeUnit)(f: (A) => Boolean): Boolean = wrap { view.tryAwait(timeout, unit)(f) }
    def set(v: A) { wrap { view.set(v) } }
    def trySet(v: A) = wrap { view.trySet(v) }
    def swap(v: A): A = wrap { view.swap(v) }
    def compareAndSet(before: A, after: A): Boolean = wrap { view.compareAndSet(before, after) }
    def compareAndSetIdentity[B <: A with AnyRef](before: B, after: A): Boolean = wrap { view.compareAndSetIdentity(before, after) }
    def transform(f: A => A) { wrap { view.transform(f) } }
    def getAndTransform(f: A => A): A = wrap { view.getAndTransform(f) }
    def transformAndGet(f: A => A): A = wrap { view.transformAndGet(f) }
    override def transformAndExtract[B](f: A => (A,B)): B = wrap { view.transformAndExtract(f) }
    def transformIfDefined(pf: PartialFunction[A, A]): Boolean = wrap { view.transformIfDefined(pf) }

    override def +=(rhs: A)(implicit num: Numeric[A]) { wrap { view += rhs } }
    override def -=(rhs: A)(implicit num: Numeric[A]) { wrap { view -= rhs } }
    override def *=(rhs: A)(implicit num: Numeric[A]) { wrap { view *= rhs } }
    override def /=(rhs: A)(implicit num: Numeric[A]) { wrap { view /= rhs } }

    override def hashCode: Int = ref.hashCode
    override def equals(rhs: Any): Boolean = ref == rhs
  }

  trait ViewFactory {
    def apply[A](ref: Ref[A], innerDepth: Int): Ref.View[A]
  }

  object SingleAccess extends ViewFactory {
    def apply[A](ref: Ref[A], innerDepth: Int): Ref.View[A] = new TestingView[A](innerDepth, ref) {
      protected def view = ref.single
    }
    override def toString = "Single"
  }

  object RefAccess extends ViewFactory {
    def apply[A](ref: Ref[A], innerDepth: Int): Ref.View[A] = new TestingView[A](innerDepth, ref) {
      protected val view = new DynamicView[A](ref)
    }
    override def toString = "Ref"
  }

  // The test environment is determined by
  //  outerLevels: the number of atomic block nesting levels that surround
  //               the entire test;
  //  innerLevels: the number of atomic block nesting levels that surround
  //               the individual operations of the test;
  //  refFactory:  Ref[Int] can be created with or without the appropriate
  //               manifest, or via the overloaded Ref.apply(Int); and
  //  viewFactory: one of FreshSingleAccess, ReuseSingleAccess, or RefAccess
  //               (which requires outerLevels + innerLevels > 0).
  //
  // Now we enumerate the environments, generating a set of tests for each
  // configuration.

  private def createTests[A : ClassManifest](name: String, v0: A)(block: (() => Ref.View[A]) => Unit) {
    test(name) {
      for (outerLevels <- 0 until 2;
           innerLevels <- 0 until 2;
           refFactory <- List(new KnownGenericFactory[A], new UnknownGenericFactory[A], new ArrayElementFactory[A]);
           viewFactory <- List(SingleAccess, RefAccess)
           if !(innerLevels + outerLevels == 0 && viewFactory == RefAccess)) {
        val current = "outer=" + outerLevels + ", inner=" + innerLevels + ", " + refFactory + ", " + viewFactory
        try {
          val ref = refFactory(v0)
          def getView = viewFactory(ref, innerLevels)
          nest(outerLevels) { block(getView _) }
        } catch {
          case x: Throwable => {
            println(name + " failed for " + current)
            fail(current + ": " + name + " failure", x)
          }
        }
      }
    }
  }

  test("primitive factory and ClassManifest generic produce same type") {
    // this cuts down on the proliferation of tests
    val g = new KnownGenericFactory[Int]
    assert(PrimitiveIntFactory(10).getClass === g(10).getClass)
  }

  private def nest(depth: Int)(block: => Unit) {
    if (depth == 0)
      block
    else
      atomic { implicit txn => nest(depth - 1)(block) }
  }

  createTests("get and set", 1) { view =>
    for (i <- 1 until 10) {
      assert(view()() === i)
      view()() = view()() + 1
    }
    assert(view()() === 10)
  }

  createTests("get and trySet", 1) { view =>
    for (i <- 1 until 10) {
      assert(view()() === i)
      val f = view().trySet(view()() + 1)
      assert(f) // trySet shouldn't fail in the absence of contention
    }
    assert(view()() === 10)
  }

  createTests("compareAndSet", 1) { view =>
    for (i <- 1 until 10) {
      assert(view()() === i)
      assert(!view().compareAndSet(0, -1))
      assert(view().compareAndSet(i, i + 1))
      assert(!view().compareAndSet(i, i + 1))
    }
    assert(view()() === 10)
  }

  createTests("swap", 1) { view =>
    for (i <- 1 until 10) {
      assert(view().swap(i + 1) === i)
    }
    assert(view()() === 10)
  }

  createTests("set + swap", 1) { view =>
    for (i <- 1 until 10) {
      view()() = -1
      assert(view().swap(i + 1) === -1)
    }
    assert(view()() === 10)
  }

  createTests("transform", 1) { view =>
    for (i <- 1 until 10) {
      assert(view()() === i)
      view().transform(_ + 1)
    }
    assert(view()() === 10)
  }

  createTests("getAndTransform", 1) { view =>
    for (i <- 1 until 10) {
      assert(view()() === i)
      assert(view().getAndTransform(_ + 1) === i)
    }
    assert(view()() === 10)
  }

  createTests("transformAndGet", 1) { view =>
    for (i <- 1 until 10) {
      assert(view()() === i)
      assert(view().transformAndGet(_ + 1) === i + 1)
    }
    assert(view()() === 10)
  }

  createTests("transformAndExtract", 1) { view =>
    for (i <- 1 until 10) {
      assert(view()() === i)
      assert(view().transformAndExtract { i => (i+1, ""+i) } === ""+i)
    }
    assert(view()() === 10)
  }

  createTests("transformIfDefined", 1) { view =>
    for (i <- 1 until 10) {
      assert(view()() === i)
      assert(!(view().transformIfDefined {
        case 0 => -1
      }))
      assert(view().transformIfDefined {
        case x if x > 0 => {
          assert(x === i)
          x + 1
        }
      })
    }
    assert(view()() === 10)
  }

  createTests("+= 1", 1) { view =>
    for (i <- 1 until 10) {
      assert(view()() === i)
      view() += 1
    }
    assert(view()() === 10)
  }

  createTests("-= -1", 1) { view =>
    for (i <- 1 until 10) {
      assert(view()() === i)
      view() -= -1
    }
    assert(view()() === 10)
  }

  createTests("*= 2", 1) { view =>
    for (i <- 1 until 10) {
      view() *= 2
    }
    assert(view()() === 512)
  }

  createTests("getWith", 1) { view =>
    assert(view().getWith(_ * 10) === 10)
  }

  createTests("write ; getWith", 1) { view =>
    view()() = 2
    assert(view().getWith(_ * 10) === 20)
  }

  createTests("getWith ; write", 1) { view =>
    assert(view().getWith(_ * 10) === 10)
    view()() = 2
  }

  createTests("relaxedGet", 10) { view =>
    assert(view().relaxedGet( _ == _ ) === 10)
  }

  createTests("write ; relaxedGet", 10) { view =>
    view()() = 20
    assert(view().relaxedGet( _ == _ ) === 20)
  }

  createTests("relaxedGet ; write", 10) { view =>
    assert(view().relaxedGet( _ == _ ) === 10)
    view()() = 20
  }

  createTests("initially true await", 10) { view =>
    view().await( _ == 10 )
  }

  createTests("initially true tryAwait", 10) { view =>
    assert(view().tryAwait(10000)( _ == 10 ))
  }

  createTests("false tryAwait with a zero timeout", 10) { view =>
    assert(!view().tryAwait(0)( _ == 20 ))
  }

  class UserException extends Exception

  createTests("excepting transform", 1) { view =>
    intercept[UserException] {
      view().transform(v => throw new UserException)
    }
    assert(view().get === 1)
    view().transform(_ + 1)
    assert(view().get === 2)
  }

  createTests("excepting transformIfDefined", 1) { view =>
    intercept[UserException] {
      view().transformIfDefined {
        case v if v > 0 => throw new UserException
        case v => v * 100
      }
    }
    assert(view().get === 1)
    view().transform(_ + 1)
    assert(view().get === 2)
  }

  class AngryEquals(val polarity: Boolean) {
    override def equals(rhs: Any): Boolean = {
      if (this eq rhs.asInstanceOf[AnyRef])
        true
      else {
        // equal polarities actively repel
        if (rhs.asInstanceOf[AngryEquals].polarity == polarity)
          throw new UserException
        false
      }
    }
  }

  createTests(".equals not involved in get and set", new AngryEquals(true)) { view =>
    assert(view().get ne null)
    view()() = new AngryEquals(true)
  }

  createTests("excepting compareAndSet", new AngryEquals(true)) { view =>
    val prev = view()()
    intercept[UserException] {
      view().compareAndSet(new AngryEquals(true), new AngryEquals(true))
    }
    assert(!view().compareAndSet(new AngryEquals(false), new AngryEquals(true)))
    val repl = new AngryEquals(false)
    assert(view().compareAndSet(prev, repl))
    assert(view().get === repl)
  }

  createTests("compareAndSetIdentity", "orig") { view =>
    assert(!view().compareAndSetIdentity(new String("orig"), "equal"))
    assert(view().compareAndSetIdentity("orig", "eq"))
    assert(view().get === "eq")
  }

  createTests("-= -1 long", Int.MaxValue + 1L) { view =>
    for (i <- 1L until 10L) {
      assert(view()() === Int.MaxValue + i)
      view() -= -1
    }
    assert(view()() === Int.MaxValue + 10L)
  }

  createTests("/=", 11) { view =>
    view() /= 2
    assert(view()() === 5)
  }

  createTests("/= double", 11.0) { view =>
    view() /= 2
    assert(view()() === 5.5)
  }

  createTests("/= float", 11.0f) { view =>
    view() /= 2
    assert(view()() === 5.5f)
  }

  createTests("BigInt ops", BigInt("1234")) { view =>
    view() += 1
    assert(view()().toString === "1235")
    view() -= 2
    assert(view()().toString === "1233")
    view() *= 3
    assert(view()().toString === "3699")
    view() /= 4
    assert(view()().toString === "924")
  }

  createTests("BigDecimal ops", BigDecimal("1234")) { view =>
    view() += 1
    assert(view()().toString === "1235")
    view() -= 2
    assert(view()().toString === "1233")
    view() *= 3
    assert(view()().toString === "3699")
    view() /= 4
    assert(view()().toString === "924.75")
  }

  createTests("TxnDebuggable", 10) { view =>
    assert(view().dbgStr === "Ref(10)")
    assert(view().dbgValue === 10)
    view()() = 11
    assert(view().dbgStr === "Ref(11)")
    assert(view().dbgValue === 11)
  }

  private def perTypeTests[A : ClassManifest](v0: A, v1: A) {
    val name = v0.asInstanceOf[AnyRef].getClass.getSimpleName

    createTests(name + " simple get+set", v0) { view =>
      assert(view()() === v0)
      view()() = v1
      assert(view()() === v1)
    }

    createTests(name + " Ref equality", v0) { view =>
      assert(view().asInstanceOf[Any] == view())
      assert(view().ref.asInstanceOf[Any] == view())
      assert(view().asInstanceOf[Any] == view().ref)
      assert(view().ref.asInstanceOf[Any] == view().ref)
      assert(view().ref.single.asInstanceOf[Any] == view())
      assert(view().asInstanceOf[Any] != Ref(v0))
      assert(view().asInstanceOf[Any] != "abc")
    }

    test(name + " TArray Ref equality") {
      val a = TArray(Seq(v0))
      assert(a.refs(0).asInstanceOf[Any] == a.refs(0))
      assert(a.single.refViews(0).asInstanceOf[Any] == a.refs(0))
      assert(a.single.refViews(0).ref.asInstanceOf[Any] == a.refs(0))
      assert(a.single.refViews(0).asInstanceOf[Any] == a.single.refViews(0))
      assert(a.refs(0).asInstanceOf[Any] == a.refs(0).single)
      assert(a.single.tarray.refs(0).asInstanceOf[Any] == a.refs(0).single)
      assert(a.refs(0).asInstanceOf[Any] != "abc")
    }

    test(name + " TArray Ref inequality between arrays") {
      val a = TArray(Seq(v0))
      val b = TArray(Seq(v1))
      assert(b.refs(0).asInstanceOf[Any] != a.refs(0))
      assert(b.single.refViews(0).asInstanceOf[Any] != a.refs(0))
      assert(b.single.refViews(0).ref.asInstanceOf[Any] != a.refs(0))
      assert(b.single.refViews(0).asInstanceOf[Any] != a.single.refViews(0))
      assert(b.refs(0).asInstanceOf[Any] != a.refs(0).single)
      assert(b.single.tarray.refs(0).asInstanceOf[Any] != a.refs(0).single)
    }
  }

  perTypeTests(false, true)
  perTypeTests(1 : Byte, 2 : Byte)
  perTypeTests(1 : Short, 2 : Short)
  perTypeTests('1', '2')
  perTypeTests(1, 2)
  perTypeTests(1.0f, 2.0f)
  perTypeTests(1L, 2L)
  perTypeTests(1.0, 2.0)
  perTypeTests((), ())
  perTypeTests("1", "2")

  test("TArray Ref inequality between indices") {
    val a = TArray.ofDim[Int](1000)
    println(a.refs(0))
    for (i <- 1 until 1000) {
      assert(a.refs(i).asInstanceOf[Any] != a.refs(0))
      assert(a.single.refViews(i).asInstanceOf[Any] != a.refs(0))
      assert(a.single.refViews(i).ref.asInstanceOf[Any] != a.refs(0))
      assert(a.single.refViews(i).asInstanceOf[Any] != a.single.refViews(0))
      assert(a.refs(i).asInstanceOf[Any] != a.refs(0).single)
      assert(a.single.tarray.refs(i).asInstanceOf[Any] != a.refs(0).single)
    }
  }

  test("TArray index checking") {
    val a = TArray.ofDim[String](10)
    for (i <- List(-1, 10, Int.MinValue, Int.MaxValue)) {
      intercept[ArrayIndexOutOfBoundsException] { a.single(i) }
      intercept[ArrayIndexOutOfBoundsException] { a.single(i) = "abc" }
      intercept[ArrayIndexOutOfBoundsException] { a.single.refViews(i) }
      intercept[ArrayIndexOutOfBoundsException] { a.refs(i) }
      intercept[ArrayIndexOutOfBoundsException] { atomic { implicit txn => a(i) } }
      intercept[ArrayIndexOutOfBoundsException] { atomic { implicit txn => a(i) = "abc" } }
    }
  }

  test("TArray length") {
    val a = TArray.ofDim[String](10)
    assert(a.length === 10)
    assert(a.single.length === 10)
    assert(a.refs.length === 10)
    assert(a.single.refViews.length === 10)

    val b = TArray.ofDim[String](0)
    assert(b.single.isEmpty)
  }

  test("TArray TxnDebuggable") {
    val a = TArray.ofDim[String](3)
    a.single(0) = "zero"
    a.refs(1).single() = "one"
    atomic { implicit txn => a(2) = "two" }

    assert(a.dbgStr === "TArray[size=3](zero, one, two)")
    val aa = a.dbgValue.asInstanceOf[Array[String]]
    assert(aa.length === 3)
    assert(aa(0) === "zero")
    assert(aa(1) === "one")
    assert(aa(2) === "two")
  }

  class ProxyRef[A](underlying: Ref[A]) extends Ref[A] {
    override def single = throw new AbstractMethodError
    def get(implicit txn: InTxn) = throw new AbstractMethodError
    def getWith[Z](f: (A) => Z)(implicit txn: InTxn) = throw new AbstractMethodError
    def relaxedGet(equiv: (A, A) => Boolean)(implicit txn: InTxn) = throw new AbstractMethodError
    def set(v: A)(implicit txn: InTxn) { throw new AbstractMethodError }
    def trySet(v: A)(implicit txn: InTxn) = throw new AbstractMethodError
    def swap(v: A)(implicit txn: InTxn) = throw new AbstractMethodError
    def transform(f: (A) => A)(implicit txn: InTxn) { throw new AbstractMethodError }
    def transformIfDefined(pf: PartialFunction[A, A])(implicit txn: InTxn) = throw new AbstractMethodError

    override def hashCode = underlying.hashCode
    override def equals(rhs: Any) = underlying.equals(rhs)
  }

  test("proxy Ref equality") {
    val lhs = Ref(10)
    val rhs = new ProxyRef(lhs)
    assert(lhs == rhs)
    assert(rhs == lhs)
    assert(rhs == rhs)
    assert(rhs != Ref(5))
    assert(Ref(5) != rhs)
  }

  test("TxnExecutor.compareAndSet") {
    val x = Ref("abc")
    val y = Ref("10")
    assert(!atomic.compareAndSet(x, "abc", "def", y, "11", "20"))
    assert(x.single() === "abc")
    assert(y.single() === "10")
    assert(!atomic.compareAndSet(x, "ABC", "def", y, "10", "20"))
    assert(x.single() === "abc")
    assert(y.single() === "10")
    assert(atomic.compareAndSet(x, "abc", "def", y, 10.toString, "20"))
    assert(x.single() === "def")
    assert(y.single() === "20")
  }

  test("TxnExecutor.compareAndSet non-txn exhaustive") {
    for (x0 <- List("abc", "ABC") ; x1 <- List("abc", "ABC") ; y0 <- List("def", "DEF") ; y1 <- List("def", "DEF")) {
      val x = Ref("abc")
      val y = Ref("def")
      val f = atomic.compareAndSet(x, x0, x1, y, y0, y1)
      if (f) {
        assert(x0 === "abc")
        assert(y0 === "def")
        assert(x.single() === x1)
        assert(y.single() === y1)
      } else {
        assert(x0 != "abc" || y0 != "def")
      }
    }
  }

  test("TxnExecutor.compareAndSet txn exhaustive") {
    for (x0 <- List("abc", "ABC") ; x1 <- List("abc", "ABC") ; y0 <- List("def", "DEF") ; y1 <- List("def", "DEF")) {
      val x = Ref("abc")
      val y = Ref("def")
      val f = atomic { implicit txn => atomic.compareAndSet(x, x0, x1, y, y0, y1) }
      if (f) {
        assert(x0 === "abc")
        assert(y0 === "def")
        assert(x.single() === x1)
        assert(y.single() === y1)
      } else {
        assert(x0 != "abc" || y0 != "def")
      }
    }
  }

  test("TxnExecutor.compareAndSetIdentity non-txn exhaustive") {
    for (x0 <- List("abc", "ABC") ; x1 <- List("abc", "ABC") ; y0 <- List("def", "DEF") ; y1 <- List("def", "DEF")) {
      val x = Ref("abc")
      val y = Ref("def")
      val f = atomic.compareAndSetIdentity(x, x0, x1, y, y0, y1)
      if (f) {
        assert(x0 === "abc")
        assert(y0 === "def")
        assert(x.single() === x1)
        assert(y.single() === y1)
      } else {
        assert(x0 != "abc" || y0 != "def")
      }
    }
  }

  test("TxnExecutor.compareAndSetIdentity txn exhaustive") {
    for (x0 <- List("abc", "ABC") ; x1 <- List("abc", "ABC") ; y0 <- List("def", "DEF") ; y1 <- List("def", "DEF")) {
      val x = Ref("abc")
      val y = Ref("def")
      val f = atomic { implicit txn => atomic.compareAndSetIdentity(x, x0, x1, y, y0, y1) }
      if (f) {
        assert(x0 === "abc")
        assert(y0 === "def")
        assert(x.single() === x1)
        assert(y.single() === y1)
      } else {
        assert(x0 != "abc" || y0 != "def")
      }
    }
  }
}
