package io.reactors
package remote



import io.reactors.common.Cell
import io.reactors.marshal.Marshalee
import io.reactors.test._
import org.scalacheck.Prop.forAllNoShrink
import org.scalacheck.Properties
import scala.collection._
import org.scalatest.funsuite.AnyFunSuite



class RuntimeMarshalerTest extends AnyFunSuite {
  test("marshal empty non-final class") {
    val buffer = DataBuffer.streaming(128)
    RuntimeMarshaler.marshal(new NonFinalEmpty, buffer)
    println(buffer.input.byteString)
    val obj = RuntimeMarshaler.unmarshal[NonFinalEmpty](buffer)
    assert(obj.isInstanceOf[NonFinalEmpty])
  }

  test("marshal empty final class") {
    val buffer = DataBuffer.streaming(128)
    RuntimeMarshaler.marshal(new FinalEmpty, buffer)
    println(buffer.input.byteString)
    val obj = RuntimeMarshaler.unmarshal[FinalEmpty](buffer)
    assert(obj.isInstanceOf[FinalEmpty])
  }

  test("marshal single integer field non-final class") {
    val buffer = DataBuffer.streaming(128)
    RuntimeMarshaler.marshal(new NonFinalSingleInt(15), buffer)
    println(buffer.input.byteString)
    val obj = RuntimeMarshaler.unmarshal[NonFinalSingleInt](buffer)
    assert(obj.x == 15)
  }

  test("marshal single integer field final class") {
    val buffer = DataBuffer.streaming(128)
    RuntimeMarshaler.marshal(new FinalSingleInt(15), buffer)
    println(buffer.input.byteString)
    val obj = RuntimeMarshaler.unmarshal[FinalSingleInt](buffer)
    assert(obj.x == 15)
  }

  test("marshal single long field class") {
    val buffer = DataBuffer.streaming(128)
    RuntimeMarshaler.marshal(new SingleLong(15), buffer)
    println(buffer.input.byteString)
    val obj = RuntimeMarshaler.unmarshal[SingleLong](buffer)
    assert(obj.x == 15)
  }

  test("marshal single int field class, when buffer is small") {
    val buffer = DataBuffer.streaming(128)
    RuntimeMarshaler.marshal(new FinalSingleInt(15), buffer)
    println(buffer.input.byteString)
    val obj = RuntimeMarshaler.unmarshal[FinalSingleInt](buffer)
    assert(obj.x == 15)
  }

  test("marshal single long field class, when buffer is small") {
    val buffer = DataBuffer.streaming(128)
    RuntimeMarshaler.marshal(new SingleLong(15), buffer)
    println(buffer.input.byteString)
    val obj = RuntimeMarshaler.unmarshal[SingleLong](buffer)
    assert(obj.x == 15)
  }

  test("marshal single double field class") {
    val buffer = DataBuffer.streaming(128)
    RuntimeMarshaler.marshal(new SingleDouble(15.0), buffer)
    println(buffer.input.byteString)
    val obj = RuntimeMarshaler.unmarshal[SingleDouble](buffer)
    assert(obj.x == 15.0)
  }

  test("marshal single double field class, when buffer is small") {
    val buffer = DataBuffer.streaming(128)
    RuntimeMarshaler.marshal(new SingleDouble(15.0), buffer)
    println(buffer.input.byteString)
    val obj = RuntimeMarshaler.unmarshal[SingleDouble](buffer)
    assert(obj.x == 15.0)
  }

  test("marshal single float field class") {
    val buffer = DataBuffer.streaming(128)
    RuntimeMarshaler.marshal(new SingleFloat(15.0f), buffer)
    println(buffer.input.byteString)
    val obj = RuntimeMarshaler.unmarshal[SingleFloat](buffer)
    assert(obj.x == 15.0f)
  }

  test("marshal single float field class, when buffer is small") {
    val buffer = DataBuffer.streaming(128)
    RuntimeMarshaler.marshal(new SingleFloat(15.0f), buffer)
    println(buffer.input.byteString)
    val obj = RuntimeMarshaler.unmarshal[SingleFloat](buffer)
    assert(obj.x == 15.0f)
  }

  test("marshal single byte field class") {
    val buffer = DataBuffer.streaming(128)
    RuntimeMarshaler.marshal(new SingleByte(7), buffer)
    println(buffer.input.byteString)
    val obj = RuntimeMarshaler.unmarshal[SingleByte](buffer)
    assert(obj.x == 7)
  }

  test("marshal single boolean field class") {
    val buffer = DataBuffer.streaming(128)
    RuntimeMarshaler.marshal(new SingleBoolean(true), buffer)
    println(buffer.input.byteString)
    val obj = RuntimeMarshaler.unmarshal[SingleBoolean](buffer)
    assert(obj.x == true)
  }

  test("marshal single char field class") {
    val buffer = DataBuffer.streaming(128)
    RuntimeMarshaler.marshal(new SingleChar('a'), buffer)
    println(buffer.input.byteString)
    val obj = RuntimeMarshaler.unmarshal[SingleChar](buffer)
    assert(obj.x == 'a')
  }

  test("marshal single short field class") {
    val buffer = DataBuffer.streaming(128)
    RuntimeMarshaler.marshal(new SingleShort(17), buffer)
    println(buffer.input.byteString)
    val obj = RuntimeMarshaler.unmarshal[SingleShort](buffer)
    assert(obj.x == 17)
  }

  test("marshal mixed primitive field class") {
    val buffer = DataBuffer.streaming(128)
    RuntimeMarshaler.marshal(new MixedPrimitives(17, 9, 2.1, true, 8.11f, 'd'), buffer)
    println(buffer.input.byteString)
    val obj = RuntimeMarshaler.unmarshal[MixedPrimitives](buffer)
    assert(obj.x == 17)
    assert(obj.y == 9)
    assert(obj.z == 2.1)
    assert(obj.b == true)
    assert(obj.f == 8.11f)
    assert(obj.c == 'd')
  }

  test("marshal object with a final class object field") {
    val buffer = DataBuffer.streaming(128)
    RuntimeMarshaler.marshal(new FinalClassObject(new FinalSingleInt(17)), buffer)
    println(buffer.input.byteString)
    val obj = RuntimeMarshaler.unmarshal[FinalClassObject](buffer)
    assert(obj.inner.x == 17)
  }

  test("marshal recursive object") {
    val buffer = DataBuffer.streaming(128)
    RuntimeMarshaler.marshal(
      new RecursiveObject(7, new RecursiveObject(5, null)), buffer)
    println(buffer.input.byteString)
    val obj = RuntimeMarshaler.unmarshal[RecursiveObject](buffer)
    assert(obj.x == 7 && obj.tail.x == 5 && obj.tail.tail == null)
  }

  test("marshal null") {
    val buffer = DataBuffer.streaming(128)
    RuntimeMarshaler.marshal(null, buffer)
    println(buffer.input.byteString)
    val obj = RuntimeMarshaler.unmarshal[AnyRef](buffer)
    assert(obj == null)
  }

  test("marshal a cyclic object") {
    val buffer = DataBuffer.streaming(128)
    val cyclic = new RecursiveObject(7, null)
    cyclic.tail = cyclic
    RuntimeMarshaler.marshal(cyclic, buffer)
    println(buffer.input.byteString)
    val obj = RuntimeMarshaler.unmarshal[RecursiveObject](buffer)
    assert(obj.tail eq obj)
    assert(obj.x == 7)
  }

  test("marshal a cyclic pair of objects") {
    val buffer = DataBuffer.streaming(128)
    val a = new RecursiveObject(7, null)
    val b = new RecursiveObject(11, null)
    a.tail = b
    b.tail = a
    RuntimeMarshaler.marshal(a, buffer)
    println(buffer.input.byteString)
    val obj = RuntimeMarshaler.unmarshal[RecursiveObject](buffer)
    assert(obj.x == 7)
    assert(obj.tail.x == 11)
    assert(obj.tail.tail eq obj)
  }

  test("marshal an inherited class") {
    val buffer = DataBuffer.streaming(128)
    val obj = new InheritedClass(17, 11)
    RuntimeMarshaler.marshal(obj, buffer)
    println(buffer.input.byteString)
    val result = RuntimeMarshaler.unmarshal[InheritedClass](buffer)
    assert(result.y == 17)
    assert(result.x == 11)
  }

  test("marshal an object pair") {
    val buffer = DataBuffer.streaming(128)
    val pair = new CyclicObjectPair(7,
      new CyclicObjectPair(11, null, null),
      new CyclicObjectPair(17, null, null)
    )
    pair.o1.o1 = pair
    pair.o2.o2 = pair
    RuntimeMarshaler.marshal(pair, buffer)
    println(buffer.input.byteString)
    val obj = RuntimeMarshaler.unmarshal[CyclicObjectPair](buffer)
    assert(obj.x == 7)
    assert(obj.o1.x == 11)
    assert(obj.o2.x == 17)
    assert(obj.o1.o1 == obj)
    assert(obj.o2.o2 == obj)
  }

  test("marshal an object with an array") {
    val buffer = DataBuffer.streaming(128)
    val input = new ArrayObject(10)
    for (i <- 0 until 10) input.array(i) = i + 11
    RuntimeMarshaler.marshal(input, buffer)
    println(buffer.input.byteString)
    val obj = RuntimeMarshaler.unmarshal[ArrayObject](buffer)
    assert(obj.array != null)
    for (i <- 0 until 10) assert(input.array(i) == i + 11)
  }

  test("marshal an object with a big array") {
    val buffer = DataBuffer.streaming(128)
    val input = new ArrayObject(256)
    for (i <- 0 until 256) input.array(i) = i + 17
    RuntimeMarshaler.marshal(input, buffer)
    println(buffer.input.byteString)
    val obj = RuntimeMarshaler.unmarshal[ArrayObject](buffer)
    assert(obj.array != null)
    for (i <- 0 until 256) assert(input.array(i) == i + 17)
  }

  test("marshal an object with a null array") {
    val buffer = DataBuffer.streaming(128)
    val input = new VarArrayObject(null)
    RuntimeMarshaler.marshal(input, buffer)
    println(buffer.input.byteString)
    val obj = RuntimeMarshaler.unmarshal[VarArrayObject](buffer)
    assert(obj.array == null)
  }

  test("marshal an int array") {
    val buffer = DataBuffer.streaming(128)
    val input = new Array[Int](10)
    for (i <- 0 until 10) input(i) = i + 3
    RuntimeMarshaler.marshal(input, buffer)
    println(buffer.input.byteString)
    val obj = RuntimeMarshaler.unmarshal[Array[Int]](buffer)
    assert(obj.length == 10)
    for (i <- 0 until 10) assert(obj(i) == i + 3)
  }

  test("marshal a big int array") {
    val buffer = DataBuffer.streaming(128)
    val input = new Array[Int](256)
    for (i <- 0 until 256) input(i) = i + 3
    RuntimeMarshaler.marshal(input, buffer)
    println(buffer.input.byteString)
    val obj = RuntimeMarshaler.unmarshal[Array[Int]](buffer)
    assert(obj.length == 256)
    for (i <- 0 until 256) assert(obj(i) == i + 3)
  }

  test("marshal a long array") {
    val buffer = DataBuffer.streaming(128)
    val input = new Array[Long](256)
    for (i <- 0 until 256) input(i) = i + 3
    RuntimeMarshaler.marshal(input, buffer)
    println(buffer.input.byteString)
    val obj = RuntimeMarshaler.unmarshal[Array[Long]](buffer)
    assert(obj.length == 256)
    for (i <- 0 until 256) assert(obj(i) == i + 3)
  }

  test("marshal an object with a long array") {
    val buffer = DataBuffer.streaming(128)
    val input = new LongArrayObject(256)
    for (i <- 0 until 256) input.array(i) = i + 3
    RuntimeMarshaler.marshal(input, buffer)
    println(buffer.input.byteString)
    val obj = RuntimeMarshaler.unmarshal[LongArrayObject](buffer)
    assert(obj.array.length == 256)
    for (i <- 0 until 256) assert(obj.array(i) == i + 3)
  }

  test("marshal an object with a double array") {
    val buffer = DataBuffer.streaming(128)
    val input = new DoubleArrayObject(256)
    for (i <- 0 until 256) input.array(i) = i + 3.5
    RuntimeMarshaler.marshal(input, buffer)
    println(buffer.input.byteString)
    val obj = RuntimeMarshaler.unmarshal[DoubleArrayObject](buffer)
    assert(obj.array.length == 256)
    for (i <- 0 until 256) assert(obj.array(i) == i + 3.5)
  }

  test("marshal an object with a float array") {
    val buffer = DataBuffer.streaming(128)
    val input = new FloatArrayObject(256)
    for (i <- 0 until 256) input.array(i) = i + 3.5f
    RuntimeMarshaler.marshal(input, buffer)
    println(buffer.input.byteString)
    val obj = RuntimeMarshaler.unmarshal[FloatArrayObject](buffer)
    assert(obj.array.length == 256)
    for (i <- 0 until 256) assert(obj.array(i) == i + 3.5f)
  }

  test("marshal an object with a byte array") {
    val buffer = DataBuffer.streaming(128)
    val input = new ByteArrayObject(256)
    for (i <- 0 until 256) input.array(i) = (i + 3).toByte
    RuntimeMarshaler.marshal(input, buffer)
    println(buffer.input.byteString)
    val obj = RuntimeMarshaler.unmarshal[ByteArrayObject](buffer)
    assert(obj.array.length == 256)
    for (i <- 0 until 256) assert(obj.array(i) == (i + 3).toByte)
  }

  test("marshal an object with a boolean array") {
    val buffer = DataBuffer.streaming(128)
    val input = new BooleanArrayObject(256)
    for (i <- 0 until 256) input.array(i) = i % 3 != 0
    RuntimeMarshaler.marshal(input, buffer)
    println(buffer.input.byteString)
    val obj = RuntimeMarshaler.unmarshal[BooleanArrayObject](buffer)
    assert(obj.array.length == 256)
    for (i <- 0 until 256) assert(obj.array(i) == (i % 3 != 0))
  }

  test("marshal an object with a char array") {
    val buffer = DataBuffer.streaming(128)
    val input = new CharArrayObject(256)
    for (i <- 0 until 256) input.array(i) = i.toChar
    RuntimeMarshaler.marshal(input, buffer)
    println(buffer.input.byteString)
    val obj = RuntimeMarshaler.unmarshal[CharArrayObject](buffer)
    assert(obj.array.length == 256)
    for (i <- 0 until 256) assert(obj.array(i) == i.toChar)
  }

  test("marshal an object with a short array") {
    val buffer = DataBuffer.streaming(128)
    val input = new ShortArrayObject(256)
    for (i <- 0 until 256) input.array(i) = i.toShort
    RuntimeMarshaler.marshal(input, buffer)
    println(buffer.input.byteString)
    val obj = RuntimeMarshaler.unmarshal[ShortArrayObject](buffer)
    assert(obj.array.length == 256)
    for (i <- 0 until 256) assert(obj.array(i) == i.toShort)
  }

  test("marshal an object with a object array") {
    val buffer = DataBuffer.streaming(128)
    val input = new ObjectArrayObject(256)
    for (i <- 0 until 256) input.array(i) = new SingleLong(i)
    RuntimeMarshaler.marshal(input, buffer)
    println(buffer.input.byteString)
    val obj = RuntimeMarshaler.unmarshal[ObjectArrayObject](buffer)
    assert(obj.array.length == 256)
    for (i <- 0 until 256) assert(obj.array(i).x == i, s"$i == ${obj.array(i)}")
  }

  test("marshal an object with a final object array") {
    val buffer = DataBuffer.streaming(128)
    val input = new FinalObjectArrayObject(256)
    for (i <- 0 until 256) input.array(i) = new FinalSingleInt(i)
    RuntimeMarshaler.marshal(input, buffer)
    println(buffer.input.byteString)
    val obj = RuntimeMarshaler.unmarshal[FinalObjectArrayObject](buffer)
    assert(obj.array.length == 256)
    for (i <- 0 until 256) assert(obj.array(i).x == i, s"$i == ${obj.array(i)}")
  }

  test("marshal an array of repeated and null objects") {
    val buffer = DataBuffer.streaming(128)
    val input = new Array[AnyRef](256)
    for (i <- 0 until 256) input(i) = i match {
      case i if i % 5 == 0 => null
      case i if i % 6 == 0 => input(i - 5)
      case i if i % 11 == 0 => new SingleLong(i)
      case _ => new FinalSingleInt(i)
    }
    RuntimeMarshaler.marshal(input, buffer)
    println(buffer.input.byteString)
    val array = RuntimeMarshaler.unmarshal[Array[AnyRef]](buffer)
    assert(array.length == 256)
    for (i <- 0 until 256) i match {
      case i if i % 5 == 0 =>
        assert(array(i) == null)
      case i if i % 6 == 0 =>
        assert(array(i) eq array(i - 5))
        input(i) match {
          case null =>
            assert(array(i) == null)
          case obj: FinalSingleInt =>
            assert(array(i).asInstanceOf[FinalSingleInt].x == obj.x)
          case obj: SingleLong =>
            assert(array(i).asInstanceOf[SingleLong].x == obj.x)
        }
      case i if i % 11 == 0 =>
        assert(array(i).isInstanceOf[SingleLong])
        assert(array(i).asInstanceOf[SingleLong].x == i)
      case _ =>
        assert(array(i).asInstanceOf[FinalSingleInt].x == i)
    }
  }

  test("marshal an array pointing to itself") {
    val buffer = DataBuffer.streaming(128)
    val input = new Array[AnyRef](256)
    for (i <- 0 until 256) input(i) = input
    RuntimeMarshaler.marshal(input, buffer)
    println(buffer.input.byteString)
    val obj = RuntimeMarshaler.unmarshal[Array[AnyRef]](buffer)
    assert(obj.array.length == 256)
    for (i <- 0 until 256) assert(obj(i) eq obj)
  }

  test("marshal an array buffer") {
    val buffer = DataBuffer.streaming(128)
    val input = mutable.ArrayBuffer[Int]()
    for (i <- 0 until 128) input += i
    RuntimeMarshaler.marshal(input, buffer)
    println(buffer.input.byteString)
    val obj = RuntimeMarshaler.unmarshal[mutable.ArrayBuffer[Int]](buffer)
    assert(obj.length == 128)
    for (i <- 0 until 128) assert(obj(i) == i)
  }

  test("marshal a list") {
    val buffer = DataBuffer.streaming(128)
    val input = (0 until 100).toList
    RuntimeMarshaler.marshal(input, buffer)
    println(buffer.input.byteString)
    val obj = RuntimeMarshaler.unmarshal[List[Int]](buffer)
    assert(obj.length == 100)
    for (i <- 0 until 100) assert(obj(i) == i)
  }
}


class NonFinalEmpty extends Marshalee


final class FinalEmpty extends Marshalee


class NonFinalSingleInt(val x: Int) extends Marshalee


final class FinalSingleInt(val x: Int) extends Marshalee


class SingleLong(val x: Long) extends Marshalee


class SingleDouble(val x: Double) extends Marshalee


class SingleFloat(val x: Float) extends Marshalee


class SingleByte(val x: Byte) extends Marshalee


class SingleBoolean(val x: Boolean) extends Marshalee


class SingleChar(val x: Char) extends Marshalee


class SingleShort(val x: Short) extends Marshalee


class MixedPrimitives(
  val x: Int, var y: Short, val z: Double, val b: Boolean, val f: Float, val c: Char
) extends Marshalee


class FinalClassObject(val inner: FinalSingleInt) extends Marshalee


class RecursiveObject(val x: Int, var tail: RecursiveObject) extends Marshalee


class BaseClass(val x: Int) extends Marshalee


class InheritedClass(val y: Int, px: Int) extends BaseClass(px) with Marshalee


class CyclicObjectPair(val x: Int, var o1: CyclicObjectPair, var o2: CyclicObjectPair)
extends Marshalee


class ArrayObject(length: Int) extends Marshalee {
  val array = new Array[Int](length)
}


class VarArrayObject(var array: Array[Int]) extends Marshalee


class LongArrayObject(length: Int) extends Marshalee {
  val array = new Array[Long](length)
}


class DoubleArrayObject(length: Int) extends Marshalee {
  val array = new Array[Double](length)
}


class FloatArrayObject(length: Int) extends Marshalee {
  val array = new Array[Float](length)
}


class ByteArrayObject(length: Int) extends Marshalee {
  val array = new Array[Byte](length)
}


class BooleanArrayObject(length: Int) extends Marshalee {
  val array = new Array[Boolean](length)
}


class CharArrayObject(length: Int) extends Marshalee {
  val array = new Array[Char](length)
}


class ShortArrayObject(length: Int) extends Marshalee {
  val array = new Array[Short](length)
}


class ObjectArrayObject(length: Int) extends Marshalee {
  val array = new Array[SingleLong](length)
}


class FinalObjectArrayObject(length: Int) extends Marshalee {
  val array = new Array[FinalSingleInt](length)
}


class LinkedList(val head: Int, val tail: LinkedList) extends Marshalee


class RuntimeMarshalerCheck
extends Properties("RuntimeMarshaler") with ExtendedProperties {
  val sizes = detChoose(0, 1000)

  val smallSizes = detChoose(0, 100)

  val depths = detChoose(0, 12)

  property("integer arrays") = forAllNoShrink(sizes) { size =>
    stackTraced {
      val buffer = DataBuffer.streaming(128)
      val array = new Array[Int](size)
      for (i <- 0 until size) array(i) = i
      RuntimeMarshaler.marshal(array, buffer)
      val result = RuntimeMarshaler.unmarshal[Array[Int]](buffer)
      assert(result.length == size)
      for (i <- 0 until size) assert(array(i) == i)
      true
    }
  }

  property("object arrays") = forAllNoShrink(sizes) { size =>
    stackTraced {
      val buffer = DataBuffer.streaming(128)
      val array = new Array[AnyRef](size)
      for (i <- 0 until size) array(i) = i.toString
      RuntimeMarshaler.marshal(array, buffer)
      val result = RuntimeMarshaler.unmarshal[Array[AnyRef]](buffer)
      assert(result.length == size)
      for (i <- 0 until size) assert(array(i) == i.toString)
      true
    }
  }

  property("circular arrays") = forAllNoShrink(sizes) { size =>
    stackTraced {
      val buffer = DataBuffer.streaming(128)
      val array = new Array[AnyRef](size)
      for (i <- 0 until size) {
        if (i % 2 == 0) array(i) = array
        else array(i) = new Array[Int](0)
      }
      RuntimeMarshaler.marshal(array, buffer)
      val result = RuntimeMarshaler.unmarshal[Array[AnyRef]](buffer)
      assert(result.length == size)
      for (i <- 0 until size) {
        if (i % 2 == 0) assert(array(i) == array)
        else assert(array(i).asInstanceOf[Array[Int]].length == 0)
      }
      true
    }
  }

  property("linked lists") = forAllNoShrink(smallSizes) { size =>
    stackTraced {
      val buffer = DataBuffer.streaming(128)
      var list: LinkedList = null
      for (i <- 0 until size) list = new LinkedList(i, list)
      RuntimeMarshaler.marshal(list, buffer)
      var result = RuntimeMarshaler.unmarshal[LinkedList](buffer)
      for (i <- (0 until size).reverse) {
        assert(result.head == i)
        result = result.tail
      }
      assert(result == null, result.tail)
      true
    }
  }

  property("trees") = forAllNoShrink(depths) { maxDepth =>
    stackTraced {
      val buffer = DataBuffer.streaming(128)
      val root = new Array[AnyRef](3)
      def generate(node: Array[AnyRef], depth: Int): Unit = if (depth < maxDepth) {
        val left = new Array[AnyRef](3)
        val right = new Array[AnyRef](3)
        left(2) = depth.toString
        right(2) = depth.toString
        node(0) = left
        node(1) = right
        generate(left, depth + 1)
        generate(right, depth + 1)
      }
      generate(root, 0)
      RuntimeMarshaler.marshal(root, buffer)
      var result = RuntimeMarshaler.unmarshal[Array[AnyRef]](buffer)
      def compare(before: Array[AnyRef], after: Array[AnyRef]): Unit = {
        if (before == null) assert(after == null)
        else {
          def asNode(x: AnyRef) = x.asInstanceOf[Array[AnyRef]]
          assert(before(2) == after(2))
          compare(asNode(before(0)), asNode(after(0)))
          compare(asNode(before(1)), asNode(after(1)))
        }
      }
      compare(root, result)
      true
    }
  }

  property("array buffers") = forAllNoShrink(sizes) { size =>
    stackTraced {
      val buffer = DataBuffer.streaming(128)
      val arrayBuffer = mutable.ArrayBuffer[Int]()
      for (i <- 0 until size) arrayBuffer += i
      RuntimeMarshaler.marshal(arrayBuffer, buffer)
      val result = RuntimeMarshaler.unmarshal[mutable.ArrayBuffer[Int]](buffer)
      assert(result.length == size, s"${result.length}, expected $size")
      for (i <- 0 until size) assert(result(i) == arrayBuffer(i))
      true
    }
  }

  property("hash tries") = forAllNoShrink(sizes) { size =>
    stackTraced {
      val buffer = DataBuffer.streaming(128)
      var map = immutable.HashMap[Int, String]()
      for (i <- 0 until size) map += i -> i.toString
      RuntimeMarshaler.marshal(map, buffer)
      val result = RuntimeMarshaler.unmarshal[immutable.HashMap[Int, String]](buffer)
      assert(result.size == size, s"${result.size}, expected $size")
      for (i <- 0 until size) assert(result(i) == i.toString)
      true
    }
  }
}
