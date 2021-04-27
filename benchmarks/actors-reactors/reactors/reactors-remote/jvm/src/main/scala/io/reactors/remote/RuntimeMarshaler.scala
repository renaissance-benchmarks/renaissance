package io.reactors
package remote



import java.lang.reflect.Modifier
import io.reactors.Reactor.MarshalContext
import io.reactors.marshal.ClassDescriptor
import scala.annotation.switch
import scala.reflect.ClassTag



object RuntimeMarshaler {
  private val unsafe = io.reactors.common.concurrent.Platform.unsafe

  private def classNameTerminatorTag: Byte = 1

  private def objectReferenceTag: Byte = 2

  private def nullTag: Byte = 3

  private def arrayTag: Byte = 4

  private def maxArrayChunk: Int = 2048

  def marshal[T](obj: T, buffer: DataBuffer, marshalType: Boolean = true): Unit = {
    val context = Reactor.marshalContext
    val data = internalMarshal(obj, buffer.output, false, marshalType, true, context)
    context.resetMarshal()
  }

  def marshalAs[T](
    klazz: Class[_], obj: T, buffer: DataBuffer, alreadyRecorded: Boolean
  ): Unit = {
    val desc = Platform.Reflect.descriptorOf(klazz)
    marshalAs(desc, obj, buffer, alreadyRecorded)
  }

  def marshalAs[T](
    desc: ClassDescriptor, obj: T, buffer: DataBuffer, alreadyRecorded: Boolean
  ): Unit = {
    if (obj == null) {
      var data = buffer.output
      if (data.remainingWriteSize < 1) data = data.writeNext(1)
      data(data.endPos) = nullTag
      data.endPos += 1
    } else {
      val ctx = Reactor.marshalContext
      val data = internalMarshalAs(desc, obj, buffer.output, true, alreadyRecorded, ctx)
      ctx.resetMarshal()
    }
  }

  private def internalMarshalArray(
    array: AnyRef, tpe: Class[_],
    inputData: Data, context: Reactor.MarshalContext
  ): Data = {
    var data = inputData
    val length = java.lang.reflect.Array.getLength(array)
    data = marshalByte(arrayTag, data)
    data = marshalInt(length, data)
    val elementType = tpe.getComponentType
    elementType match {
      case Platform.Reflect.intClass =>
        val intArray = array.asInstanceOf[Array[Int]]
        var i = 0
        while (i < length) {
          val batchSize = math.min(data.remainingWriteSize / 4, length - i)
          var j = i
          var pos = data.endPos
          while (j < i + batchSize) {
            val v = intArray(j)
            data(pos + 0) = ((v & 0x000000ff) >>> 0).toByte
            data(pos + 1) = ((v & 0x0000ff00) >>> 8).toByte
            data(pos + 2) = ((v & 0x00ff0000) >>> 16).toByte
            data(pos + 3) = ((v & 0xff000000) >>> 24).toByte
            pos += 4
            j += 1
          }
          i += batchSize
          data.endPos += batchSize * 4
          data = data.writeNext(math.min(4 * (length - i), maxArrayChunk))
        }
      case Platform.Reflect.longClass =>
        val longArray = array.asInstanceOf[Array[Long]]
        var i = 0
        while (i < length) {
          val batchSize = math.min(data.remainingWriteSize / 8, length - i)
          var j = i
          var pos = data.endPos
          while (j < i + batchSize) {
            val v = longArray(j)
            data(pos + 0) = ((v & 0x00000000000000ffL) >>> 0).toByte
            data(pos + 1) = ((v & 0x000000000000ff00L) >>> 8).toByte
            data(pos + 2) = ((v & 0x0000000000ff0000L) >>> 16).toByte
            data(pos + 3) = ((v & 0x00000000ff000000L) >>> 24).toByte
            data(pos + 4) = ((v & 0x000000ff00000000L) >>> 32).toByte
            data(pos + 5) = ((v & 0x0000ff0000000000L) >>> 40).toByte
            data(pos + 6) = ((v & 0x00ff000000000000L) >>> 48).toByte
            data(pos + 7) = ((v & 0xff00000000000000L) >>> 56).toByte
            pos += 8
            j += 1
          }
          i += batchSize
          data.endPos += batchSize * 8
          data = data.writeNext(math.min(8 * (length - i), maxArrayChunk))
        }
      case Platform.Reflect.doubleClass =>
        val doubleArray = array.asInstanceOf[Array[Double]]
        var i = 0
        while (i < length) {
          val batchSize = math.min(data.remainingWriteSize / 8, length - i)
          var j = i
          var pos = data.endPos
          while (j < i + batchSize) {
            val v = doubleArray(j)
            val bits = java.lang.Double.doubleToRawLongBits(v)
            data(pos + 0) = ((bits & 0x00000000000000ffL) >>> 0).toByte
            data(pos + 1) = ((bits & 0x000000000000ff00L) >>> 8).toByte
            data(pos + 2) = ((bits & 0x0000000000ff0000L) >>> 16).toByte
            data(pos + 3) = ((bits & 0x00000000ff000000L) >>> 24).toByte
            data(pos + 4) = ((bits & 0x000000ff00000000L) >>> 32).toByte
            data(pos + 5) = ((bits & 0x0000ff0000000000L) >>> 40).toByte
            data(pos + 6) = ((bits & 0x00ff000000000000L) >>> 48).toByte
            data(pos + 7) = ((bits & 0xff00000000000000L) >>> 56).toByte
            pos += 8
            j += 1
          }
          i += batchSize
          data.endPos += batchSize * 8
          data = data.writeNext(math.min(8 * (length - i), maxArrayChunk))
        }
      case Platform.Reflect.floatClass =>
        val floatArray = array.asInstanceOf[Array[Float]]
        var i = 0
        while (i < length) {
          val batchSize = math.min(data.remainingWriteSize / 4, length - i)
          var j = i
          var pos = data.endPos
          while (j < i + batchSize) {
            val v = floatArray(j)
            val bits = java.lang.Float.floatToRawIntBits(v)
            data(pos + 0) = ((bits & 0x000000ff) >>> 0).toByte
            data(pos + 1) = ((bits & 0x0000ff00) >>> 8).toByte
            data(pos + 2) = ((bits & 0x00ff0000) >>> 16).toByte
            data(pos + 3) = ((bits & 0xff000000) >>> 24).toByte
            pos += 4
            j += 1
          }
          i += batchSize
          data.endPos += batchSize * 4
          data = data.writeNext(math.min(4 * (length - i), maxArrayChunk))
        }
      case Platform.Reflect.byteClass =>
        val byteArray = array.asInstanceOf[Array[Byte]]
        var i = 0
        while (i < length) {
          val batchSize = math.min(data.remainingWriteSize / 1, length - i)
          var j = i
          var pos = data.endPos
          while (j < i + batchSize) {
            val v = byteArray(j)
            data(pos + 0) = v
            pos += 1
            j += 1
          }
          i += batchSize
          data.endPos += batchSize * 1
          data = data.writeNext(math.min(1 * (length - i), maxArrayChunk))
        }
      case Platform.Reflect.booleanClass =>
        val booleanArray = array.asInstanceOf[Array[Boolean]]
        var i = 0
        while (i < length) {
          val batchSize = math.min(data.remainingWriteSize / 1, length - i)
          var j = i
          var pos = data.endPos
          while (j < i + batchSize) {
            val v = booleanArray(j)
            data(pos + 0) = if (v) 1 else 0
            pos += 1
            j += 1
          }
          i += batchSize
          data.endPos += batchSize * 1
          data = data.writeNext(math.min(1 * (length - i), maxArrayChunk))
        }
      case Platform.Reflect.charClass =>
        val charArray = array.asInstanceOf[Array[Char]]
        var i = 0
        while (i < length) {
          val batchSize = math.min(data.remainingWriteSize / 2, length - i)
          var j = i
          var pos = data.endPos
          while (j < i + batchSize) {
            val v = charArray(j)
            data(pos + 0) = ((v & 0x000000ff) >>> 0).toByte
            data(pos + 1) = ((v & 0x0000ff00) >>> 8).toByte
            pos += 2
            j += 1
          }
          i += batchSize
          data.endPos += batchSize * 2
          data = data.writeNext(math.min(2 * (length - i), maxArrayChunk))
        }
      case Platform.Reflect.shortClass =>
        val shortArray = array.asInstanceOf[Array[Short]]
        var i = 0
        while (i < length) {
          val batchSize = math.min(data.remainingWriteSize / 2, length - i)
          var j = i
          var pos = data.endPos
          while (j < i + batchSize) {
            val v = shortArray(j)
            data(pos + 0) = ((v & 0x000000ff) >>> 0).toByte
            data(pos + 1) = ((v & 0x0000ff00) >>> 8).toByte
            pos += 2
            j += 1
          }
          i += batchSize
          data.endPos += batchSize * 2
          data = data.writeNext(math.min(2 * (length - i), maxArrayChunk))
        }
      case _ =>
        val objectArray = array.asInstanceOf[Array[AnyRef]]
        val marshalElementType = !Modifier.isFinal(elementType.getModifiers)
        var i = 0
        while (i < length) {
          val elem = objectArray(i)
          data = internalMarshal(elem, data, true, marshalElementType, false, context)
          i += 1
        }
    }
    data
  }

  private def marshalInt(v: Int, inputData: Data): Data = {
    var data = inputData
    if (data.remainingWriteSize < 4) data = data.writeNext(4)
    val pos = data.endPos
    data(pos + 0) = ((v & 0x000000ff) >>> 0).toByte
    data(pos + 1) = ((v & 0x0000ff00) >>> 8).toByte
    data(pos + 2) = ((v & 0x00ff0000) >>> 16).toByte
    data(pos + 3) = ((v & 0xff000000) >>> 24).toByte
    data.endPos += 4
    data
  }

  private def marshalLong(v: Long, inputData: Data): Data = {
    var data = inputData
    if (data.remainingWriteSize < 8) data = data.writeNext(8)
    val pos = data.endPos
    data(pos + 0) = ((v & 0x00000000000000ffL) >>> 0).toByte
    data(pos + 1) = ((v & 0x000000000000ff00L) >>> 8).toByte
    data(pos + 2) = ((v & 0x0000000000ff0000L) >>> 16).toByte
    data(pos + 3) = ((v & 0x00000000ff000000L) >>> 24).toByte
    data(pos + 4) = ((v & 0x000000ff00000000L) >>> 32).toByte
    data(pos + 5) = ((v & 0x0000ff0000000000L) >>> 40).toByte
    data(pos + 6) = ((v & 0x00ff000000000000L) >>> 48).toByte
    data(pos + 7) = ((v & 0xff00000000000000L) >>> 56).toByte
    data.endPos += 8
    data
  }

  private def marshalDouble(v: Double, inputData: Data): Data = {
    var data = inputData
    val bits = java.lang.Double.doubleToRawLongBits(v)
    if (data.remainingWriteSize < 8) data = data.writeNext(8)
    val pos = data.endPos
    data(pos + 0) = ((bits & 0x00000000000000ffL) >>> 0).toByte
    data(pos + 1) = ((bits & 0x000000000000ff00L) >>> 8).toByte
    data(pos + 2) = ((bits & 0x0000000000ff0000L) >>> 16).toByte
    data(pos + 3) = ((bits & 0x00000000ff000000L) >>> 24).toByte
    data(pos + 4) = ((bits & 0x000000ff00000000L) >>> 32).toByte
    data(pos + 5) = ((bits & 0x0000ff0000000000L) >>> 40).toByte
    data(pos + 6) = ((bits & 0x00ff000000000000L) >>> 48).toByte
    data(pos + 7) = ((bits & 0xff00000000000000L) >>> 56).toByte
    data.endPos += 8
    data
  }

  private def marshalFloat(v: Float, inputData: Data): Data = {
    var data = inputData
    val bits = java.lang.Float.floatToRawIntBits(v)
    if (data.remainingWriteSize < 4) data = data.writeNext(4)
    val pos = data.endPos
    data(pos + 0) = ((bits & 0x000000ff) >>> 0).toByte
    data(pos + 1) = ((bits & 0x0000ff00) >>> 8).toByte
    data(pos + 2) = ((bits & 0x00ff0000) >>> 16).toByte
    data(pos + 3) = ((bits & 0xff000000) >>> 24).toByte
    data.endPos += 4
    data
  }

  private def marshalByte(v: Byte, inputData: Data): Data = {
    var data = inputData
    if (data.remainingWriteSize < 1) data = data.writeNext(1)
    val pos = data.endPos
    data(pos + 0) = v
    data.endPos += 1
    data
  }

  private def marshalBoolean(v: Boolean, inputData: Data): Data = {
    var data = inputData
    if (data.remainingWriteSize < 1) data = data.writeNext(1)
    val pos = data.endPos
    data(pos) = if (v) 1 else 0
    data.endPos += 1
    data
  }

  private def marshalChar(v: Char, inputData: Data): Data = {
    var data = inputData
    if (data.remainingWriteSize < 2) data = data.writeNext(2)
    val pos = data.endPos
    data(pos + 0) = ((v & 0x000000ff) >>> 0).toByte
    data(pos + 1) = ((v & 0x0000ff00) >>> 8).toByte
    data.endPos += 2
    data
  }

  private def marshalShort(v: Short, inputData: Data): Data = {
    var data = inputData
    if (data.remainingWriteSize < 2) data = data.writeNext(2)
    val pos = data.endPos
    data(pos + 0) = ((v & 0x000000ff) >>> 0).toByte
    data(pos + 1) = ((v & 0x0000ff00) >>> 8).toByte
    data.endPos += 2
    data
  }

  private def internalMarshalAs[T](
    classDescriptor: ClassDescriptor, obj: T, inputData: Data, topLevel: Boolean,
    alreadyRecorded: Boolean, ctx: Reactor.MarshalContext
  ): Data = {
    // assert(obj != null)
    var recorded = alreadyRecorded
    if (!topLevel && !recorded) {
      ctx.written.put(obj.asInstanceOf[AnyRef], ctx.createFreshReference())
      recorded = true
    }
    var data = inputData
    val descriptors = classDescriptor.fields
    var i = 0
    while (i < descriptors.length) {
      val descriptor = descriptors(i)
      (descriptor.tag: @switch) match {
        case 0x01 =>
          val v = unsafe.getInt(obj, descriptor.offset)
          data = marshalInt(v, data)
        case 0x02 =>
          val v = unsafe.getLong(obj, descriptor.offset)
          data = marshalLong(v, data)
        case 0x03 =>
          val v = unsafe.getDouble(obj, descriptor.offset)
          data = marshalDouble(v, data)
        case 0x04 =>
          val v = unsafe.getFloat(obj, descriptor.offset)
          data = marshalFloat(v, data)
        case 0x05 =>
          val v = unsafe.getByte(obj, descriptor.offset)
          data = marshalByte(v, data)
        case 0x06 =>
          val v = unsafe.getBoolean(obj, descriptor.offset)
          data = marshalBoolean(v, data)
        case 0x07 =>
          val v = unsafe.getChar(obj, descriptor.offset)
          data = marshalChar(v, data)
        case 0x08 =>
          val v = unsafe.getShort(obj, descriptor.offset)
          data = marshalShort(v, data)
        case 0x0a =>
          val value = unsafe.getObject(obj, descriptor.offset)
          val marshalType = !descriptor.isFinal
          if (!recorded) {
            ctx.written.put(obj.asInstanceOf[AnyRef], ctx.createFreshReference())
            recorded = true
          }
          data = internalMarshal(value, data, true, marshalType, false, ctx)
        case _ =>
          val array = unsafe.getObject(obj, descriptor.offset)
          if (array == null) {
            data = marshalByte(nullTag, data)
          } else {
            if (!recorded) {
              ctx.written.put(obj.asInstanceOf[AnyRef], ctx.createFreshReference())
              recorded = true
            }
            val tpe = descriptor.field.getType
            data = internalMarshalArray(array, tpe, data, ctx)
          }
      }
      i += 1
    }
    data
  }

  def optionallyMarshalType(
    klazz: Class[_], inputData: Data, marshalType: Boolean
  ): Data = {
    var data = inputData
    if (marshalType) {
      val name = klazz.getName
      val typeLength = name.length + 1
      if (typeLength > data.remainingWriteSize) data = data.writeNext(typeLength)
      val pos = data.endPos
      var i = 0
      while (i < name.length) {
        data(pos + i) = name.charAt(i).toByte
        i += 1
      }
      data(pos + i) = classNameTerminatorTag
      data.endPos += typeLength
    } else {
      if (data.remainingWriteSize < 1) data = data.writeNext(-1)
      data(data.endPos) = classNameTerminatorTag
      data.endPos += 1
    }
    data
  }

  private def internalMarshal[T](
    obj: T, inputData: Data, checkRecorded: Boolean, marshalType: Boolean,
    topLevel: Boolean, context: Reactor.MarshalContext
  ): Data = {
    var data = inputData
    if (obj == null) {
      if (data.remainingWriteSize < 1) data = data.writeNext(1)
      data(data.endPos) = nullTag
      data.endPos += 1
      return data
    }
    if (checkRecorded) {
      val ref = context.written.get(obj.asInstanceOf[AnyRef])
      if (ref != context.written.nil) {
        if (data.remainingWriteSize < 5) data = data.writeNext(5)
        val pos = data.endPos
        data(pos + 0) = objectReferenceTag
        data(pos + 1) = ((ref & 0x000000ff) >>> 0).toByte
        data(pos + 2) = ((ref & 0x0000ff00) >>> 8).toByte
        data(pos + 3) = ((ref & 0x00ff0000) >>> 16).toByte
        data(pos + 4) = ((ref & 0xff000000) >>> 24).toByte
        data.endPos += 5
        return data
      }
    }
    val klazz = obj.getClass
    if (klazz.isArray) {
      if (!topLevel || obj.isInstanceOf[Array[AnyRef]]) {
        context.written.put(obj.asInstanceOf[AnyRef], context.createFreshReference())
      }
      data = optionallyMarshalType(klazz, data, marshalType)
      internalMarshalArray(obj.asInstanceOf[AnyRef], klazz, data, context)
    } else {
      data = optionallyMarshalType(klazz, data, marshalType)
      val desc = Platform.Reflect.descriptorOf(klazz)
      internalMarshalAs(desc, obj, data, topLevel, false, context)
    }
  }

  def unmarshal[T](
    buffer: DataBuffer, unmarshalType: Boolean = true
  )(implicit tag: ClassTag[T]): T = {
    val context = Reactor.marshalContext
    val klazz = tag.runtimeClass
    val obj = internalUnmarshal[T](klazz, buffer, unmarshalType, context)
    context.resetUnmarshal()
    obj
  }

  def unmarshalAs[T](
    classDescriptor: ClassDescriptor, obj: T, buffer: DataBuffer,
    context: Reactor.MarshalContext
  )(implicit tag: ClassTag[T]): Unit = {
    internalUnmarshalAs(classDescriptor, obj, buffer, context)
  }

  private def internalUnmarshal[T](
    assumedKlazz: Class[_], buffer: DataBuffer, unmarshalType: Boolean,
    context: Reactor.MarshalContext
  ): T = {
    var data = buffer.input
    var klazz = assumedKlazz
    if (data.remainingReadSize < 1) data = data.readNext()
    val initialByte = data(data.startPos)
    if (initialByte == objectReferenceTag) {
      data.startPos += 1
      var i = 0
      var ref = 0
      while (i < 4) {
        if (data.remainingReadSize == 0) data = data.readNext()
        val b = data(data.startPos)
        ref |= (b.toInt & 0xff) << (8 * i)
        data.startPos += 1
        i += 1
      }
      val obj = context.seen(ref)
      obj.asInstanceOf[T]
    } else if (initialByte == nullTag) {
      data.startPos += 1
      null.asInstanceOf[T]
    } else {
      if (unmarshalType) {
        val stringBuffer = context.stringBuffer
        var last = initialByte
        if (last == classNameTerminatorTag)
          sys.error("Data does not contain a type signature.")
        var i = data.startPos
        var until = data.startPos + data.remainingReadSize
        stringBuffer.setLength(0)
        while (last != classNameTerminatorTag) {
          last = data(i)
          if (last != classNameTerminatorTag && last != arrayTag) {
            stringBuffer.append(last.toChar)
          }
          i += 1
          if (i == until) {
            data.startPos += i - data.startPos
            if (last != classNameTerminatorTag) {
              data = data.readNext()
              i = data.startPos
              until = data.startPos + data.remainingReadSize
            }
          }
        }
        data.startPos += i - data.startPos
        val klazzName = stringBuffer.toString
        klazz = Class.forName(klazzName)
      } else {
        assert(initialByte == classNameTerminatorTag)
        data.startPos += 1
      }
      if (klazz.isArray) {
        unmarshalArray(klazz, buffer, context).asInstanceOf[T]
      } else {
        val obj = unsafe.allocateInstance(klazz)
        context.seen += obj
        val desc = Platform.Reflect.descriptorOf(klazz)
        internalUnmarshalAs(desc, obj, buffer, context)
        obj.asInstanceOf[T]
      }
    }
  }

  def unmarshalArray(
    tpe: Class[_], buffer: DataBuffer, context: MarshalContext
  ): AnyRef = {
    var data = buffer.input
    var array: AnyRef = null
    if (data.remainingReadSize < 1) data = data.readNext()
    val tag = data(data.startPos)
    data.startPos += 1
    if (tag == nullTag) {
      array = null
    } else {
      assert(tag == arrayTag)
      var length = 0
      if (data.remainingReadSize >= 4) {
        val pos = data.startPos
        val b0 = (data(pos + 0).toInt << 0) & 0x000000ff
        val b1 = (data(pos + 1).toInt << 8) & 0x0000ff00
        val b2 = (data(pos + 2).toInt << 16) & 0x00ff0000
        val b3 = (data(pos + 3).toInt << 24) & 0xff000000
        data.startPos = pos + 4
        length = b3 | b2 | b1 | b0
      } else {
        var i = 0
        var x = 0
        while (i < 4) {
          if (data.remainingReadSize == 0) data = data.readNext()
          val b = data(data.startPos)
          x |= (b.toInt & 0xff) << (8 * i)
          data.startPos += 1
          i += 1
        }
        length = x
      }
      array = java.lang.reflect.Array.newInstance(tpe.getComponentType, length)
      context.seen += array
      val elementType = tpe.getComponentType
      elementType match {
        case Platform.Reflect.intClass =>
          val intArray = array.asInstanceOf[Array[Int]]
          var i = 0
          while (i < length) {
            val batchByteSize =
              math.min(data.remainingReadSize / 4 * 4, (length - i) * 4)
            var j = i
            var pos = data.startPos
            while (j < i + batchByteSize / 4) {
              val b0 = (data(pos + 0).toInt << 0) & 0x000000ff
              val b1 = (data(pos + 1).toInt << 8) & 0x0000ff00
              val b2 = (data(pos + 2).toInt << 16) & 0x00ff0000
              val b3 = (data(pos + 3).toInt << 24) & 0xff000000
              val v = b3 | b2 | b1 | b0
              intArray(j) = v
              pos += 4
              j += 1
            }
            i += batchByteSize / 4
            data.startPos += batchByteSize
            if (i < length) {
              var x = 0
              var j = 0
              while (j < 4) {
                if (data.remainingReadSize == 0) data = data.readNext()
                val b = data(data.startPos)
                x |= (b.toInt & 0xff) << (8 * j)
                data.startPos += 1
                j += 1
              }
              intArray(i) = x
              i += 1
            }
          }
        case Platform.Reflect.longClass =>
          val longArray = array.asInstanceOf[Array[Long]]
          var i = 0
          while (i < length) {
            val batchByteSize =
              math.min(data.remainingReadSize / 8 * 8, (length - i) * 8)
            var j = i
            var pos = data.startPos
            while (j < i + batchByteSize / 8) {
              val b0 = (data(pos + 0).toLong << 0) & 0x00000000000000ffL
              val b1 = (data(pos + 1).toLong << 8) & 0x000000000000ff00L
              val b2 = (data(pos + 2).toLong << 16) & 0x0000000000ff0000L
              val b3 = (data(pos + 3).toLong << 24) & 0x00000000ff000000L
              val b4 = (data(pos + 4).toLong << 32) & 0x000000ff00000000L
              val b5 = (data(pos + 5).toLong << 40) & 0x0000ff0000000000L
              val b6 = (data(pos + 6).toLong << 48) & 0x00ff000000000000L
              val b7 = (data(pos + 7).toLong << 56) & 0xff00000000000000L
              val v = b7 | b6 | b5 | b4 | b3 | b2 | b1 | b0
              longArray(j) = v
              pos += 8
              j += 1
            }
            i += batchByteSize / 8
            data.startPos += batchByteSize
            if (i < length) {
              var x = 0L
              var j = 0
              while (j < 8) {
                if (data.remainingReadSize == 0) data = data.readNext()
                val b = data(data.startPos)
                x |= (b.toLong & 0xff) << (8 * j)
                data.startPos += 1
                j += 1
              }
              longArray(i) = x
              i += 1
            }
          }
        case Platform.Reflect.doubleClass =>
          val doubleArray = array.asInstanceOf[Array[Double]]
          var i = 0
          while (i < length) {
            val batchByteSize =
              math.min(data.remainingReadSize / 8 * 8, (length - i) * 8)
            var j = i
            var pos = data.startPos
            while (j < i + batchByteSize / 8) {
              val b0 = (data(pos + 0).toLong << 0) & 0x00000000000000ffL
              val b1 = (data(pos + 1).toLong << 8) & 0x000000000000ff00L
              val b2 = (data(pos + 2).toLong << 16) & 0x0000000000ff0000L
              val b3 = (data(pos + 3).toLong << 24) & 0x00000000ff000000L
              val b4 = (data(pos + 4).toLong << 32) & 0x000000ff00000000L
              val b5 = (data(pos + 5).toLong << 40) & 0x0000ff0000000000L
              val b6 = (data(pos + 6).toLong << 48) & 0x00ff000000000000L
              val b7 = (data(pos + 7).toLong << 56) & 0xff00000000000000L
              val bits = b7 | b6 | b5 | b4 | b3 | b2 | b1 | b0
              val v = java.lang.Double.longBitsToDouble(bits)
              doubleArray(j) = v
              pos += 8
              j += 1
            }
            i += batchByteSize / 8
            data.startPos += batchByteSize
            if (i < length) {
              var bits = 0L
              var j = 0
              while (j < 8) {
                if (data.remainingReadSize == 0) data = data.readNext()
                val b = data(data.startPos)
                bits |= (b.toLong & 0xff) << (8 * j)
                data.startPos += 1
                j += 1
              }
              doubleArray(i) = java.lang.Double.longBitsToDouble(bits)
              i += 1
            }
          }
        case Platform.Reflect.floatClass =>
          val floatArray = array.asInstanceOf[Array[Float]]
          var i = 0
          while (i < length) {
            val batchByteSize =
              math.min(data.remainingReadSize / 4 * 4, (length - i) * 4)
            var j = i
            var pos = data.startPos
            while (j < i + batchByteSize / 4) {
              val b0 = (data(pos + 0).toInt << 0) & 0x000000ff
              val b1 = (data(pos + 1).toInt << 8) & 0x0000ff00
              val b2 = (data(pos + 2).toInt << 16) & 0x00ff0000
              val b3 = (data(pos + 3).toInt << 24) & 0xff000000
              val bits = b3 | b2 | b1 | b0
              val v = java.lang.Float.intBitsToFloat(bits)
              floatArray(j) = v
              pos += 4
              j += 1
            }
            i += batchByteSize / 4
            data.startPos += batchByteSize
            if (i < length) {
              var bits = 0
              var j = 0
              while (j < 4) {
                if (data.remainingReadSize == 0) data = data.readNext()
                val b = data(data.startPos)
                bits |= (b.toInt & 0xff) << (8 * j)
                data.startPos += 1
                j += 1
              }
              floatArray(i) = java.lang.Float.intBitsToFloat(bits)
              i += 1
            }
          }
        case Platform.Reflect.byteClass =>
          val byteArray = array.asInstanceOf[Array[Byte]]
          var i = 0
          while (i < length) {
            if (data.remainingReadSize == 0) data = data.readNext()
            val batchByteSize =
              math.min(data.remainingReadSize / 1 * 1, (length - i) * 1)
            var j = i
            var pos = data.startPos
            while (j < i + batchByteSize / 1) {
              val v = data(pos + 0)
              byteArray(j) = v
              pos += 1
              j += 1
            }
            i += batchByteSize / 1
            data.startPos += batchByteSize
          }
        case Platform.Reflect.booleanClass =>
          val booleanArray = array.asInstanceOf[Array[Boolean]]
          var i = 0
          while (i < length) {
            if (data.remainingReadSize == 0) data = data.readNext()
            val batchByteSize =
              math.min(data.remainingReadSize / 1 * 1, (length - i) * 1)
            var j = i
            var pos = data.startPos
            while (j < i + batchByteSize / 1) {
              val v = data(pos + 0)
              booleanArray(j) = if (v != 0) true else false
              pos += 1
              j += 1
            }
            i += batchByteSize / 1
            data.startPos += batchByteSize
          }
        case Platform.Reflect.charClass =>
          val charArray = array.asInstanceOf[Array[Char]]
          var i = 0
          while (i < length) {
            val batchByteSize =
              math.min(data.remainingReadSize / 2 * 2, (length - i) * 2)
            var j = i
            var pos = data.startPos
            while (j < i + batchByteSize / 2) {
              val b0 = (data(pos + 0).toInt << 0) & 0x000000ff
              val b1 = (data(pos + 1).toInt << 8) & 0x0000ff00
              val v = (b1 | b0).toChar
              charArray(j) = v
              pos += 2
              j += 1
            }
            i += batchByteSize / 2
            data.startPos += batchByteSize
            if (i < length) {
              var v = 0
              var j = 0
              while (j < 2) {
                if (data.remainingReadSize == 0) data = data.readNext()
                val b = data(data.startPos)
                v |= (b.toInt & 0xff) << (8 * j)
                data.startPos += 1
                j += 1
              }
              charArray(i) = v.toChar
              i += 1
            }
          }
        case Platform.Reflect.shortClass =>
          val shortArray = array.asInstanceOf[Array[Short]]
          var i = 0
          while (i < length) {
            val batchByteSize =
              math.min(data.remainingReadSize / 2 * 2, (length - i) * 2)
            var j = i
            var pos = data.startPos
            while (j < i + batchByteSize / 2) {
              val b0 = (data(pos + 0).toInt << 0) & 0x000000ff
              val b1 = (data(pos + 1).toInt << 8) & 0x0000ff00
              val v = (b1 | b0).toShort
              shortArray(j) = v
              pos += 2
              j += 1
            }
            i += batchByteSize / 2
            data.startPos += batchByteSize
            if (i < length) {
              var v = 0
              var j = 0
              while (j < 2) {
                if (data.remainingReadSize == 0) data = data.readNext()
                val b = data(data.startPos)
                v |= (b.toInt & 0xff) << (8 * j)
                data.startPos += 1
                j += 1
              }
              shortArray(i) = v.toShort
              i += 1
            }
          }
        case _ =>
          val objectArray = array.asInstanceOf[Array[AnyRef]]
          var i = 0
          while (i < length) {
            val unmarshalElementType = !Modifier.isFinal(elementType.getModifiers)
            val obj = internalUnmarshal[AnyRef](elementType, buffer,
              unmarshalElementType, context)
            objectArray(i) = obj
            i += 1
          }
          data = buffer.input
      }
    }
    array
  }

  private def internalUnmarshalAs[T](
    classDescriptor: ClassDescriptor, obj: T, buffer: DataBuffer,
    context: Reactor.MarshalContext
  ): Unit = {
    var data = buffer.input
    val descriptors = classDescriptor.fields
    var i = 0
    while (i < descriptors.length) {
      val descriptor = descriptors(i)
      (descriptor.tag: @switch) match {
        case 0x01 =>
          if (data.remainingReadSize >= 4) {
            val pos = data.startPos
            val b0 = (data(pos + 0).toInt << 0) & 0x000000ff
            val b1 = (data(pos + 1).toInt << 8) & 0x0000ff00
            val b2 = (data(pos + 2).toInt << 16) & 0x00ff0000
            val b3 = (data(pos + 3).toInt << 24) & 0xff000000
            val x = b3 | b2 | b1 | b0
            unsafe.putInt(obj, descriptor.offset, x)
            data.startPos = pos + 4
          } else {
            var i = 0
            var x = 0
            while (i < 4) {
              if (data.remainingReadSize == 0) data = data.readNext()
              val b = data(data.startPos)
              x |= (b.toInt & 0xff) << (8 * i)
              data.startPos += 1
              i += 1
            }
            unsafe.putInt(obj, descriptor.offset, x)
          }
        case 0x02 =>
          if (data.remainingReadSize >= 8) {
            val pos = data.startPos
            val b0 = (data(pos + 0).toLong << 0) & 0x00000000000000ffL
            val b1 = (data(pos + 1).toLong << 8) & 0x000000000000ff00L
            val b2 = (data(pos + 2).toLong << 16) & 0x0000000000ff0000L
            val b3 = (data(pos + 3).toLong << 24) & 0x00000000ff000000L
            val b4 = (data(pos + 4).toLong << 32) & 0x000000ff00000000L
            val b5 = (data(pos + 5).toLong << 40) & 0x0000ff0000000000L
            val b6 = (data(pos + 6).toLong << 48) & 0x00ff000000000000L
            val b7 = (data(pos + 7).toLong << 56) & 0xff00000000000000L
            val x = b7 | b6 | b5 | b4 | b3 | b2 | b1 | b0
            unsafe.putLong(obj, descriptor.offset, x)
            data.startPos = pos + 8
          } else {
            var i = 0
            var x = 0L
            while (i < 8) {
              if (data.remainingReadSize == 0) data = data.readNext()
              val b = data(data.startPos)
              x |= (b.toLong & 0xff) << (8 * i)
              data.startPos += 1
              i += 1
            }
            unsafe.putLong(obj, descriptor.offset, x)
          }
        case 0x03 =>
          if (data.remainingReadSize >= 8) {
            val pos = data.startPos
            val b0 = (data(pos + 0).toLong << 0) & 0x00000000000000ffL
            val b1 = (data(pos + 1).toLong << 8) & 0x000000000000ff00L
            val b2 = (data(pos + 2).toLong << 16) & 0x0000000000ff0000L
            val b3 = (data(pos + 3).toLong << 24) & 0x00000000ff000000L
            val b4 = (data(pos + 4).toLong << 32) & 0x000000ff00000000L
            val b5 = (data(pos + 5).toLong << 40) & 0x0000ff0000000000L
            val b6 = (data(pos + 6).toLong << 48) & 0x00ff000000000000L
            val b7 = (data(pos + 7).toLong << 56) & 0xff00000000000000L
            val bits = b7 | b6 | b5 | b4 | b3 | b2 | b1 | b0
            val x = java.lang.Double.longBitsToDouble(bits)
            unsafe.putDouble(obj, descriptor.offset, x)
            data.startPos = pos + 8
          } else {
            var i = 0
            var bits = 0L
            while (i < 8) {
              if (data.remainingReadSize == 0) data = data.readNext()
              val b = data(data.startPos)
              bits |= (b.toLong & 0xff) << (8 * i)
              data.startPos += 1
              i += 1
            }
            val x = java.lang.Double.longBitsToDouble(bits)
            unsafe.putDouble(obj, descriptor.offset, x)
          }
        case 0x04 =>
          if (data.remainingReadSize >= 4) {
            val pos = data.startPos
            val b0 = (data(pos + 0).toInt << 0) & 0x000000ff
            val b1 = (data(pos + 1).toInt << 8) & 0x0000ff00
            val b2 = (data(pos + 2).toInt << 16) & 0x00ff0000
            val b3 = (data(pos + 3).toInt << 24) & 0xff000000
            val bits = b3 | b2 | b1 | b0
            val x = java.lang.Float.intBitsToFloat(bits)
            unsafe.putFloat(obj, descriptor.offset, x)
            data.startPos = pos + 4
          } else {
            var i = 0
            var bits = 0
            while (i < 4) {
              if (data.remainingReadSize == 0) data = data.readNext()
              val b = data(data.startPos)
              bits |= (b.toInt & 0xff) << (8 * i)
              data.startPos += 1
              i += 1
            }
            val x = java.lang.Float.intBitsToFloat(bits)
            unsafe.putFloat(obj, descriptor.offset, x)
          }
        case 0x05 =>
          if (data.remainingReadSize < 1) data = data.readNext()
          val pos = data.startPos
          val b = data(pos)
          unsafe.putByte(obj, descriptor.offset, b)
          data.startPos = pos + 1
        case 0x06 =>
          if (data.remainingReadSize < 1) data = data.readNext()
          val pos = data.startPos
          val b = data(pos)
          unsafe.putBoolean(obj, descriptor.offset, if (b != 0) true else false)
          data.startPos = pos + 1
        case 0x07 =>
          if (data.remainingReadSize >= 2) {
            val pos = data.startPos
            val b0 = (data(pos + 0).toChar << 0) & 0x000000ff
            val b1 = (data(pos + 1).toChar << 8) & 0x0000ff00
            unsafe.putChar(obj, descriptor.offset, (b1 | b0).toChar)
            data.startPos = pos + 2
          } else {
            var i = 0
            var x = 0
            while (i < 2) {
              if (data.remainingReadSize == 0) data = data.readNext()
              val b = data(data.startPos)
              x |= (b.toInt & 0xff) << (8 * i)
              data.startPos += 1
              i += 1
            }
            unsafe.putChar(obj, descriptor.offset, x.toChar)
          }
        case 0x08 =>
          if (data.remainingReadSize >= 2) {
            val pos = data.startPos
            val b0 = (data(pos + 0).toShort << 0) & 0x000000ff
            val b1 = (data(pos + 1).toShort << 8) & 0x0000ff00
            unsafe.putShort(obj, descriptor.offset, (b1 | b0).toShort)
            data.startPos = pos + 2
          } else {
            var i = 0
            var x = 0
            while (i < 2) {
              if (data.remainingReadSize == 0) data = data.readNext()
              val b = data(data.startPos)
              x |= (b.toInt & 0xff) << (8 * i)
              data.startPos += 1
              i += 1
            }
            unsafe.putShort(obj, descriptor.offset, x.toShort)
          }
        case 0x0a =>
          val unmarshalType = !descriptor.isFinal
          val tpe = descriptor.field.getType
          val x = internalUnmarshal[AnyRef](tpe, buffer, unmarshalType, context)
          data = buffer.input
          unsafe.putObject(obj, descriptor.offset, x)
        case _ =>
          val tpe = descriptor.field.getType
          val array = unmarshalArray(tpe, buffer, context)
          data = buffer.input
          unsafe.putObject(obj, descriptor.offset, array)
      }
      i += 1
    }
  }
}
