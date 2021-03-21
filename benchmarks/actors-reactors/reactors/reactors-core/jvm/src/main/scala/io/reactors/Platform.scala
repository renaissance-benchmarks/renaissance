package io.reactors



import com.typesafe.config._
import java.net.InetSocketAddress
import java.lang.reflect._
import java.util.Arrays
import java.util.Comparator
import io.reactors.common.BloomMap
import io.reactors.marshal.ClassDescriptor
import io.reactors.marshal.Marshalable
import io.reactors.marshal.Marshalee
import scala.collection._
import scala.collection.JavaConverters._
import scala.collection.concurrent.TrieMap



object Platform {
  class HoconConfiguration(val config: Config) extends Configuration {
    def int(path: String): Int = config.getInt(path)
    def string(path: String): String = config.getString(path)
    def double(path: String): Double = config.getDouble(path)
    def list(path: String): Seq[Configuration] = {
      val elems = config.getObjectList(path).iterator().asScala.toSeq
      elems.map(c => new HoconConfiguration(c.toConfig))
    }
    def children(path: String): Seq[Configuration] = {
      config.getConfig("remote").root.values.asScala.collect {
        case c: ConfigObject => c.toConfig
      }.map(c => new HoconConfiguration(c)).toSeq
    }
    def withFallback(other: Configuration): Configuration = {
      new HoconConfiguration(this.config.withFallback(
        other.asInstanceOf[HoconConfiguration].config))
    }
  }

  private[reactors] val configurationFactory = new Configuration.Factory {
    def parse(s: String) = new HoconConfiguration(ConfigFactory.parseString(s))
    def empty = new HoconConfiguration(ConfigFactory.empty)
  }

  private[reactors] val machineConfiguration = s"""
    system = {
      num-processors = ${Runtime.getRuntime.availableProcessors}
    }
  """

  private[reactors] val defaultConfiguration = """
    debug-level = 0
    pickler = "io.reactors.pickle.JavaSerializationPickler"
    remote = {
      default-schema = "local"
      transports = [
        {
          schema = "udp"
          transport = "io.reactors.remote.UdpTransport"
          host = "localhost"
          port = 0
        }
        {
          schema = "tcp"
          transport = "io.reactors.remote.TcpTransport"
          host = "localhost"
          port = 0
        }
      ]
    }
    transport = {
      tcp = {
        data-chunk-pool = {
          parallelism = 8
        }
      }
    }
    debug-api = {
      name = "io.reactors.debugger.ZeroDebugApi"
      port = 9500
      repl = {
        expiration = 120
        expiration-check-period = 60
      }
      session = {
        expiration = 240
        expiration-check-period = 150
      }
      delta-debugger = {
        window-size = 1024
      }
    }
    error-handler = {
      name = "io.reactors.DefaultErrorHandler"
    }
    scheduler = {
      lagging = {
        enabled = 1
      }
      default = {
        budget = 64
        postschedule-count = 100
      }
    }
    system = {
      net = {
        parallelism = 8
      }
    }
  """

  private[reactors] def registerDefaultSchedulers(b: ReactorSystem.Bundle): Unit = {
    b.registerScheduler(JvmScheduler.Key.globalExecutionContext,
      JvmScheduler.globalExecutionContext)
    b.registerScheduler(JvmScheduler.Key.default, JvmScheduler.default)
    b.registerScheduler(JvmScheduler.Key.newThread, JvmScheduler.newThread)
    b.registerScheduler(JvmScheduler.Key.piggyback, JvmScheduler.piggyback)
  }

  private[reactors] lazy val defaultScheduler = JvmScheduler.default

  private[reactors] def inetAddress(host: String, port: Int) =
    new InetSocketAddress(host, port)

  private[reactors] object Reflect {
    private val monitor = new AnyRef
    private val classCache = new BloomMap[Class[_], ClassDescriptor]
    private val fieldComparator = new Comparator[FieldDescriptor] {
      def compare(x: FieldDescriptor, y: FieldDescriptor): Int =
        x.field.toString.compareTo(y.field.toString)
    }
    private val isMarshalableField: Field => Boolean = f => {
      !Modifier.isTransient(f.getModifiers) && !Modifier.isStatic(f.getModifiers)
    }
    val booleanClass = classOf[Boolean]
    val byteClass = classOf[Byte]
    val shortClass = classOf[Short]
    val charClass = classOf[Char]
    val intClass = classOf[Int]
    val floatClass = classOf[Float]
    val longClass = classOf[Long]
    val doubleClass = classOf[Double]

    private def canBeMarshaled(cls: Class[_]): Boolean = {
      val isOk =
        classOf[Marshalee].isAssignableFrom(cls) ||
          classOf[Marshalable].isAssignableFrom(cls) ||
          classOf[java.io.Serializable].isAssignableFrom(cls) ||
          cls.isPrimitive ||
          cls.isArray
      isOk
    }

    private def computeFieldsOf(klazz: Class[_]): ClassDescriptor =
      monitor.synchronized {
        if (!canBeMarshaled(klazz)) {
          throw new IllegalArgumentException(s"Class $klazz cannot be marshaled")
        }
        val fields = mutable.ArrayBuffer[Field]()
        var ancestor = klazz
        while (ancestor != null) {
          val marshalableFields = ancestor.getDeclaredFields.filter(isMarshalableField)
          for (field <- marshalableFields) {
            field.setAccessible(true)
          }
          fields ++= marshalableFields
          ancestor = ancestor.getSuperclass
        }
        val fieldDescriptors = fields.map(f => {
          new Platform.Reflect.FieldDescriptor(f)
        }).toArray
        Arrays.sort(fieldDescriptors, fieldComparator)
        new ClassDescriptor(klazz, fieldDescriptors)
      }

    def descriptorOf(klazz: Class[_]): ClassDescriptor = {
      var desc = classCache.get(klazz)
      if (desc == null) {
        desc = computeFieldsOf(klazz)
        classCache.put(klazz, desc)
      }
      desc
    }

    def instantiate[T](clazz: Class[T], args: scala.Array[Any]): T = {
      // Java-only version.
      instantiate(clazz, args.toSeq)
    }

    def instantiate[T](clazz: Class[T], args: Seq[Any]): T = {
      val ctor = matchingConstructor(clazz, args)
      ctor.setAccessible(true)
      ctor.newInstance(args.asInstanceOf[Seq[AnyRef]]: _*)
    }

    def instantiate[T](name: String, args: Seq[Any]): T = {
      val clazz = Class.forName(name).asInstanceOf[Class[T]]
      instantiate(clazz, args)
    }

    private def matchingConstructor[T](
      cls: Class[T], args: Seq[Any]
    ): Constructor[T] = try {
      if (args.isEmpty) cls.getDeclaredConstructor()
      else {
        def matches(c: Constructor[_]): Boolean = {
          val cargs = c.getParameterTypes
          cargs.length == args.length && {
            val cit = cargs.iterator
            val pit = args.iterator
            while (cit.hasNext) {
              val cls = cit.next()
              val obj = pit.next()
              if (
                !cls.isInstance(obj) &&
                !boxedVersion(cls).isInstance(obj) &&
                !(obj == null && !cls.isPrimitive)
              ) return false
            }
            true
          }
        }
        val cs = cls.getDeclaredConstructors.filter(matches)
        if (cs.length == 0) exception.illegalArg(s"No match for $cls and $args.")
        else if (cs.length > 1)
          exception.illegalArg(s"Multiple matches for $cls and $args.")
        else cs.head.asInstanceOf[Constructor[T]]
      }
    } catch {
      case e: Exception =>
        throw new IllegalArgumentException(s"Could not find constructor for $cls.", e)
    }

    private val boxedMapping = Map[Class[_], Class[_]](
      classOf[Boolean] -> classOf[java.lang.Boolean],
      classOf[Byte] -> classOf[java.lang.Byte],
      classOf[Char] -> classOf[java.lang.Character],
      classOf[Short] -> classOf[java.lang.Short],
      classOf[Int] -> classOf[java.lang.Integer],
      classOf[Long] -> classOf[java.lang.Long],
      classOf[Float] -> classOf[java.lang.Float],
      classOf[Double] -> classOf[java.lang.Double]
    )

    private def boxedVersion(cls: Class[_]) =
      if (!cls.isPrimitive) cls else boxedMapping(cls)

    class FieldDescriptor(val field: Field) {
      val offset =
        io.reactors.common.concurrent.Platform.unsafe.objectFieldOffset(field)
      val isFinal = Modifier.isFinal(field.getType.getModifiers)
      val tag = {
        val tpe = field.getType
        val tagMask = {
          if (tpe.isPrimitive) {
            tpe match {
              case Platform.Reflect.intClass =>
                0x01
              case Platform.Reflect.longClass =>
                0x02
              case Platform.Reflect.doubleClass =>
                0x03
              case Platform.Reflect.floatClass =>
                0x04
              case Platform.Reflect.byteClass =>
                0x05
              case Platform.Reflect.booleanClass =>
                0x06
              case Platform.Reflect.charClass =>
                0x07
              case Platform.Reflect.shortClass =>
                0x08
            }
          } else if (tpe.isArray) {
            val ctpe = tpe.getComponentType
            tpe match {
              case Platform.Reflect.intClass =>
                0x11
              case Platform.Reflect.longClass =>
                0x12
              case Platform.Reflect.doubleClass =>
                0x13
              case Platform.Reflect.floatClass =>
                0x14
              case Platform.Reflect.byteClass =>
                0x15
              case Platform.Reflect.booleanClass =>
                0x16
              case Platform.Reflect.charClass =>
                0x17
              case Platform.Reflect.shortClass =>
                0x18
              case _ =>
                0x1a
            }
          } else {
            0x0a
          }
        }
        tagMask
      }
    }
  }

  private[reactors] def javaReflect = Reflect

  private[reactors] trait Reflectable

  private[reactors] def newSnapshotMap[K, V] = new TrieMap[K, V]

}
