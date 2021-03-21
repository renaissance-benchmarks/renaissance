package io.reactors



import io.reactors.common.BloomMap
import io.reactors.marshal.ClassDescriptor
import scala.collection._
import scala.scalajs.reflect.InstantiatableClass
import scala.scalajs.reflect.InvokableConstructor
import scala.scalajs.reflect.annotation.EnableReflectiveInstantiation
import scala.util.parsing.combinator._



object Platform {

  private[reactors] object HoconParser extends JavaTokenParsers {
    def configuration: Parser[Map[String, Any]] = rep(tuple) ^^ {
      case s: Seq[Map[String, Any]] @unchecked => s.foldLeft(Map[String, Any]())(_ ++ _)
    }
    def tuple: Parser[Map[String, Any]] = keyName ~ "=" ~ value ^^ {
      case name ~ _ ~ (dict: Map[String, Any] @unchecked) =>
        for ((k, v) <- dict) yield (s"$name.$k", v)
      case name ~ _ ~ v =>
        Map(name -> v)
    }
    def keyName = regex("[a-zA-Z][a-zA-Z0-9_\\-]*".r)
    def value: Parser[Any] = string | double | int | list | dictionary
    def string: Parser[String] =
      "\"" ~ regex("[ -!#-~]*".r) ~ "\"" ^^ {
        case _ ~ content ~ _ => content
      }
    def int: Parser[Int] = wholeNumber ^^ { _.toInt }
    def double: Parser[Double] = decimalNumber ^^ { _.toDouble }
    def list: Parser[Seq[Any]] = "[" ~ repsep(value, ",") ~ "]" ^^ {
      case _ ~ values ~ _ => values
    }
    def dictionary: Parser[Map[String, Any]] = "{" ~ configuration ~ "}" ^^ {
      case _ ~ config ~ _ => config
    }

    def simpleParse(s: String): Map[String, Any] = {
      parseAll(configuration, s.trim) match {
        case Success(m, _) => m
        case _ => sys.error(s"Cannot parse '$s'.")
      }
    }
  }

  private[reactors] class SimpleConfiguration(val paths: Map[String, Any])
  extends Configuration {
    def int(path: String): Int = paths(path).asInstanceOf[Int]
    def string(path: String): String = paths(path).asInstanceOf[String]
    def double(path: String): Double = paths(path).asInstanceOf[Double]
    def list(path: String): Seq[Configuration] = {
      val values = paths(path).asInstanceOf[Seq[Map[String, Any]]]
      values.map(v => new SimpleConfiguration(v))
    }
    def children(path: String): Seq[Configuration] = {
      val prefix = path + "."
      def isDict(p: String): Boolean = {
        p.startsWith(prefix) && p.substring(prefix.length).indexOf('.') != -1
      }
      paths.toSeq.collect {
        case (p, obj) if isDict(p) =>
          val parts = p.substring(prefix.length).split("\\.")
          val group = parts(0)
          val nkey = parts(1)
          (group, (nkey, obj))
      }.groupBy { case (p, _) => p }.toMap.map {
        case (group, elems) =>
          (group, elems.map { case (_, (nkey, obj)) => (nkey, obj) }.toMap)
      }.values.toList.map(m => new SimpleConfiguration(m))
    }
    def withFallback(other: Configuration): Configuration = {
      val newPaths = mutable.Map[String, Any](paths.toSeq: _*)
      for ((p, obj) <- other.asInstanceOf[SimpleConfiguration].paths) {
        if (!newPaths.contains(p)) newPaths(p) = obj
      }
      new SimpleConfiguration(newPaths)
    }
  }

  private val classCache = new BloomMap[Class[_], ClassDescriptor]

  private[reactors] val configurationFactory = new Configuration.Factory {
    def parse(s: String) = new SimpleConfiguration(HoconParser.simpleParse(s))
    def empty = new SimpleConfiguration(Map())
  }

  private[reactors] val machineConfiguration = s"""
    system = {
      num-processors = ${1}
    }
  """

  private[reactors] val defaultConfiguration = """
    debug-level = 0
    pickler = "io.reactors.pickle.NoPickler"
    remote = {
      default-schema = "local"
      transports = [
        {
          schema = "datagram"
          transport = "io.reactors.remote.NodeJSDatagramTransport"
          host = "localhost"
          port = 17771
        }
      ]
    }
    debug-api = {
      name = "io.reactors.debugger.ZeroDebugApi"
    }
    error-handler = {
      name = "io.reactors.DefaultErrorHandler"
    }
    scheduler = {
      lagging = {
        enabled = 0
      }
      default = {
        budget = 50
        postschedule-count = 0
      }
    }
    system = {
      net = {
        parallelism = 1
      }
    }
  """

  private[reactors] def registerDefaultSchedulers(b: ReactorSystem.Bundle): Unit = {
    b.registerScheduler(JsScheduler.Key.default, JsScheduler.default)
  }

  private[reactors] lazy val defaultScheduler = JsScheduler.default

  private[reactors] def inetAddress(host: String, port: Int) = ???

  private[reactors] object Reflect {
    def instantiate[T](clazz: Class[T], args: Seq[Any]): T = {
      instantiate(clazz.getName, args)
    }

    def instantiate[T](className: String, args: Seq[Any]): T = {
      val reflect = scala.scalajs.reflect.Reflect
      val cls = reflect.lookupInstantiatableClass(className).get
      val ctor = matchingConstructor(cls, args)
      ctor.newInstance(args: _*).asInstanceOf[T]
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

    private def matchingConstructor[T](
      cls: InstantiatableClass, args: Seq[Any]
    ): InvokableConstructor = {
      if (args.isEmpty) cls.getConstructor().get
      else {
        def matches(c: InvokableConstructor): Boolean = {
          val cargs = c.parameterTypes
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
        val cs = cls.declaredConstructors.filter(matches)
        if (cs.length == 0) exception.illegalArg(s"No match for $cls and $args.")
        else if (cs.length > 1) {
          exception.illegalArg(s"Multiple matches for $cls and $args.")
        } else cs.head
      }
    }

    private def computeFieldsOf(klazz: Class[_]) = ???

    def descriptorOf(klazz: Class[_]): ClassDescriptor = {
      var desc = classCache.get(klazz)
      if (desc == null) {
        desc = computeFieldsOf(klazz)
        classCache.put(klazz, desc)
      }
      desc
    }
  }

  @EnableReflectiveInstantiation
  trait Reflectable {
  }

  private[reactors] class SnapshotMap[K, V] extends mutable.HashMap[K, V] {
    def replace(k: K, ov: V, nv: V): Boolean = this.get(k) match {
      case Some(v) if v == ov =>
        this(k) = nv
        true
      case _ =>
        false
    }

    def putIfAbsent(k: K, v: V): Option[V] = this.get(k) match {
      case Some(ov) =>
        Some(ov)
      case None =>
        this(k) = v
        None
    }

    def snapshot: Map[K, V] = {
      val m = mutable.Map[K, V]()
      for ((k, v) <- this) m(k) = v
      m
    }
  }

  private[reactors] def newSnapshotMap[K, V] = new SnapshotMap[K, V]

}
