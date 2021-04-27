package io.reactors



import org.apache.commons.lang3.StringEscapeUtils
import scalajson.ast._



package object json {
  implicit class StringJsonInterpolationOps(val ctx: StringContext) {
    def json(args: Any*): JValue = {
      var content = ""
      for ((part, arg) <- ctx.parts.zip(args)) {
        content += part
        def appendValue(x: Any) {
          x match {
            case b: Boolean =>
              content += b
            case n: Number =>
              content += n
            case xs: Array[t] =>
              content += "["
              if (xs.nonEmpty) {
                for (x <- xs.init) {
                  appendValue(x)
                  content += ","
                }
                appendValue(xs.last)
              }
              content += "]"
            case xs: Map[k, v] =>
              content += "{"
              if (xs.nonEmpty) {
                for ((key, value) <- xs.init) {
                  content += s""""${key}": """
                  appendValue(value)
                  content += ","
                }
                val (lastKey, lastValue) = xs.last
                content += s""""${lastKey}": """
                appendValue(lastValue)
              }
              content += "}"
            case xs: Traversable[t] =>
              content += "["
              if (xs.nonEmpty) {
                for (x <- xs.init) {
                  appendValue(x)
                  content += ","
                }
                appendValue(xs.last)
              }
              content += "]"
            case Some(v) =>
              appendValue(v)
            case null =>
              content += "null"
            case None =>
              content += "null"
            case jv: JValue =>
              content += jv.jsonString
            case _ =>
              content += s""""${x.toString}""""
          }
        }
        appendValue(arg)
      }
      content += ctx.parts.last

      JsonParser.parse(content)
    }
  }

  implicit class JsonOps(val jv: JValue) {
    def jsonString: String = jv match {
      case JNull => "null"
      case JString(s) => s""""${s}""""
      case JNumber(num) => num
      case JTrue => "true"
      case JFalse => "false"
      case JArray(xs) => s"[${xs.map(_.jsonString).mkString(", ")}]"
      case JObject(xs) => {
        val strings = for ((k, v) <- xs) yield s""""${k}": ${v.jsonString}"""
        s"{ ${strings.mkString(", ")} }"
      }
    }

    def asJObject: JObject = jv match {
      case x @ JObject(_) => x
      case _ => sys.error("Not an instance of JObject.")
    }

    def asString: String = jv match {
      case JString(s) => s
      case _ => sys.error("Not an instance of JString.")
    }

    def asLong: Long = jv match {
      case JNumber(num) => java.lang.Long.parseLong(num)
      case _ => sys.error("Not an instance of JNumber.")
    }

    def asList[T](convert: JValue => T): List[T] = jv match {
      case JArray(xs) => xs.map(convert).toList
      case _ => sys.error("Not an instance of JArray.")
    }

    def ++(that: JObject): JObject = {
      val self = asJObject
      JObject(self.value ++ that.value)
    }
  }

  object JsonParser {
    def parse(s: String): JValue = {
      val jackson = org.json4s.jackson.JsonMethods.parse(s)
      def convert(jv: org.json4s.JValue): JValue = jv match {
        case org.json4s.JNull => JNull
        case org.json4s.JString(s) => JString(s)
        case org.json4s.JDouble(num) => JNumber(num)
        case org.json4s.JDecimal(num) => JNumber(num)
        case org.json4s.JInt(num) => JNumber(num)
        case org.json4s.JLong(num) => JNumber(num)
        case org.json4s.JBool(true) => JTrue
        case org.json4s.JBool(false) => JFalse
        case org.json4s.JArray(xs) =>
          val values = for (x <- xs) yield convert(x)
          JArray(values.toVector)
        case org.json4s.JObject(xs) =>
          val fields = for ((k, v) <- xs) yield (k, convert(v))
          JObject(fields.toMap)
        case _ => ???
      }
      convert(jackson)
    }
  }
}
