package io.reactors
package debugger



import _root_.com.github.mustachejava._
import io.reactors.http._
import io.reactors.json._
import io.reactors.protocol._
import java.io.BufferedReader
import java.io.StringReader
import java.io.StringWriter
import java.util.ArrayList
import java.util.HashMap
import java.util.regex._
import io.reactors.http.Http.Request.Wrapper
import org.apache.commons.io.IOUtils
import org.rapidoid.http.Req
import scala.collection._
import scala.collection.JavaConverters._
import scala.concurrent._
import scala.concurrent.ExecutionContext.Implicits.global
import scala.concurrent.duration._



class WebServer(webapi: WebApi) extends Reactor[WebServer.Command] {
  val http = WebServer.createServer(system, webapi)

  def shutdown() {
    http.shutdown()
  }
}


object WebServer {
  sealed trait Command

  case object Shutdown extends Command

  private[debugger] def createServer(
    system: ReactorSystem, webapi: WebApi
  ): Http.Adapter = {
    val port = system.bundle.config.int("debug-api.port")

    def loadPage(path: String): String = {
      sealed trait NodeType
      case object Com extends NodeType
      case object Lib extends NodeType
      case object Style extends NodeType
      case object Page extends NodeType

      class Node(val path: String, val nodeType: NodeType, var content: String = "") {
        val deps = mutable.LinkedHashMap[String, Node]()
      }

      val libPattern = Pattern.compile("\\s*@@library\\((?<path>.*)\\)")
      val stylePattern = Pattern.compile("\\s*@@style\\((?<path>.*)\\)")
      val componentPattern = Pattern.compile("\\s*@@component\\((?<path>.*)\\)")
      val seen = mutable.Map[String, Node]()

      def add(n: Node): Node = {
        seen(n.path) = n
        n
      }

      def interpolate(n: Node): String = {
        val scopes = new HashMap[String, Object]
        scopes.put("reactor-system.url",
          s"${system.bundle.urlMap("udp").url.host}:$port")
        scopes.put("reactor-system.version", "0.7")
        scopes.put("debugger-ui.configuration", "{}")
        scopes.put("debugger-ui.plugins", "<!-- No plugins -->")
        val imports = {
          val sb = new StringBuffer
          def traverse(n: Node): Unit = if (seen.contains(n.path)) {
            seen.remove(n.path)
            for ((path, d) <- n.deps) {
              traverse(d)
            }
            sb.append("\n\n")
            n.nodeType match {
              case Style =>
                sb.append("<style>\n")
                sb.append(n.content)
                sb.append("\n</style>\n")
              case Lib =>
                sb.append("<script type='text/javascript'>\n")
                sb.append(n.content)
                sb.append("\n</script>\n")
              case Com =>
                sb.append(n.content)
              case Page =>
            }
            sb.append("\n\n")
          }
          traverse(n)
          sb.toString
        }
        scopes.put("debugger-ui.imports", imports)

        val writer = new StringWriter
        val mf = new DefaultMustacheFactory()
        val mustache =
          mf.compile(new StringReader(n.content), s"${system.name}.template")
        mustache.execute(writer, scopes)
        writer.toString
      }

      def loadPage(path: String): Node = {
        def loadString(path: String) = {
          val stream = getClass.getResourceAsStream("/" + path)
          if (stream == null) sys.error(s"Cannot find path: $path")
          IOUtils.toString(stream, "UTF-8")
        }

        def absorbImports(n: Node, raw: String): String = {
          val reader = new BufferedReader(new StringReader(raw))
          val sb = new StringBuffer

          var line: String = null
          while ({ line = reader.readLine(); line != null }) {
            def path(p: Pattern, txt: String): String = {
              val m = p.matcher(txt)
              if (m.matches()) m.group("path") else null
            }

            val stylepath = path(stylePattern, line)
            if (stylepath != null) {
              n.deps(stylepath) = loadStyle(stylepath)
            }

            val libpath = path(libPattern, line)
            if (libpath != null) {
              n.deps(libpath) = loadLibrary(libpath)
            }

            val compath = path(componentPattern, line)
            if (compath != null) {
              n.deps(compath) = loadCom(compath)
            }

            if (libpath == null && stylepath == null && compath == null) {
              sb.append(line).append("\n")
            }
          }

          sb.toString
        }

        def loadLibrary(path: String): Node =
          if (seen.contains(path)) seen(path)
          else add(new Node(path, Lib, loadString(path)))

        def loadStyle(path: String): Node =
          if (seen.contains(path)) seen(path) else {
            val style = add(new Node(path, Style))
            val raw = loadString(path)
            style.content = absorbImports(style, raw)
            style
          }

        def loadCom(path: String, t: NodeType = Com): Node =
          if (seen.contains(path)) seen(path) else {
            val com = add(new Node(path, t))
            val raw = loadString(path)
            com.content = absorbImports(com, raw)
            com
          }

        loadCom(path, Page)
      }

      interpolate(loadPage(path))
    }

    val debuggerPage = loadPage("io/reactors/debugger/index.html")
    val s = system.service[Http].seq(port)

    // worker pool
    val workerProto = Reactor[Http.Request] { self =>
      self.main.events onEvent { req =>
        val stream = getClass.getResourceAsStream("/io/reactors/debugger/" + req.path)
        if (stream == null) sys.error(s"Cannot find path: ${req.path}")
        if (req.path.endsWith(".svg")) {
          req.respond("text/plain", IOUtils.toString(stream))
        } else {
          req.respond("application/octet-stream", stream)
        }
      }
    }
    val workers = for (i <- 0 until 16) yield {
      system.spawn(workerProto
        .withScheduler(JvmScheduler.Key.newThread)
        .withName(s"~debugger/http-worker-$i"))
    }
    val workChannel = system.channels.router[Http.Request]
      .route(Router.roundRobin(workers))

    // ui routes
    s.html("/") { req =>
      Events(debuggerPage)
    }
    s.async { req =>
      workChannel.channel ! req
    }

    // api routes
    s.json("/api/state") { req =>
      val values = req.posted
      val suid = values("suid").asInstanceOf[String]
      val ts = values("timestamp").asInstanceOf[Number].longValue
      val repluids = values("repluids").asInstanceOf[ArrayList[String]].asScala
      Events(webapi.state(suid, ts, repluids.toList).jsonString)
    }
    s.json("/api/breakpoint/add") { req =>
      val values = req.posted
      val suid = values("suid").asInstanceOf[String]
      val ts = values("pattern").asInstanceOf[String]
      val tpe = values("tpe").asInstanceOf[String]
      ???
    }
    s.json("/api/breakpoint/list") { req =>
      val values = req.posted
      val suid = values("suid").asInstanceOf[String]
      ???
    }
    s.json("/api/breakpoint/remove") { req =>
      val values = req.posted
      val suid = values("suid").asInstanceOf[String]
      val bid = values("bid").asInstanceOf[Number].longValue
      ???
    }
    s.json("/api/repl/get") { req =>
      val values = req.posted
      val tpe = values("tpe").asInstanceOf[String]
      val result = webapi.replGet(tpe)
      result.map(_.jsonString).toIVar
    }
    s.json("/api/repl/eval") { req =>
      val values = req.posted
      val repluid = values("repluid").asInstanceOf[String]
      val command = values("cmd").asInstanceOf[String]
      val result = webapi.replEval(repluid, command)
      result.map(_.jsonString).toIVar
    }
    s.json("/api/repl/close") { req =>
      val values = req.posted
      val repluid = values("repluid").asInstanceOf[String]
      val result = webapi.replClose(repluid)
      result.map(_.jsonString).toIVar
    }

    s
  }
}
