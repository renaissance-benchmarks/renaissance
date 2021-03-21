package io.reactors
package http



import io.reactors.json._
import java.io._
import org.apache.commons.io.IOUtils
import org.rapidoid.http._
import org.rapidoid.setup._
import scala.collection._
import scala.collection.JavaConverters._
import scalajson.ast._



class Http(val system: ReactorSystem) extends Protocol.Service {
  private val servers = mutable.Map[Int, Http.Instance]()
  private val debugMode = system.bundle.config.int("debug-level")

  private def getOrCreateServer(
    port: Int
  ): Http.Instance = servers.synchronized {
    if (!servers.contains(port)) {
      val reactorUid = Reactor.self.uid
      val instance = new Http.Instance(port, reactorUid, debugMode)
      Reactor.self.sysEvents onMatch {
        case ReactorTerminated => instance.shutdown()
      }
      servers(port) = instance
    }
    servers(port)
  }

  def seq(port: Int): Http.Adapter = getOrCreateAdapter(port)

  private[reactors] def getOrCreateAdapter(port: Int): Http.Adapter = {
    val adapter = getOrCreateServer(port)
    if (Reactor.self.uid != adapter.reactorUid)
      sys.error("Server already at $port, and owned by reactor ${adapter.reactorUid}.")
    adapter
  }

  def shutdown() {
    servers.synchronized {
      for ((port, server) <- servers) {
        server.shutdown()
      }
    }
  }
}


object Http {
  sealed trait Method
  case object Get extends Method
  case object Put extends Method

  trait Request {
    def headers: Map[String, String]
    def parameters: Map[String, String]
    def method: Method
    def path: String
    def posted: Map[String, AnyRef]
    def respond(mime: String, content: Any): Unit
  }

  object Request {
    private[reactors] class Wrapper(val req: Req) extends Request {
      def headers = req.headers.asScala
      def parameters = req.params.asScala
      def method = req.verb match {
        case "GET" => Get
        case "PUT" => Put
        case _ => sys.error(s"Method ${req.verb} is not supported.")
      }
      def path = req.path
      def posted = req.posted.asScala
      def respond(mime: String, content: Any): Unit = {
        req.response.contentType(MediaType.of(mime)).result(content)
        req.done()
      }
      override def toString = s"Wrapper($req)"
    }
  }

  trait Adapter {
    def text(route: String)(handler: Request => Events[String]): Unit
    def html(route: String)(handler: Request => Events[String]): Unit
    def json(route: String)(handler: Request => Events[String]): Unit
    def resource(route: String)(mime: String)(
      handler: Request => Events[InputStream]
    ): Unit
    def default(handler: Request => (String, Any)): Unit
    def async(handler: Request => Unit): Unit
    def shutdown(): Unit
  }

  implicit class handler1(f: Req => Object) extends ReqHandler {
    def execute(x: Req): Object = f(x)
  }

  private[reactors] class Instance (
    val port: Int,
    val reactorUid: Long,
    val debugMode: Int
  ) extends Adapter {
    private val setup = Setup.create(Reactor.self.system.name)
    private val handlers = mutable.Map[String, Req => Unit]()
    private val defaultHandlerKey = "#"
    private val requestChannel = {
      val system = Reactor.self.system
      val requests = system.channels.daemon.open[Req]
      requests.events.onEvent(req => serve(req))
      requests.channel
    }

    handlers(defaultHandlerKey) = defaultHandler
    setup.port(port)
    setup.req((req: Req) => {
      req.async()
      requestChannel ! req
      req
    })

    private def defaultHandler(req: Req): Any = {
      val content = """
      <html>
      <head><title>HTTP 404 Not Found</title>
        <meta http-equiv="Content-Type" content="text/html; charset=iso-8859-1">
        <meta name="description" content="Error 404 File not found">
      </head>
      <body>
        <h1>Requested resource not found.</h1>
      </body>
      </html>
      """
      content
    }

    private def serve(req: Req): Unit = {
      val route = req.uri
      val handler = handlers.synchronized {
        handlers.get(route) match {
          case Some(handler) => handler
          case None => handlers("#")
        }
      }
      handler(req)
    }

    private def printDebugInformation(session: Req, d: Double): Unit = {
      println(s"""
      |Request at: ${session.uri}
      |  Reactor:    ${Reactor.self.name}
      |  Duration:   $d ms
      """.stripMargin.trim)
    }

    private def wrap[T](req: Req, code: =>T): T = {
      val start = System.nanoTime
      try {
        code
      } catch {
        case t: Throwable =>
          t.printStackTrace()
          throw t
      } finally {
        val end = System.nanoTime
        if (debugMode != 0) {
          printDebugInformation(req, (end - start) / 1000 / 1000.0)
        }
      }
    }

    def shutdown(): Unit = {
      setup.shutdown()
    }

    private def respondWith[T](
      mime: MediaType, req: Req, events: Events[T]
    ): Unit = {
      events.materialize.take(1) onMatch {
        case Events.React(x) =>
          req.response.contentType(mime).result(x)
          req.done()
        case Events.Except(t) =>
          t.printStackTrace()
          req.done()
        case Events.Unreact =>
          req.done()
      }
    }

    private def respondWithBody(
      mime: MediaType, req: Req, events: Events[Array[Byte]]
    ): Unit = {
      events.materialize.take(1) onMatch {
        case Events.React(x) =>
          req.response
            .contentType(mime)
            .body(x)
          req.done()
        case Events.Except(t) =>
          t.printStackTrace()
          req.done()
        case Events.Unreact =>
          req.done()
      }
    }

    def text(route: String)(handler: Request => Events[String]): Unit =
      handlers.synchronized {
        val sessionHandler: Req => Unit = req => wrap(req, {
          val events = handler(new Request.Wrapper(req))
          respondWith(MediaType.PLAIN_TEXT_UTF_8, req, events)
        })
        handlers(route) = sessionHandler
      }

    def html(route: String)(handler: Request => Events[String]): Unit =
      handlers.synchronized {
        val sessionHandler: Req => Unit = req => wrap(req, {
          val text = handler(new Request.Wrapper(req))
          respondWith(MediaType.HTML_UTF_8, req, text)
        })
        handlers(route) = sessionHandler
      }

    def json(route: String)(handler: Request => Events[String]): Unit =
      handlers.synchronized {
        val sessionHandler: Req => Unit = req => wrap(req, {
          val text = handler(new Request.Wrapper(req))
          respondWithBody(MediaType.JSON, req, text.map(_.getBytes))
        })
        handlers(route) = sessionHandler
      }

    def resource(route: String)(mime: String)(
      handler: Request => Events[InputStream]
    ): Unit =
      handlers.synchronized {
        val sessionHandler: Req => Unit = req => wrap(req, {
          val inputStream = handler(new Request.Wrapper(req))
          val byteArray = inputStream.map(is => IOUtils.toByteArray(is))
          respondWith(MediaType.of(mime), req, byteArray)
        })
        handlers(route) = sessionHandler
      }

    def default(handler: Request => (String, Any)): Unit =
      handlers.synchronized {
        val sessionHandler: Req => Unit = req => wrap(req, {
          try {
            val (mime, value) = handler(new Request.Wrapper(req))
            req.response.contentType(MediaType.of(mime))
            req.response.result(value)
          } finally {
            req.done()
          }
        })
        handlers(defaultHandlerKey) = sessionHandler
      }

    def async(handler: Request => Unit): Unit = {
      handlers.synchronized {
        val sessionHandler: Req => Unit = req => wrap(req, {
          var completeRequest = true
          handler(new Request.Wrapper(req))
        })
        handlers(defaultHandlerKey) = sessionHandler
      }
    }
  }
}
