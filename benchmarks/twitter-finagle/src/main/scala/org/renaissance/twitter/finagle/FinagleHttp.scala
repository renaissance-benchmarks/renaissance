package org.renaissance.twitter.finagle

import java.net.InetSocketAddress
import java.util.Date
import java.util.concurrent.CountDownLatch

import com.fasterxml.jackson.databind.ObjectMapper
import com.fasterxml.jackson.module.scala.DefaultScalaModule
import com.twitter.finagle.ListeningServer
import com.twitter.finagle.http.HttpMuxer
import com.twitter.finagle.http.Request
import com.twitter.finagle.http.Response
import com.twitter.finagle.stats.NullStatsReceiver
import com.twitter.finagle.tracing.NullTracer
import com.twitter.finagle.Service
import com.twitter.finagle.SimpleFilter
import com.twitter.finagle.http
import com.twitter.io.Buf
import com.twitter.util.Await
import com.twitter.util.Future
import org.renaissance.Benchmark
import org.renaissance.Benchmark._
import org.renaissance.BenchmarkContext
import org.renaissance.BenchmarkResult
import org.renaissance.License

@Name("finagle-http")
@Group("twitter-finagle")
@Summary("Sends many small Finagle HTTP requests to a Finagle HTTP server and awaits response.")
@Licenses(Array(License.APACHE2))
@Repetitions(12)
class FinagleHttp extends Benchmark {

  class WorkerThread(port: Int, barrier: CountDownLatch, requestCount: Int) extends Thread {
    var totalContentLength = 0L

    override def run(): Unit = {
      val client: Service[http.Request, http.Response] =
        com.twitter.finagle.Http.newService(s"localhost:$port")

      try {
        barrier.countDown
        barrier.await

        for (i <- 0 until requestCount) {
          val request = http.Request(http.Method.Get, "/json")
          request.host = s"localhost:$port"

          val response: Future[http.Response] = client(request)

          // Need to use map() instead of onSuccess() as we actually need to
          // wait for the side-effect, not the original response
          Await.result(response.map { rep: http.Response =>
            totalContentLength += rep.content.length
          })
        }

      } finally {
        client.close()
      }
    }
  }

  // TODO: Consolidate benchmark parameters across the suite.
  //  See: https://github.com/renaissance-benchmarks/renaissance/issues/27

  /** Number of requests sent during the execution of the benchmark.
   */
  var NUM_REQUESTS = 12000

  /** Number of clients that are simultaneously sending the requests.
   */
  var NUM_CLIENTS = Runtime.getRuntime.availableProcessors

  /** Manually computed length of one request (see /json handler).
   */
  val REQUEST_CONTENT_SIZE = 27

  var server: ListeningServer = null

  var port: Int = -1

  var threads: Array[WorkerThread] = null
  var threadBarrier: CountDownLatch = null

  override def setUpBeforeAll(c: BenchmarkContext): Unit = {
    if (c.functionalTest) {
      NUM_REQUESTS = 150
      NUM_CLIENTS = 2
    }

    val mapper: ObjectMapper = new ObjectMapper().registerModule(DefaultScalaModule)
    val helloWorld: Buf = Buf.Utf8("Hello, World!")
    val muxer: HttpMuxer = new HttpMuxer()
      .withHandler(
        "/json",
        Service.mk { req: Request =>
          val rep = Response()
          rep.content =
            Buf.ByteArray.Owned(mapper.writeValueAsBytes(Map("message" -> "Hello, World!")))
          rep.contentType = "application/json"
          Future.value(rep)
        }
      )
      .withHandler("/plaintext", Service.mk { req: Request =>
        val rep = Response()
        rep.content = helloWorld
        rep.contentType = "text/plain"
        Future.value(rep)
      })

    val serverAndDate: SimpleFilter[Request, Response] =
      new SimpleFilter[Request, Response] {
        private[this] val addServerAndDate: Response => Response = { rep =>
          rep.server = "Finagle"
          rep.date = new Date()
          rep
        }

        def apply(req: Request, s: Service[Request, Response]): Future[Response] =
          s(req).map(addServerAndDate)
      }

    server = com.twitter.finagle.Http.server
      .withCompressionLevel(0)
      .withStatsReceiver(NullStatsReceiver)
      .withTracer(NullTracer)
      .serve(s":0", serverAndDate.andThen(muxer))
    port = server.boundAddress.asInstanceOf[InetSocketAddress].getPort
    println(
      "finagle-http on :%d spawning %d client and %s server workers.".format(
        port,
        NUM_CLIENTS,
        System.getProperty("com.twitter.finagle.netty4.numWorkers", "default number of")
      )
    )
  }

  override def tearDownAfterAll(c: BenchmarkContext): Unit = {
    server.close()
  }

  override def beforeIteration(c: BenchmarkContext): Unit = {
    //
    // Use a CountDownLatch initialized to NUM_CLIENTS + 1 to start the
    // threads (outside the measured loop) and make them block until the
    // measured operation is executed. In the measured operation, we provide
    // the one last countDown() invocation which unblocks all the threads
    // and lets the start working simultaneously.
    //
    threadBarrier = new CountDownLatch(NUM_CLIENTS + 1)

    threads = new Array[WorkerThread](NUM_CLIENTS)
    for (i <- threads.indices) {
      threads(i) = new WorkerThread(port, threadBarrier, NUM_REQUESTS)
      threads(i).setName(s"finagle-http-worker-$i")
      threads(i).start()
    }
  }

  override def runIteration(c: BenchmarkContext): BenchmarkResult = {
    // Let the threads do the work (see beforeIteration)
    threadBarrier.countDown

    var totalLength = 0L
    for (thread <- threads) {
      thread.join()
      totalLength += thread.totalContentLength
    }

    BenchmarkResult.simple(
      "total request length",
      NUM_CLIENTS * NUM_REQUESTS * REQUEST_CONTENT_SIZE,
      totalLength
    )
  }
}
