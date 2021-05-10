package org.renaissance.twitter.finagle

import com.google.common.collect.ConcurrentHashMultiset
import com.google.common.collect.Multiset.Entry
import com.twitter.finagle.Http
import com.twitter.finagle.ListeningServer
import com.twitter.finagle.Service
import com.twitter.finagle.http.Method
import com.twitter.finagle.http.Request
import com.twitter.finagle.http.Response
import com.twitter.finagle.http.Status
import com.twitter.io.Buf
import com.twitter.io.BufReader
import com.twitter.util.Await
import com.twitter.util.Future
import com.twitter.util.FuturePool
import org.renaissance.Benchmark
import org.renaissance.Benchmark._
import org.renaissance.BenchmarkContext
import org.renaissance.BenchmarkResult
import org.renaissance.BenchmarkResult.Validators
import org.renaissance.License

import java.io.FileNotFoundException
import java.io.InputStream
import java.net.InetSocketAddress
import java.net.URLEncoder
import java.nio.ByteBuffer
import java.util.Comparator
import java.util.concurrent.atomic.AtomicInteger
import java.util.concurrent.atomic.AtomicReference
import scala.collection._
import scala.io.Source
import scala.util.hashing.byteswap32

@Name("finagle-chirper")
@Group("twitter-finagle")
@Summary("Simulates a microblogging service using Twitter Finagle.")
@Licenses(Array(License.APACHE2))
@Repetitions(90)
@Parameter(name = "request_count", defaultValue = "1250")
@Parameter(name = "user_count", defaultValue = "5000")
@Configuration(name = "test", settings = Array("request_count = 10", "user_count = 10"))
@Configuration(name = "jmh")
final class FinagleChirper extends Benchmark {

  class Master extends Service[Request, Response] {
    val lock = new AnyRef
    val feeds = new concurrent.TrieMap[String, mutable.ArrayBuffer[String]]
    var requestCount = 0
    var postCount = 0

    def analyze[T](feed: Seq[String], zero: T, f: String => T, op: (T, T) => T): T = {
      val a = new Accumulator(zero)(op)
      for (msg <- feed) a.accumulate(f(msg))
      a.get()
    }

    def longestMessageInFeed(feed: Seq[String]): String = {
      analyze[String](feed, "", x => x, (x, y) => if (x.length > y.length) x else y)
    }

    def longestMessageInAllFeeds(allFeeds: Seq[Seq[String]]): String = {
      var result = ""
      for (feed <- allFeeds) {
        val r = longestMessageInFeed(feed)
        if (r.length > result.length) result = r
      }
      result
    }

    def hashStartCountInAllFeeds(allFeeds: Seq[Seq[String]]): Long = {
      var result = 0L
      for (feed <- allFeeds) {
        result += analyze[Long](
          feed,
          0,
          s => {
            if (s.length > 0 && s.charAt(0) == '#') 1 else 0
          },
          _ + _
        )
      }
      result
    }

    def longestRechirpInAllFeeds(allFeeds: Seq[Seq[String]]): String = {
      var result = ""
      for (feed <- allFeeds) {
        val s = analyze[String](
          feed,
          "",
          s => {
            if (s.length >= 2 && s.charAt(0) == 'R' && s.charAt(1) == 'T') s else ""
          },
          (x, y) => {
            if (x.length > y.length) x else y
          }
        )
        if (s.length > result.length) result = s
      }
      result
    }

    def mostRechirpsInAllFeeds(allFeeds: Seq[(String, Seq[String])]): Long = {
      val counts = ConcurrentHashMultiset.create[String]()
      allFeeds.par.foreach {
        case (username, feed) =>
          for (s <- feed) {
            if (s.length >= 2 && s.charAt(0) == 'R' && s.charAt(1) == 'T')
              counts.add(username)
          }
      }

      val compInt = new Comparator[Integer] {
        override def compare(c1: Integer, c2: Integer): Int = {
          c1.compareTo(c2);
        }
        def naturalOrder(): Comparator[Integer] =
          return new Comparator[Integer] {
            override def compare(c1: Integer, c2: Integer): Int = {
              c1.compareTo(c2);
            }
            override def reversed(): Comparator[Integer] = {
              Comparator.reverseOrder[Integer];
            }
          }
      }

      counts
        .entrySet()
        .parallelStream()
        .map[Integer](
          new java.util.function.Function[Entry[String], Integer] {
            override def apply(t: Entry[String]): Integer = t.getCount
          }
        )
        .max(compInt.naturalOrder())
        .get
        .toLong
    }

    override def apply(req: Request): Future[Response] =
      lock.synchronized {
        requestCount += 1

        req.path match {
          case "/api/feed" =>
            val username = req.getParam("username")
            feeds.get(username) match {
              case Some(feed) =>
                var length = 0
                for (msg <- feed) length += msg.length + 1
                length += 1
                val bytes = new Array[Byte](length)
                var i = 0
                for (msg <- feed) {
                  for (j <- 0 until msg.length) {
                    bytes(i) = msg(j).toByte
                    i += 1
                  }
                  bytes(i) = '\n'
                  i += 1
                }
                val buf = Buf.ByteArray.Owned(bytes)
                val response = Response(req.version, Status.Ok, BufReader(buf))
                Future.value(response)
              case None =>
                feeds(username) = new mutable.ArrayBuffer[String]
                val response = Response(req.version, Status.Ok, BufReader(Buf.Empty))
                Future.value(response)
            }
          case "/api/post" =>
            postCount += 1
            val username = req.getParam("username")
            val ord = req.getIntParam("ord")
            val buf = req.content
            val content = Buf.Utf16.unapply(buf).get
            feeds.putIfAbsent(username, new mutable.ArrayBuffer[String])
            val feed = feeds(username)
            feed += content
            val responseBuf = Buf.ByteArray.Owned(Array[Byte]('o', 'k'))
            val response = Response(req.version, Status.Ok, BufReader(responseBuf))
            Future.value(response)
          case "/api/stats/longest" =>
            val allFeeds =
              for ((_, feed) <- feeds.readOnlySnapshot())
                yield feed.view.take(feed.length)
            FuturePool.unboundedPool {
              val message = longestMessageInAllFeeds(allFeeds.toSeq)
              val bytes = message.getBytes("UTF-8")
              val buf = Buf.ByteArray.Owned(bytes)
              Response(req.version, Status.Ok, BufReader(buf))
            }
          case "/api/stats/hash-tag-count" =>
            val allFeeds =
              for ((_, feed) <- feeds.readOnlySnapshot())
                yield feed.view.take(feed.length)
            FuturePool.unboundedPool {
              val count = hashStartCountInAllFeeds(allFeeds.toSeq)
              val buffer = ByteBuffer.allocate(8)
              buffer.putLong(count)
              val bytes = buffer.array()
              val buf = Buf.ByteArray.Owned(bytes)
              Response(req.version, Status.Ok, BufReader(buf))
            }
          case "/api/stats/longest-rechirp" =>
            val allFeeds =
              for ((_, feed) <- feeds.readOnlySnapshot())
                yield feed.view.take(feed.length)
            FuturePool.unboundedPool {
              val message = longestRechirpInAllFeeds(allFeeds.toSeq)
              val bytes = message.getBytes("UTF-8")
              val buf = Buf.ByteArray.Owned(bytes)
              Response(req.version, Status.Ok, BufReader(buf))
            }
          case "/api/stats/most-rechirps" =>
            val allFeeds =
              for ((username, feed) <- feeds.readOnlySnapshot())
                yield (username, feed.view.take(feed.length))
            FuturePool.unboundedPool {
              val count = mostRechirpsInAllFeeds(allFeeds.toSeq)
              val buffer = ByteBuffer.allocate(8)
              buffer.putLong(count)
              val bytes = buffer.array()
              val buf = Buf.ByteArray.Owned(bytes)
              Response(req.version, Status.Ok, BufReader(buf))
            }
          case "/api/reset" =>
            feeds.clear()
            for (username <- userNames) {
              val hash = byteswap32(username.length + username.charAt(0))
              val offset = math.abs(hash) % (messages.length - startingFeedSize)
              val startingMessages = messages.slice(offset, offset + startingFeedSize)
              feeds(username) = startingMessages.to[mutable.ArrayBuffer]
            }
            println("Resetting master, feed map size: " + feeds.size)
            val response = Response(req.version, Status.Ok, BufReader(Buf.Empty))
            Future.value(response)
        }
      }
  }

  class Cache(val index: Int, val service: Service[Request, Response])
    extends Service[Request, Response] {
    val cache = new concurrent.TrieMap[String, Buf]
    val count = new AtomicInteger

    override def apply(req: Request): Future[Response] = {
      val uid = math.abs((index * count.incrementAndGet()).toDouble.hashCode)
      if (uid % invalidationPeriodicity == 0) {
        cache.clear()
      }

      val username = req.getParam("username")
      cache.get(username) match {
        case Some(valueBuffer) =>
          val response = Response(req.version, Status.Ok, BufReader(valueBuffer))
          Future.value(response)
        case None =>
          val request = Request(Method.Get, "/api/feed?username=" + username)
          val responseFuture = service(request)
          for (response <- responseFuture) yield {
            cache(username) = response.content
            response
          }
      }
    }
  }

  class Client(val username: String) extends Thread {
    var digest = 0
    var postCount = 0

    val statVariants = Seq[(Int, Service[Request, Response] => Unit)](
      (
        20,
        master => {
          val query = "/api/stats/longest"
          val request = Request(Method.Get, query)
          digest += Await.result(master.apply(request)).content.length
        }
      ),
      (
        20,
        master => {
          val query = "/api/stats/hash-tag-count"
          val request = Request(Method.Get, query)
          digest += Await.result(master.apply(request)).content.length
        }
      ),
      (
        20,
        master => {
          val query = "/api/stats/longest-rechirp"
          val request = Request(Method.Get, query)
          digest += Await.result(master.apply(request)).content.length
        }
      ),
      (
        50,
        master => {
          val query = "/api/stats/most-rechirps"
          val request = Request(Method.Get, query)
          digest += Await.result(master.apply(request)).content.length
        }
      )
    )

    val statMultiplicities: Seq[Service[Request, Response] => Unit] = for {
      (m, s) <- statVariants
      v <- Seq.fill(m)(s)
    } yield v

    override def run(): Unit = {
      val master = Http.newService(":" + masterPort)
      val feeds = for (cachePort <- cachePorts) yield {
        Http.newService(":" + cachePort)
      }
      val feedQuery = "/api/feed?username=" + username
      val offset = byteswap32(username.charAt(username.length - 1))
      var i = 0
      while (i < requestCountParam) {
        val uid = math.abs(byteswap32(offset * i))
        if (uid % postPeriodicity == 0) {
          postCount += 1
          //   Post a new message.
          val message = messages(uid % messages.length)
          val postQuery = "/api/post?username=" + username +
            "&message=" + URLEncoder.encode(message, "UTF-8") +
            "&ord=" + postCount
          val request = Request(Method.Get, postQuery)
          val response = Await.result(master.apply(request))
          require(
            response.status == Status.Ok,
            s"The response status is ${response.status}, message: $message"
          )
        } else if (uid % statisticsPeriodicity == 0) {
          // Get some feed statistics.
          statMultiplicities(uid % statMultiplicities.length).apply(master)
        } else {
          // Fetch a few feeds.
          val request = Request(Method.Get, feedQuery)
          val responses = for (i <- 0 until batchSize) yield {
            val feedService = feeds(uid % cacheCount)
            val response: Future[Response] = feedService.apply(request)
            response
          }
          val contents = Await.result(Future.collect(responses))
          for (content <- contents) digest += content.toString.hashCode
        }
        i += 1
      }
      for (feed <- feeds) {
        Await.ready(feed.close())
      }
      Await.ready(master.close())
    }
  }

  class Accumulator[T](zero: T)(val operator: (T, T) => T) {
    private val value = new AtomicReference[T](zero)

    def get(): T = value.get()

    def accumulate(x: T): Unit = {
      val ov = value.get()
      val nv = operator(ov, x)
      value.compareAndSet(ov, nv)
    }
  }

  // Start with / so it is treated as an absolute path
  // (here, "/" is platform independent according to the JavaDoc)
  val inputFile = "/new-years-resolution.csv"

  private var messages: IndexedSeq[String] = _

  val postPeriodicity: Int = 57
  val invalidationPeriodicity: Int = 256
  val statisticsPeriodicity: Int = 19
  val batchSize = 4
  var master: ListeningServer = null
  var masterPort: Int = -1
  var masterService: Service[Request, Response] = null
  val clientCount = Runtime.getRuntime.availableProcessors
  val cacheCount = Runtime.getRuntime.availableProcessors
  val caches = new mutable.ArrayBuffer[ListeningServer]
  var cachePorts = new mutable.ArrayBuffer[Int]
  val startingFeedSize = 80

  private var requestCountParam: Int = _

  val usernameBases = Seq(
    "johnny",
    "shaokahn",
    "mila",
    "mihovil",
    "yathan",
    "jack",
    "jill",
    "jeanette",
    "billie",
    "lubomir",
    "danilino",
    "francois",
    "metadron",
    "heidi",
    "jovance",
    "giussepe",
    "supermario",
    "luigi",
    "borisov",
    "bapra",
    "jopec",
    "william",
    "mirza",
    "ivanhoe",
    "andrea",
    "thurin",
    "oana",
    "terence",
    "ganimed",
    "sharon",
    "betty",
    "megatron",
    "voltaire",
    "zumma",
    "baobab",
    "zhen",
    "kunglao",
    "yvette"
  )

  private var userNames: Seq[String] = _

  override def setUpBeforeAll(c: BenchmarkContext): Unit = {
    requestCountParam = c.parameter("request_count").toPositiveInteger
    val userCountParam = c.parameter("user_count").toPositiveInteger

    userNames =
      for (i <- 0 until userCountParam)
        yield usernameBases(i % usernameBases.length) + i

    messages = resourceAsLines(inputFile)

    master = Http.serve(":0", new Master)
    /* TODO
    Implement an unified mechanism of assigning ports to benchmarks.
    Related to https://github.com/D-iii-S/renaissance-benchmarks/issues/13
     */
    masterPort = master.boundAddress.asInstanceOf[InetSocketAddress].getPort
    for (i <- 0 until cacheCount) {
      caches += Http.serve(":0", new Cache(i, Http.newService(":" + masterPort)))
      cachePorts += caches.last.boundAddress.asInstanceOf[InetSocketAddress].getPort
    }
    println("Master port: " + masterPort)
    println("Cache ports: " + cachePorts.mkString(", "))
    masterService = Http.newService(":" + masterPort)
  }

  override def tearDownAfterAll(c: BenchmarkContext): Unit = {
    for (cache <- caches) {
      Await.ready(cache.close())
    }
    Await.ready(master.close())
    Await.ready(masterService.close())
  }

  override def setUpBeforeEach(c: BenchmarkContext): Unit = {
    val resetQuery = "/api/reset"
    val request = Request(Method.Get, resetQuery)
    require(Await.result(masterService.apply(request)).status == Status.Ok)
  }

  override def run(c: BenchmarkContext): BenchmarkResult = {
    val clients =
      for (i <- 0 until clientCount)
        yield new Client(userNames(i % userNames.length) + i)
    clients.foreach(_.start())
    clients.foreach(_.join())

    // TODO: add proper validation
    Validators.dummy()
  }

  private def resourceAsLines(resourceName: String) = {
    val source = Source.fromInputStream(getResourceStream(resourceName))
    try {
      source.getLines().map { _.trim }.filterNot { _.isEmpty }.to[IndexedSeq]
    } finally {
      source.close()
    }
  }

  private def getResourceStream(resourceName: String): InputStream = {
    val is = getClass.getResourceAsStream(resourceName)
    if (is != null) {
      return is
    }

    throw new FileNotFoundException(s"resource '$resourceName' not found")
  }
}
