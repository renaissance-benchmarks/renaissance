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
import java.nio.charset.StandardCharsets
import java.security.MessageDigest
import java.util.Comparator
import java.util.concurrent.atomic.AtomicInteger
import java.util.concurrent.atomic.AtomicReference
import scala.collection._
import scala.collection.immutable.ArraySeq
import scala.collection.mutable.{ArrayBuffer, ListBuffer}
import scala.collection.parallel.CollectionConverters._
import scala.io.Source
import scala.util.hashing.byteswap32

@Name("finagle-chirper")
@Group("web")
@Group("twitter-finagle")
@Summary("Simulates a microblogging service using Twitter Finagle.")
@Licenses(Array(License.APACHE2))
@Repetitions(90)
@Parameter(name = "request_count", defaultValue = "200")
@Parameter(name = "user_count", defaultValue = "5000")
@Parameter(name = "active_users", defaultValue = "100")
@Parameter(name = "threads", defaultValue = "auto")
@Configuration(name = "test", settings = Array("request_count = 10", "user_count = 10", "active_users = 5"))
@Configuration(name = "jmh")
final class FinagleChirper extends Benchmark {

  /**
   * A variant of [[ArrayBuffer]] with support for taking a light-weight snapshot of
   * the underlying array. The snapshot consists of the array reference together with
   * the number of items present and DOES NOT protect against direct modifications of
   * the existing elements or removal of elements from the underlying array. However,
   * it allows iterating over elements that were present at the time of the snapshot,
   * even if the original buffer is appended to after the snapshot was taken.
   */
  final class FeedBuffer[A](initialSize: Int) extends mutable.ArrayBuffer[A](initialSize) {
    def this() = this(FeedBuffer.DefaultInitialSize)

    def snapshotView(): IndexedSeqView[A] = {
      val snapshot = immutable.ArraySeq.unsafeWrapArray(array).asInstanceOf[ArraySeq[A]]
      snapshot.view.take(length)
    }
  }

  // Helper: resolve the `threads` parameter.
  //
  // If the user passes "auto" (case‑insensitive) or leaves it at the
  // default, we return Runtime.getRuntime.availableProcessors().
  // Otherwise we try to parse an integer and make sure it is > 0.
  private def resolveThreads(c: BenchmarkContext): Int = {
    val param = c.parameter("threads")
    scala.util.Try(param.toPositiveInteger).toOption match {
      case Some(n) if n > 0 => n // valid integer
      case None | Some(_) => // "auto" or zero
        Runtime.getRuntime.availableProcessors()
    }
  }

  private def calculateStartingMessagesForUser(username: String): FeedBuffer[String] = {

    val hash = byteswap32(username.length + username.charAt(0))
    val offset = math.abs(hash) % (messages.length - startingFeedSize)
    val startingMessages = messages.slice(offset, offset + startingFeedSize)
    FeedBuffer.from(startingMessages)
  }

  private def calculatePostMessagesForUser(username: String): Unit = {
    // Initialize with starting messages
    userPostsPredicted(username) = calculateStartingMessagesForUser(username)

    // Only calculate additional posts for active users
    if (activeUsers.contains(username)) {
      val offset_posted = byteswap32(username.charAt(username.length - 1))

      for (i <- 0 until requestCountParam) {
        val uid = math.abs(byteswap32(offset_posted * i))
        if (uid % postPeriodicity == 0) {
          val message = messages(uid % messages.length)
          userPostsPredicted(username) += message
        }
      }
    }
  }

  private def getUserPostedMessages(username: String): FeedBuffer[String] = {

    val postedMessages = masterInstance.getUserFeedDirect(username)
    userPostsFetched(username) = postedMessages
    postedMessages
  }

  private def getUsersMessages: concurrent.TrieMap[String, FeedBuffer[String]] = {
    masterInstance.feeds
  }

  private def getHashedMessages(data: concurrent.TrieMap[String, FeedBuffer[String]]): Long = {
    val allMessages = data.keys.toSeq.sorted.flatMap(username => data(username))
    hashMessages(allMessages)
  }

  private def hashMessages(messages: Seq[String]): Long = {
    val sortedMessages = messages.sorted // Sort for consistent hashing
    val concatenated = sortedMessages.mkString("|") // Use separator to avoid ambiguity
    val hash = md.digest(concatenated.getBytes(StandardCharsets.UTF_8))
    ByteBuffer.wrap(hash.take(8)).getLong()
  }

  object FeedBuffer {
    final val DefaultInitialSize = ArrayBuffer.DefaultInitialSize

    def from[A](coll: collection.IterableOnce[A]): FeedBuffer[A] = {
      val initialSize = DefaultInitialSize.max(coll.knownSize)
      new FeedBuffer[A](initialSize) ++= coll
    }
  }

  class Master extends Service[Request, Response] {
    val lock = new AnyRef
    val feeds = new concurrent.TrieMap[String, FeedBuffer[String]]
    var requestCount = 0
    var postCount = 0

    def getUserFeedDirect(username: String): FeedBuffer[String] = {
      feeds.get(username) match {
        case Some(feed) =>
          val allMessages = feed
          allMessages
        case None =>
          new FeedBuffer[String]
      }
    }

    def analyze[T](
      feed: IndexedSeqView[String],
      zero: T,
      f: String => T,
      op: (T, T) => T
    ): T = {
      val a = new Accumulator(zero)(op)
      feed.foreach { msg => a.accumulate(f(msg)) }
      a.get()
    }

    def longestMessageInFeed(feed: IndexedSeqView[String]): String = {
      analyze[String](feed, "", x => x, (x, y) => if (x.length > y.length) x else y)
    }

    def longestMessageInAllFeeds(allFeeds: Seq[IndexedSeqView[String]]): String = {
      var result = ""
      for (feed <- allFeeds) {
        val r = longestMessageInFeed(feed)
        if (r.length > result.length) result = r
      }
      result
    }

    def hashStartCountInAllFeeds(allFeeds: Seq[IndexedSeqView[String]]): Long = {
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

    def longestRechirpInAllFeeds(allFeeds: Seq[IndexedSeqView[String]]): String = {
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

    def mostRechirpsInAllFeeds(allFeeds: Seq[(String, IndexedSeqView[String])]): Long = {
      val counts = ConcurrentHashMultiset.create[String]()
      allFeeds.par.foreach {
        case (username, feed) =>
          for (s <- feed) {
            if (s.length >= 2 && s.charAt(0) == 'R' && s.charAt(1) == 'T')
              counts.add(username)
          }
      }

      counts
        .entrySet()
        .parallelStream()
        .map[Integer] { t: Entry[String] => t.getCount }
        .max(Comparator.naturalOrder[Integer]())
        .get
        .toLong
    }

    override def apply(req: Request): Future[Response] =
      lock.synchronized {
        requestCount += 1
        req.path match {
          case "/api/feed" => handleFeedRequest(req)
          case "/api/post" => handlePostRequest(req)
          case "/api/stats/longest" => handleLongestStatsRequest(req)
          case "/api/stats/hash-tag-count" => handleHashTagCountRequest(req)
          case "/api/stats/longest-rechirp" => handleLongestRechirpRequest(req)
          case "/api/stats/most-rechirps" => handleMostRechirpsRequest(req)
          case "/api/reset" => handleResetRequest(req)
        }
      }

    private def handleFeedRequest(req: Request): Future[Response] = {
      val username = req.getParam("username")
      feeds.get(username) match {
        case Some(feed) =>
          val content = if (feed.isEmpty) "" else feed.mkString("\n")
          val bytes = content.getBytes(StandardCharsets.UTF_8)
          val buf = Buf.ByteArray.Owned(bytes)
          Future.value(Response(req.version, Status.Ok, BufReader(buf)))
        case None =>
          feeds(username) = new FeedBuffer[String]
          Future.value(Response(req.version, Status.Ok, BufReader(Buf.Empty)))
      }
    }

    private def handlePostRequest(req: Request): Future[Response] = {
      postCount += 1
      val username = req.getParam("username")
      val ord = req.getIntParam("ord")
      val content = Buf.Utf8.unapply(req.content).get
      feeds.putIfAbsent(username, new FeedBuffer[String])
      val feed = feeds(username)
      feed += content
      val responseBuf = Buf.ByteArray.Owned(Array[Byte]('o', 'k'))
      Future.value(Response(req.version, Status.Ok, BufReader(responseBuf)))
    }

    private def handleLongestStatsRequest(req: Request): Future[Response] = {
      val allFeeds = for ((_, feed) <- feeds.readOnlySnapshot()) yield feed.snapshotView()
      FuturePool.unboundedPool {
        val message = longestMessageInAllFeeds(allFeeds.toSeq)
        val bytes = message.getBytes("UTF-8")
        val buf = Buf.ByteArray.Owned(bytes)
        Response(req.version, Status.Ok, BufReader(buf))
      }
    }

    private def handleHashTagCountRequest(req: Request): Future[Response] = {
      val allFeeds = for ((_, feed) <- feeds.readOnlySnapshot()) yield feed.snapshotView()
      FuturePool.unboundedPool {
        val count = hashStartCountInAllFeeds(allFeeds.toSeq)
        val buffer = ByteBuffer.allocate(8)
        buffer.putLong(count)
        val bytes = buffer.array()
        val buf = Buf.ByteArray.Owned(bytes)
        Response(req.version, Status.Ok, BufReader(buf))
      }
    }

    private def handleLongestRechirpRequest(req: Request): Future[Response] = {
      val allFeeds = for ((_, feed) <- feeds.readOnlySnapshot()) yield feed.snapshotView()
      FuturePool.unboundedPool {
        val message = longestRechirpInAllFeeds(allFeeds.toSeq)
        val bytes = message.getBytes("UTF-8")
        val buf = Buf.ByteArray.Owned(bytes)
        Response(req.version, Status.Ok, BufReader(buf))
      }
    }

    private def handleMostRechirpsRequest(req: Request): Future[Response] = {
      val allFeeds =
        for ((username, feed) <- feeds.readOnlySnapshot()) yield (username, feed.snapshotView())
      FuturePool.unboundedPool {
        val count = mostRechirpsInAllFeeds(allFeeds.toSeq)
        val buffer = ByteBuffer.allocate(8)
        buffer.putLong(count)
        val bytes = buffer.array()
        val buf = Buf.ByteArray.Owned(bytes)
        Response(req.version, Status.Ok, BufReader(buf))
      }
    }

    private def handleResetRequest(req: Request): Future[Response] = {
      feeds.clear()
      for (username <- userNames) {
        feeds(username) = calculateStartingMessagesForUser(username)
      }

      println("Resetting master, feed map size: " + feeds.size)
      Future.value(Response(req.version, Status.Ok, BufReader(Buf.Empty)))
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

  class Client(val assignedUsers: Seq[String]) extends Thread {
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
      for (username <- assignedUsers) {

        val feedQuery = "/api/feed?username=" + username
        val offset = byteswap32(username.charAt(username.length - 1))
        var i = 0

        for (i <- 0 until requestCountParam) {
          val uid = math.abs(byteswap32(offset * i))
          if (uid % postPeriodicity == 0) {
            postCount += 1

            //   Post a new message.
            val message = messages(uid % messages.length)

            val postQuery = s"/api/post?username=$username&ord=$postCount"
            val request = Request(Method.Post, postQuery)

            val messageBytes = message.getBytes(StandardCharsets.UTF_8)
            request.content = Buf.ByteArray.Owned(messageBytes)

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
        }
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
  val caches = new mutable.ArrayBuffer[ListeningServer]
  var cachePorts = new mutable.ArrayBuffer[Int]
  val startingFeedSize = 80
  private var clientCount: Int = _
  private var cacheCount: Int = _
  private var userCountParam: Int = _
  private var activeUsersParam: Int = _
  private var requestCountParam: Int = _
  private var masterInstance: Master = _
  private var md: MessageDigest = _
  private var predictedResult: Long = _
  private var activeUsers: Seq[String] = _
  private var userGroups: Seq[Seq[String]] = _

  var userPostsPredicted: concurrent.TrieMap[String, FeedBuffer[String]] =
    new concurrent.TrieMap()

  var userPostsFetched: concurrent.TrieMap[String, FeedBuffer[String]] =
    new concurrent.TrieMap()

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
    FinagleUtil.setUpLoggers()

    clientCount = resolveThreads(c)
    cacheCount = resolveThreads(c)
    requestCountParam = c.parameter("request_count").toPositiveInteger
    userCountParam = c.parameter("user_count").toPositiveInteger
    activeUsersParam = c.parameter("active_users").toPositiveInteger

    // active users can't be greater than user count
    assert(
      activeUsersParam <= userCountParam,
      s"Active users ($activeUsersParam) cannot be greater than total user count ($userCountParam)"
    )

    md = MessageDigest.getInstance("MD5")

    userNames =
      for (i <- 0 until userCountParam)
        yield usernameBases(i % usernameBases.length) + i

    // shuffle, we want different users
    activeUsers = scala.util.Random.shuffle(userNames).take(activeUsersParam)

    val baseUsersPerThread = activeUsersParam / clientCount
    val remainder = activeUsersParam % clientCount
    val userGroupsBuffer = mutable.ArrayBuffer[Seq[String]]()
    var currentIndex = 0

    for (i <- 0 until clientCount) {
      val usersForThisThread = if (i < remainder) baseUsersPerThread + 1 else baseUsersPerThread
      val endIndex = currentIndex + usersForThisThread
      userGroupsBuffer += activeUsers.slice(currentIndex, endIndex)
      currentIndex = endIndex
    }

    userGroups = userGroupsBuffer.toSeq

    messages = resourceAsLines(inputFile)

    masterInstance = new Master
    master = Http.serve(":0", masterInstance)
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
    println(s"Will use $clientCount threads to handle $activeUsersParam users")

    masterService = Http.newService(":" + masterPort)

    // Predict posts
    for (username <- userNames) {
      calculatePostMessagesForUser(username)
    }

    predictedResult = getHashedMessages(userPostsPredicted)
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

    val clients = userGroups.map(ug => new Client(ug))
    clients.foreach(_.start())
    clients.foreach(_.join())

    Validators.simple(
      "comparing hash of predicted and fetched messages ",
      predictedResult,
      getHashedMessages(getUsersMessages)
    )
  }

  private def resourceAsLines(resourceName: String) = {
    val source =
      Source.fromInputStream(getResourceStream(resourceName), StandardCharsets.UTF_8.name)
    try {
      source.getLines().map { _.trim }.filterNot { _.isEmpty }.toIndexedSeq
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
