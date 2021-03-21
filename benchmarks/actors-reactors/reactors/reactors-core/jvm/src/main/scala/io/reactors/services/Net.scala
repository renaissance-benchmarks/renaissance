package io.reactors
package services



import java.io._
import java.net.URL
import java.util.concurrent.ForkJoinPool
import scala.concurrent._
import scala.util.Failure
import scala.util.Success
import scala.util.Try



/** Contains common network protocol services.
 */
class Net(val system: ReactorSystem, private val resolver: URL => InputStream)
extends Protocol.Service {
  private val networkRequestForkJoinPool = {
    val parallelism = system.config.int("system.net.parallelism")
    new ForkJoinPool(parallelism)
  }
  private implicit val networkRequestContext: ExecutionContext =
    ExecutionContext.fromExecutor(networkRequestForkJoinPool)

  def this(s: ReactorSystem) = this(s, url => url.openStream())

  def shutdown() {
    networkRequestForkJoinPool.shutdown()
  }

  /** Asynchronously retrieves the resource at the given URL.
   *
   *  Once the resource is retrieved, the resulting `IVar` gets a string event with
   *  the resource contents.
   *  In the case of failure, the event stream raises an exception and unreacts.
   *
   *  @param url     the url to load the resource from
   *  @param cs      the name of the charset to use
   *  @return        a single-assignment variable with the resource string
   */
  def resourceAsString(
    url: String, cs: String = system.io.defaultCharset
  ): IVar[String] = {
    val connector = system.channels.daemon.open[Try[String]]
    Future {
      blocking {
        val inputStream = resolver(new URL(url))
        try {
          val sb = new StringBuilder
          val reader = new BufferedReader(new InputStreamReader(inputStream))
          var line = reader.readLine()
          while (line != null) {
            sb.append(line)
            line = reader.readLine()
          }
          sb.toString
        } finally {
          inputStream.close()
        }
      }
    } onComplete {
      case s @ Success(_) =>
        connector.channel ! s
      case f @ Failure(t) =>
        connector.channel ! f
    }
    val ivar = connector.events.map({
      case Success(s) => s
      case Failure(t) => throw t
    }).toIVar
    ivar.ignoreExceptions.onDone(connector.seal())
    ivar
  }
}
