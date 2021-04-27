package io.reactors
package concurrent



import io.reactors.services._
import java.util.Date
import scala.collection._
import scala.concurrent.duration._
import scala.reflect.ClassTag



/** Defines services used by an reactor system.
 */
abstract class Services extends Platform.Reflectable {
  def system: ReactorSystem

  private val services = mutable.Map[ClassTag[_], AnyRef]()

  /** System configuration */
  def config = system.bundle.config

  /** Clock services. */
  val clock = service[Clock]

  /** Debugger services. */
  val debugger = service[Debugger]

  /** Logging services. */
  val log = service[Log]

  /** Naming services. */
  val names = service[Names]

  /** I/O services. */
  val io = service[Io]

  /** Network services. */
  val net = service[Net]

  /** Remoting services, used to contact other reactor systems. */
  lazy val remote = service[Remote]

  /** The register of channels in this reactor system.
   *
   *  Used for creating and finding channels.
   */
  val channels = service[Channels]

  /** Arbitrary service. */
  def service[T <: Protocol.Service: ClassTag] = {
    system.monitor.synchronized {
      val tag = implicitly[ClassTag[T]]
      if (!services.contains(tag)) {
        services(tag) =
          Platform.Reflect.instantiate(tag.runtimeClass, Seq(system))
            .asInstanceOf[AnyRef]
      }
      services(tag).asInstanceOf[T]
    }
  }

  /** Shut down all services. */
  protected def shutdownServices() {
    for ((_, service) <- services) {
      service.asInstanceOf[Protocol.Service].shutdown()
    }
  }
}


/** Contains common service implementations.
 */
object Services {
  private[reactors] def loggingTag(): String = {
    val time = System.currentTimeMillis()
    val d = new Date(time)
    val formattedDate = d.toString
    val frame = Reactor.self[Nothing].frame
    s"[$formattedDate | ${frame.name} <${frame.uid}>] "
  }
}
