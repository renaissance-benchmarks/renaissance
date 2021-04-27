package tutorial;



/*!begin-include!*/
/*!begin-code!*/
import io.reactors.japi.*;
/*!end-code!*/
/*!end-include(reactors-java-schedulers-import.html)!*/
import java.util.ArrayList;
import java.util.Arrays;
import org.junit.Assert;
import org.junit.Test;



public class schedulers_intro {
  static FakeSystem System = new FakeSystem();

  /*!begin-include!*/
  /*!begin-code!*/
  public static class Logger extends Reactor<String> {
    private int count = 3;
    public Logger() {
      sysEvents().onEvent(x -> {
        if (x.isReactorScheduled()) {
          System.out.println("scheduled");
        } else if (x.isReactorPreempted()) {
          count -= 1;
          if (count == 0) {
            main().seal();
            System.out.println("terminating");
          }
        }
      });
      main().events().onEvent(
        x -> System.out.println(x)
      );
    }
  }
  /*!end-code!*/
  /*!end-include(reactors-java-schedulers-logger.html)!*/

  /*!begin-include!*/
  /*!begin-code!*/
  ReactorSystem system = ReactorSystem.create("test-system");
  /*!end-code!*/
  /*!end-include(reactors-java-schedulers-system.html)!*/

  @Test
  public void globalExecutionContext() throws InterruptedException {
    /*!begin-include!*/
    /*!begin-code!*/
    Proto<String> proto = Proto.create(Logger.class).withScheduler(
      Scheduler.GLOBAL_EXECUTION_CONTEXT);
    Channel<String> ch = system.spawn(proto);
    /*!end-code!*/
    /*!end-include(reactors-java-schedulers-global-ec.html)!*/

    Assert.assertEquals("scheduled", System.out.queue.take());

    Thread.sleep(1000);

    /*!begin-include!*/
    /*!begin-code!*/
    ch.send("event 1");
    /*!end-code!*/
    /*!end-include(reactors-java-schedulers-global-ec-send.html)!*/

    Assert.assertEquals("scheduled", System.out.queue.take());
    Assert.assertEquals("event 1", System.out.queue.take());

    Thread.sleep(1000);

    /*!begin-include!*/
    /*!begin-code!*/
    ch.send("event 2");
    /*!end-code!*/
    /*!end-include(reactors-java-schedulers-global-ec-send-again.html)!*/

    Assert.assertEquals("scheduled", System.out.queue.take());
    Assert.assertEquals("event 2", System.out.queue.take());
    Assert.assertEquals("terminating", System.out.queue.take());
  }

  /*!begin-include!*/
  /*!begin-code!*/
  public static class LifecycleReactor extends Reactor<String> {
    private boolean first = true;
    public LifecycleReactor() {
      sysEvents().onEvent(x -> {
        if (x.isReactorStarted()) System.out.println("started");
        else if (x.isReactorScheduled()) System.out.println("scheduled");
        else if (x.isReactorPreempted()) {
          System.out.println("preempted");
          if (first) first = false;
          else throw new RuntimeException("This exception is expected!");
        } else if (x.isReactorDied()) System.out.println("died");
        else if (x.isReactorTerminated()) System.out.println("terminated");
      });
    }
  }
  /*!end-code!*/
  /*!end-include(reactors-java-schedulers-lifecycle.html)!*/

  @Test
  public void lifecycle() throws InterruptedException {
    /*!begin-include!*/
    /*!begin-code!*/
    Channel<String> ch = system.spawn(Proto.create(LifecycleReactor.class));
    /*!end-code!*/
    /*!end-include(reactors-java-schedulers-lifecycle-spawn.html)!*/

    Assert.assertEquals("started", System.out.queue.take());
    Assert.assertEquals("scheduled", System.out.queue.take());
    Assert.assertEquals("preempted", System.out.queue.take());

    Thread.sleep(1000);

    /*!begin-include!*/
    /*!begin-code!*/
    ch.send("event");
    /*!end-code!*/
    /*!end-include(reactors-java-schedulers-lifecycle-send.html)!*/

    Assert.assertEquals("scheduled", System.out.queue.take());
    Assert.assertEquals("preempted", System.out.queue.take());
    Assert.assertEquals("died", System.out.queue.take());
    Assert.assertEquals("terminated", System.out.queue.take());

      }
}
