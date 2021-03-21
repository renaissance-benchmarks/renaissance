package tutorial;



import io.reactors.japi.*;
/*!begin-include!*/
/*!begin-code!*/
import io.reactors.japi.services.Log;
/*!end-code!*/
/*!end-include(reactors-java-services-log-import.html)!*/
import java.util.HashMap;
import java.util.Map;
import org.junit.Assert;
import org.junit.Test;



public class services {
  static FakeSystem System = new FakeSystem();

  @Test
  public void useLog() {
    ReactorSystem system = ReactorSystem.create("test-system");
    try {
      /*!begin-include!*/
      /*!begin-code!*/
      Proto<String> proto = Reactor.apply(self -> {
        Log log = system.service(Log.class);
        log.info("Test reactor started!");
        self.main().seal();
      });
      system.spawn(proto);
      /*!end-code!*/
      /*!end-include(reactors-java-services-log-example.html)!*/

      Thread.sleep(100);
    } catch (Throwable t) {
      throw new RuntimeException(t);
    } finally {
      system.shutdown();
    }
  }

  @Test
  public void useClock() {
    ReactorSystem system = ReactorSystem.create("test-system");
    try {
      /*!begin-include!*/
      /*!begin-code!*/
      Proto<String> proto = Reactor.apply(self -> {
        system.clock().timeout(1000).onEvent(v -> {
          System.out.println("Timeout!");
          self.main().seal();
        });
      });
      system.spawn(proto);
      /*!end-code!*/
      /*!end-include(reactors-java-services-timeout.html)!*/

      Assert.assertEquals("Timeout!", System.out.queue.take());
    } catch (Throwable t) {
      throw new RuntimeException(t);
    } finally {
      system.shutdown();
    }
  }

  @Test
  public void useChannels() {
    ReactorSystem system = ReactorSystem.create("test-system");
    try {
      /*!begin-include!*/
      /*!begin-code!*/
      Proto<String> proto = Reactor.apply(self -> {
        system.clock().timeout(1000).onEvent(v -> {
          Connector<Integer> c =
            system.channels().daemon().named("lucky").<Integer>open();
          c.events().onEvent(i -> {
            System.out.println("Done!");
            self.main().seal();
          });
        });
      });
      system.spawn(proto.withName("first"));

      system.spawn(Reactor.apply(self -> {
        system.channels().<Integer>await("first", "lucky").onEvent(ch -> {
          ch.send(7);
          self.main().seal();
        });
      }));
      /*!end-code!*/
      /*!end-include(reactors-java-services-channels.html)!*/

      Assert.assertEquals("Done!", System.out.queue.take());
    } catch (Throwable t) {
      throw new RuntimeException(t);
    } finally {
      system.shutdown();
    }
  }
}
