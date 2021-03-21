package tutorial;



/*!begin-include!*/
/*!begin-code!*/
import io.reactors.japi.*;
/*!end-code!*/
/*!end-include(reactors-java-reactors-import.html)!*/
import java.util.HashMap;
import java.util.Map;
import org.junit.Assert;
import org.junit.Test;



public class reactors_intro {

  /*!begin-include!*/
  /*!begin-code!*/
  ReactorSystem system = ReactorSystem.create("test-system");
  /*!end-code!*/
  /*!end-include(reactors-java-reactors-system.html)!*/

  static FakeSystem System = new FakeSystem();

  @Test
  public void runsAnonymousReactor() {
    /*!begin-include!*/
    /*!begin-code!*/
    Proto<String> proto = Reactor.apply(
      self -> self.main().events().onEvent(x -> System.out.println(x))
    );
    /*!end-code!*/
    /*!end-include(reactors-java-reactors-anonymous.html)!*/

    /*!begin-include!*/
    /*!begin-code!*/
    Channel<String> ch = system.spawn(proto);
    /*!end-code!*/
    /*!end-include(reactors-java-reactors-spawn.html)!*/

    /*!begin-include!*/
    /*!begin-code!*/
    ch.send("Hola!");
    /*!end-code!*/
    /*!end-include(reactors-java-reactors-send.html)!*/

    try {
      Assert.assertEquals("Hola!", System.out.queue.take());
    } catch (Exception e) {
      throw new RuntimeException(e);
    }
  }

  /*!begin-include!*/
  /*!begin-code!*/
  public static class HelloReactor extends Reactor<String> {
    public HelloReactor() {
      main().events().onEvent(
        x -> System.out.println(x)
      );
    }
  }
  /*!end-code!*/
  /*!end-include(reactors-java-reactors-template.html)!*/

  @Test
  public void runsHelloReactor() {
    ReactorSystem system = ReactorSystem.create("test-system");

    /*!begin-include!*/
    /*!begin-code!*/
    Proto<String> proto = Proto.create(HelloReactor.class);
    Channel<String> ch = system.spawn(proto);
    ch.send("Howdee!");
    /*!end-code!*/
    /*!end-include(reactors-java-reactors-spawn-template.html)!*/

    try {
      Assert.assertEquals("Howdee!", System.out.queue.take());
    } catch (Exception e) {
      throw new RuntimeException(e);
    }

    /*!begin-include!*/
    /*!begin-code!*/
    system.spawn(Proto.create(HelloReactor.class)
      .withScheduler(Scheduler.NEW_THREAD));
    /*!end-code!*/
    /*!end-include(reactors-java-reactors-with-scheduler.html)!*/

    /*!begin-include!*/
    /*!begin-code!*/
    system.bundle().registerScheduler("customTimer", Scheduler.timer(1000));
    Proto<String> protoWithTimer =
      Proto.create(HelloReactor.class).withScheduler("customTimer");
    Channel<String> periodic = system.spawn(protoWithTimer);
    periodic.send("Ohayo");
    /*!end-code!*/
    /*!end-include(reactors-java-reactors-custom-scheduler.html)!*/

    try {
      Assert.assertEquals("Ohayo", System.out.queue.take());
    } catch (Exception e) {
      throw new RuntimeException(e);
    }
  }

  /*!begin-include!*/
  /*!begin-code!*/
  public static class Pair<K, V> {
    public K k;
    public V v;
    public Pair(K k, V v) {
      this.k = k;
      this.v = v;
    }
  }

  public static class PutOnlyReactor<K, V> extends Reactor<Pair<K, V>> {
    Map<K, V> map = new HashMap<K, V>();

    public PutOnlyReactor() {
      main().events().onEvent(p -> map.put(p.k, p.v));
    }
  }
  /*!end-code!*/
  /*!end-include(reactors-java-reactors-put-only.html)!*/

  /*!begin-include!*/
  /*!begin-code!*/
  public static interface Op<K, V> {
    public void apply(Map<K, V> map);
  }

  public static class Put<K, V> implements Op<K, V> {
    public K k;
    public V v;
    public Put(K k, V v) {
      this.k = k;
      this.v = v;
    }
    public void apply(Map<K, V> map) {
      map.put(k, v);
    }
  }

  public static class Get<K, V> implements Op<K, V> {
    public K k;
    public Channel<V> ch;
    public Get(K k, Channel<V> ch) {
      this.k = k;
      this.ch = ch;
    }
    public void apply(Map<K, V> map) {
      ch.send(map.get(k));
    }
  }
  /*!end-code!*/
  /*!end-include(reactors-java-reactors-map-ops.html)!*/

  /*!begin-include!*/
  /*!begin-code!*/
  public static class MapReactor<K, V> extends Reactor<Op<K, V>> {
    Map<K, V> map = new HashMap<K, V>();

    public MapReactor() {
      main().events().onEvent(op -> op.apply(map));
    }
  }
  /*!end-code!*/
  /*!end-include(reactors-java-reactors-map-reactor.html)!*/

  @Test
  public void runsMapper() {
    /*!begin-include!*/
    /*!begin-code!*/
    Channel<Op<String, String[]>> mapper =
      system.spawn(Proto.create(MapReactor.class));
    /*!end-code!*/
    /*!end-include(reactors-java-reactors-spawn-mapper.html)!*/

    /*!begin-include!*/
    /*!begin-code!*/
    mapper.send(new Put("dns-main", new String[] { "dns1", "lan" }));
    mapper.send(new Put("dns-backup", new String[] { "dns2", "com" }));
    /*!end-code!*/
    /*!end-include(reactors-java-reactors-send-mapper.html)!*/

    try {
      Thread.sleep(1000);
    } catch (Exception e) {
      throw new RuntimeException(e);
    }

    /*!begin-include!*/
    /*!begin-code!*/
    Proto<String> clientProto = Reactor.apply(
      self -> self.main().events().onEvent(x -> {
        if (x.equals("start")) {
          Connector<String[]> reply = self.system().channels().<String[]>open();
          mapper.send(new Get("dns-main", reply.channel()));
          reply.events().onEvent(
            url -> System.out.println(url[0] + "." + url[1]));
        } else if (x.equals("end")) {
          self.main().seal();
        }
      })
    );
    Channel<String> ch = system.spawn(clientProto);
    /*!end-code!*/
    /*!end-include(reactors-java-reactors-mapper-client.html)!*/

    /*!begin-include!*/
    /*!begin-code!*/
    ch.send("start");
    /*!end-code!*/
    /*!end-include(reactors-java-reactors-mapper-client-start.html)!*/

    try {
      Assert.assertEquals("dns1.lan", System.out.queue.take());
    } catch (Exception e) {
      throw new RuntimeException(e);
    }

    /*!begin-include!*/
    /*!begin-code!*/
    ch.send("end");
    /*!end-code!*/
    /*!end-include(reactors-java-reactors-mapper-client-end.html)!*/
  }

}
