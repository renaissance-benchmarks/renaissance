package io.reactors.japi;



import io.reactors.SysEvent;
import java.util.function.Consumer;



public abstract class Reactor<T> {
  private io.reactors.concurrent.Frame frame;
  private ReactorSystem system;
  private Connector<T> defaultConnector;

  public Reactor() {
    frame = io.reactors.Reactor$.MODULE$.currentFrame();
    system = ReactorSystem.from(frame.reactorSystem());
    defaultConnector = new Connector(frame.defaultConnector());
  }

  public ReactorSystem system() {
    return system;
  }

  public long uid() {
    return frame.uid();
  }

  public Connector<T> main() {
    return defaultConnector;
  }

  public Events<SysEvent> sysEvents() {
    return new Events(frame.reactor().sysEvents());
  }

  private static class AnonymousReactor<T> extends Reactor<T> {
    public AnonymousReactor(Consumer<Reactor<T>> c) {
      c.accept(this);
    }
  }

  public static <T> Proto<T> apply(Consumer<Reactor<T>> c) {
    return Proto.create(AnonymousReactor.class, c);
  }
}
