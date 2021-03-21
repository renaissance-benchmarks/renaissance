package io.reactors.japi;






public class Proto<T> {
  public static <T, I extends Reactor<T>> Proto<T> create(Class<I> cls, Object... as) {
    return new Proto(cls, as);
  }

  public static class ProxyReactor<T> extends io.reactors.Reactor.Abstract<T> {
    public ProxyReactor(Class<?> cls, Object... as) {
      try {
        io.reactors.Platform$.MODULE$.javaReflect().instantiate(cls, as);
      } catch (Exception e) {
        throw new RuntimeException(e);
      }
    }
  }

  private io.reactors.Proto<io.reactors.Reactor<T>> self;

  io.reactors.Proto<io.reactors.Reactor<T>> getOriginal() {
    return self;
  }

  public Proto<T> withName(String name) {
    return new Proto(self.withName(name));
  }

  public Proto<T> withScheduler(String name) {
    return new Proto(self.withScheduler(name));
  }

  public Proto<T> withChannelName(String name) {
    return new Proto(self.withChannelName(name));
  }

  public Proto<T> withTransport(String name) {
    return new Proto(self.withTransport(name));
  }

  private Proto(io.reactors.Proto<io.reactors.Reactor<T>> self) {
    this.self = self;
  }

  private Proto(Class<?> cls, Object... as) {
    Object[] args = new Object[] {cls, as};
    this.self = io.reactors.Proto.apply(ProxyReactor.class, args);
  }
}
