package io.reactors.japi;



import java.util.function.Consumer;



public abstract class Observer<T> {
  io.reactors.Observer<T> self;

  Observer(io.reactors.Observer<T> self) {
    this.self = self;
  }

  public void react(T value, Object hint) {
    self.react(value, hint);
  }

  public void except(Throwable t) {
    self.except(t);
  }

  public void unreact() {
    self.unreact();
  }

  public static <T> Observer<T> create(
    Consumer<T> onEvent, Consumer<Throwable> onExcept, Runnable onUnreact
  ) {
    io.reactors.Observer<T> self = io.reactors.Observer$.MODULE$.apply(
      Util.toScalaFunction(onEvent),
      Util.toScalaFunction(onExcept),
      Util.toScalaFunction(onUnreact));
    return new Observer(self) {};
  }
}
