package io.reactors.japi;



import java.util.function.BiFunction;
import java.util.function.Consumer;
import java.util.function.Function;
import java.util.function.Predicate;



public class Events<T> {
  io.reactors.Events<T> self;

  public Events(io.reactors.Events<T> self) {
    this.self = self;
  }

  public void onEvent(Consumer<T> c) {
    self.onEvent(Util.toScalaFunction(c));
  }

  public void onReaction(Observer<T> observer) {
    self.onReaction(observer.self);
  }

  public void onEventOrDone(Consumer<T> c, Runnable r) {
    self.onEventOrDone(Util.toScalaFunction(c), Util.toScalaFunction(r));
  }

  public void onDone(Runnable r) {
    self.onDone(Util.toScalaFunction(r), null);
  }

  public void onExcept(Consumer<Throwable> c) {
    self.onExcept(Util.toScalaPartialFunction(c));
  }

  public <S> Events<S> map(Function<T, S> f) {
    return new Events(self.map(Util.toScalaFunction(f)));
  }

  public <S> Events<S> scanPast(S zero, BiFunction<S, T, S> f) {
    return new Events(self.scanPast(zero, Util.toScalaFunction(f)));
  }

  public Events<T> filter(Predicate<T> p) {
    return new Events(self.filter(Util.toScalaFunction(p)));
  }

  public Events<T> take(int n) {
    return new Events(self.take(n));
  }

  public Events<T> drop(int n) {
    return new Events(self.drop(n));
  }

  public Events<T> union(Events<T> that) {
    return new Events(self.union(that.self));
  }

  public static <T> Events<T> toMux(Events<Events<T>> e) {
    return new Events(io.reactors.Events$.MODULE$.mux(e.map(n -> n.self).self));
  }

  public static <T> Events<T> toUnion(Events<Events<T>> e) {
    return new Events(io.reactors.Events$.MODULE$.union(e.map(n -> n.self).self));
  }

  public static <T> Events<T> never() {
    return new Events(io.reactors.Events$.MODULE$.never());
  }

  public static <T> Events.Emitter<T> emitter() {
    return new Events.Emitter(new io.reactors.Events.Emitter<T>());
  }

  public static class Emitter<T> extends Events<T> {
    private io.reactors.Events.Emitter<T> self;

    Emitter(io.reactors.Events.Emitter<T> self) {
      super(self);
      this.self = self;
    }

    public void react(T x) {
      self.react(x);
    }

    public void except(Throwable t) {
      self.except(t);
    }

    public void unreact() {
      self.unreact();
    }
  }
}
