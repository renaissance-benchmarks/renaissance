package io.reactors.japi;






public class Channel<T> {
  private io.reactors.Channel<T> self;

  public Channel(io.reactors.Channel<T> self) {
    this.self = self;
  }

  public void send(T event) {
    this.self.send(event);
  }
}
