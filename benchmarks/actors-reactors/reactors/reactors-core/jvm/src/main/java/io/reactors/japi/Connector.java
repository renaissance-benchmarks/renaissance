package io.reactors.japi;






public class Connector<T> {
  private io.reactors.Connector<T> self;
  private Events<T> events;
  private Channel<T> channel;

  Connector(io.reactors.Connector<T> self) {
    this.self = self;
    this.events = new Events(self.events());
    this.channel = new Channel(self.channel());
  }

  public Events<T> events() {
    return events;
  }

  public Channel<T> channel() {
    return channel;
  }

  public long uid() {
    return self.uid();
  }

  public boolean seal() {
    return self.seal();
  }
}
