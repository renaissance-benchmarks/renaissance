package io.reactors.japi;






public class ChannelBuilder {
  private io.reactors.ChannelBuilder self;

  public ChannelBuilder(io.reactors.ChannelBuilder self) {
    this.self = self;
  }

  public ChannelBuilder daemon() {
    return new ChannelBuilder(self.daemon());
  }

  public ChannelBuilder named(String name) {
    return new ChannelBuilder(self.named(name));
  }

  public <Q> Connector<Q> open() {
    return new Connector<Q>(self.open(Util.<Q>arrayable()));
  }
}
