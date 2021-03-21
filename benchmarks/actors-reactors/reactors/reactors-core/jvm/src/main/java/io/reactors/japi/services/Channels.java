package io.reactors.japi.services;



import io.reactors.japi.Channel;
import io.reactors.japi.ChannelBuilder;
import io.reactors.japi.Events;
import io.reactors.japi.ReactorSystem;
import io.reactors.japi.Service;



public class Channels extends ChannelBuilder implements Service {
  private io.reactors.services.Channels rawChannels;

  public Channels(ReactorSystem system) {
    super(system.rawSystem().channels());
    this.rawChannels = getRawService(system, io.reactors.services.Channels.class);
  }

  public <T> Events<Channel<T>> await(String reactorName, String channelName) {
    return new Events<>(rawChannels.await(reactorName, channelName))
      .map(c -> new Channel(c));
  }
}
