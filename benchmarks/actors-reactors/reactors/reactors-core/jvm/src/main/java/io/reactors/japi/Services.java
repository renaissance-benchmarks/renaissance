package io.reactors.japi;



import io.reactors.japi.services.Channels;
import io.reactors.japi.services.Clock;
import io.reactors.japi.services.Log;



public abstract class Services {
  private Channels channelsService;
  private Clock clockService;
  private Log logService;

  public void initServices() {
    channelsService = service(Channels.class);
    clockService = service(Clock.class);
    logService = service(Log.class);
  }

  public Channels channels() {
    return channelsService;
  }

  public Clock clock() {
    return clockService;
  }

  public Log log() {
    return logService;
  }

  public <S extends Service> S service(Class<S> cls) {
    try {
      return cls.getConstructor(ReactorSystem.class).newInstance(this);
    } catch (Throwable throwable) {
      throw new RuntimeException(throwable);
    }
  }
}
