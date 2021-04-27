package io.reactors.japi.services;



import io.reactors.japi.ReactorSystem;
import io.reactors.japi.Service;



public class Log implements Service {
  private io.reactors.services.Log rawLog;

  public Log(ReactorSystem system) {
    this.rawLog = getRawService(system, io.reactors.services.Log.class);
  }

  public void info(Object obj) {
    rawLog.apply().apply(obj);
  }
}
