package org.renaissance;

public interface ResultObserver {
  public void onNewResult(String benchmark, String metric, long value);
  public void onExit();
}
