package io.reactors.japi;






public class Scheduler {
  private io.reactors.Scheduler self;

  private Scheduler(io.reactors.Scheduler self) {
    this.self = self;
  }

  io.reactors.Scheduler getSelf() {
    return self;
  }

  public static Scheduler timer(long period, boolean isDaemon) {
    return new Scheduler(new io.reactors.JvmScheduler.Timer(period, isDaemon));
  }

  public static Scheduler timer(long period) {
    return timer(period, true);
  }

  public static final String NEW_THREAD =
    io.reactors.JvmScheduler$.MODULE$.javaKey().newThread();

  public static final String DEFAULT =
    io.reactors.JvmScheduler$.MODULE$.javaKey().defaultScheduler();

  public static final String PIGGYBACK =
    io.reactors.JvmScheduler$.MODULE$.javaKey().piggyback();

  public static final String GLOBAL_EXECUTION_CONTEXT =
    io.reactors.JvmScheduler$.MODULE$.javaKey().globalExecutionContext();
}
