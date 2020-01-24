package org.renaissance.plugins.ubenchagent;

import org.renaissance.Plugin;

import java.util.Arrays;
import java.util.List;
import java.util.stream.Collectors;

import cz.cuni.mff.d3s.perf.Measurement;
import cz.cuni.mff.d3s.perf.BenchmarkResults;

public class Main implements Plugin,
    Plugin.AfterBenchmarkSetUpListener,
    Plugin.AfterOperationSetUpListener,
    Plugin.BeforeOperationTearDownListener,
    Plugin.MeasurementResultPublisher {

  final int eventSet;

  public Main(String[] args) {
    String[] events = Arrays.stream(args)
        .flatMap(a -> Arrays.stream(a.split(",")))
        .collect(Collectors.toList())
        .toArray(new String[0]);
    if (events.length == 0) {
      warn("No events specified, are you sure about this?");
      eventSet = -1;
      return;
    }

    eventSet = Measurement.createEventSet(1, events, Measurement.THREAD_INHERIT);
  }

  @Override
  public void afterBenchmarkSetUp(String benchmark) {
    Measurement.start(eventSet);
    Measurement.stop(eventSet);
  }

  @Override
  public void afterOperationSetUp(String benchmark, int opIndex, boolean isLastOp) {
    Measurement.start(eventSet);
  }

  @Override
  public void beforeOperationTearDown(String benchmark, int opIndex, long harnessDuration) {
    Measurement.stop(eventSet);
  }

  @Override
  public void onMeasurementResultsRequested(String benchmark, int opIndex, Plugin.MeasurementResultListener dispatcher) {
    BenchmarkResults results = Measurement.getResults(eventSet);
    String[] events = results.getEventNames();
    List<long[]> data = results.getData();
    if (data.size() != 1) {
      warn("Ignoring invalid data from this loop.");
      return;
    }
    long[] values = data.get(0);
    if (values.length != events.length) {
      warn("Ignoring invalid data from this loop.");
      return;
    }
    for (int i = 0; i < values.length; i++) {
      dispatcher.onMeasurementResult(benchmark, "ubench_agent_" + events[i], values[i]);
    }
  }

  private void warn(String msg, Object... args) {
    System.out.printf("[ubench plugin] WARNING: " + msg + "\n", args);
  }
}

