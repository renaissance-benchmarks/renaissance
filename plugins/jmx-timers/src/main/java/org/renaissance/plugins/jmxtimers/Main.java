package org.renaissance.plugins.jmxtimers;

import java.lang.management.CompilationMXBean;
import java.lang.management.ManagementFactory;

import org.renaissance.Plugin;

public class Main implements Plugin,
    Plugin.AfterOperationSetUpListener,
    Plugin.BeforeOperationTearDownListener,
    Plugin.MeasurementResultPublisher {

  CompilationMXBean __compilationMXBean;

  long __compilationTimeBefore;
  long __compilationTimeAfter;

  public Main() {
    __compilationMXBean = ManagementFactory.getCompilationMXBean ();
  }

  @Override
  public void afterOperationSetUp(String benchmark, int opIndex, boolean isLastOp) {
    __compilationTimeBefore = __compilationMXBean.getTotalCompilationTime ();
  }

  @Override
  public void beforeOperationTearDown(String benchmark, int opIndex, long harnessDuration) {
    __compilationTimeAfter = __compilationMXBean.getTotalCompilationTime ();
  }

  @Override
  public void onMeasurementResultsRequested(String benchmark, int opIndex, Plugin.MeasurementResultListener dispatcher) {
    dispatcher.onMeasurementResult(benchmark, "jmx_timers_compilation_total_ms", __compilationTimeAfter);
    dispatcher.onMeasurementResult(benchmark, "jmx_timers_compilation_time_ms", __compilationTimeAfter - __compilationTimeBefore);
  }
}
