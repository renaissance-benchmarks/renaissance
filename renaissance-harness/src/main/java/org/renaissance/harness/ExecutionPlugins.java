package org.renaissance.harness;

import org.renaissance.Plugin.AfterOperationSetUpListener;

import java.util.Formatter;
import java.util.Locale;

final class ExecutionPlugins {

  static final class ForceGcPlugin implements AfterOperationSetUpListener {
    private final Runtime runtime = Runtime.getRuntime();

    @Override
    public void afterOperationSetUp(String benchmark, int opIndex, boolean isLastOp) {
      collectGarbage("before operation");
    }

    private void collectGarbage(String occasion) {
      final long startHeapSize = heapSize();
      final long startTime = System.nanoTime();
      runtime.runFinalization();
      runtime.gc();
      final long durationNanos = System.nanoTime() - startTime;
      final long endHeapSize = heapSize();

      System.out.printf(
        (Locale) null,
        "GC %s: completed in %.3f ms, heap usage %s -> %s.\n",
        occasion, durationNanos / 1e6,
        humanFormat("%.3f", " %sB", startHeapSize),
        humanFormat("%.3f", " %sB", endHeapSize)
      );
    }

    private long heapSize() {
      return runtime.totalMemory() - runtime.freeMemory();
    }

    private static String humanFormat(String numberFormat, String unitFormat, long value) {
      final Formatter result = new Formatter();

      final int unit = (Long.SIZE - Long.numberOfLeadingZeros(value) - 1) / 10;
      if (unit > 0) {
        final long granularity = 1L << (unit * 10);
        result.format(numberFormat, (double) value / granularity);
        result.format(unitFormat, "KMGTPE".charAt(unit - 1));
      } else {
        result.format("%d", value);
        result.format(unitFormat, "");
      }

      return result.toString();
    }

  }

}
