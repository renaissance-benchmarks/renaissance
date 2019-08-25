package org.renaissance.harness;

import org.renaissance.Plugin.OperationSetUpListener;
import org.renaissance.Plugin.OperationTearDownListener;

import java.util.concurrent.TimeUnit;

final class ExecutionPlugins {

  static OperationSetUpListener forceGcBeforeOperationPlugin() {
    return (benchmark, opIndex, isLastOp) -> {
      System.out.println("Forcing GC before measured operation.");
      RuntimeHelper.singleton.collectGarbage();
    };
  }


  static OperationTearDownListener forceGcAfterOperationPlugin() {
    return (benchmark, opIndex, isLastOp) -> {
      System.out.println("Forcing GC after measured operation.");
      RuntimeHelper.singleton.collectGarbage();
    };
  }


  private static final class RuntimeHelper {
    private static final RuntimeHelper singleton = new RuntimeHelper();

    private static final int FORCED_GC_LOOPS_LIMIT = 10;
    private static final int FORCED_GC_DELAY_SECONDS = 1;

    private final Runtime runtime = Runtime.getRuntime();

    private long getHeapSize() {
      return runtime.totalMemory() - runtime.freeMemory();
    }

    private void triggerCollection() {
      runtime.runFinalization();
      runtime.gc();
    }

    long collectGarbage() {
      final long initialSize = getHeapSize();

      try {
        GC_LOOP: for (int i = 0; i < FORCED_GC_LOOPS_LIMIT; i++) {
          final long sizeBefore = getHeapSize();
          triggerCollection();

          TimeUnit.SECONDS.sleep(FORCED_GC_DELAY_SECONDS);

          if (getHeapSize() >= sizeBefore) {
            break GC_LOOP;
          }
        }

      } catch (InterruptedException e) {
        // Stop trying to shrink the heap.
      }

      return initialSize - getHeapSize();
    }
  }

}
