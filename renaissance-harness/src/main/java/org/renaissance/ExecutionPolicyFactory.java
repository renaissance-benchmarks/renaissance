package org.renaissance;

import org.renaissance.core.BenchmarkInfo;

import static java.util.concurrent.TimeUnit.SECONDS;

enum ExecutionPolicyFactory {
  FIXED_OP_COUNT {
    @Override
    ExecutionPolicy create(Config config, BenchmarkInfo benchInfo) {
        return create (
          config.repetitions > 0 ? config.repetitions : benchInfo.repetitions()
        );
    }

    private ExecutionPolicy create(final int count) {
      return new ExecutionPolicy() {
        private int executedCount = 0;

        @Override
        public boolean keepExecuting() {
          return executedCount < count;
        }

        @Override
        public void registerOperation(int index, long duration) {
          executedCount = index + 1;
        }

        @Override
        public boolean isLastOperation() { return executedCount + 1 >= count; }
      };
    }

  },

  FIXED_OP_TIME {
    @Override
    ExecutionPolicy create(Config config, BenchmarkInfo benchInfo) {
      return create (SECONDS.toNanos(config.runSeconds));
    }

    private ExecutionPolicy create(long elapsedNanosLimit) {
      return new ExecutionPolicy() {
        private long elapsedNanos = 0;
        private int elapsedCount = 0;

        @Override
        public boolean keepExecuting() { return !isElapsed() || isLastOperation(); }

        private boolean isElapsed() { return elapsedNanos >= elapsedNanosLimit; }

        @Override
        public void registerOperation(int index, long durationNanos) {
          elapsedNanos += durationNanos;
          elapsedCount += isElapsed() ? 1 : 0;
        }

        @Override
        public boolean isLastOperation() { return elapsedCount == 1; }
      };
    }

  },

  FIXED_TIME {
    @Override
    ExecutionPolicy create(Config config, BenchmarkInfo benchInfo) {
      return create (SECONDS.toNanos(config.runSeconds));
    }

    private ExecutionPolicy create(long elapsedNanosLimit) {
      return new ExecutionPolicy() {
        private long lastNanos = -1;
        private long elapsedNanos = 0;
        private int elapsedCount = 0;

        @Override
        public boolean keepExecuting() { return !isElapsed() || isLastOperation(); }

        private boolean isElapsed() { return elapsedNanos >= elapsedNanosLimit; }

        @Override
        public void registerOperation(int index, long durationNanos) {
          final long currentNanos = System.nanoTime();

          if (lastNanos < 0) {
            lastNanos = currentNanos - durationNanos;
          }

          elapsedNanos += currentNanos - lastNanos;
          elapsedCount += isElapsed() ? 1 : 0;
        }

        @Override
        public boolean isLastOperation() { return elapsedCount == 1; }
      };
    }
  },

  CUSTOM {
    @Override
    ExecutionPolicy create(Config config, BenchmarkInfo benchInfo) {
      throw new UnsupportedOperationException("not yet implemented");
    }
  };

  abstract ExecutionPolicy create (Config config, BenchmarkInfo benchInfo);

}
