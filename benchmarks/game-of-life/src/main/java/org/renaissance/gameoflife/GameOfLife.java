package org.renaissance.gameoflife;

import java.util.ArrayList;
import java.util.List;
import java.util.Random;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.Future;
import java.util.concurrent.TimeUnit;

import org.renaissance.Benchmark;
import org.renaissance.BenchmarkContext;
import org.renaissance.BenchmarkResult;
import org.renaissance.BenchmarkResult.Validators;
import org.renaissance.License;

import static org.renaissance.Benchmark.*;

@Name("game-of-life")
@Group("functional")
@Summary("Simulates Conway-style cellular automata on a 2D grid using polymorphic rule dispatch.")
@Licenses(License.MIT)
@Repetitions(20)
@Parameter(name = "grid_size", defaultValue = "1000")
@Parameter(name = "iterations", defaultValue = "100")
@Parameter(name = "thread_count", defaultValue = "4")
@Parameter(name = "rule_count", defaultValue = "4")
@Parameter(name = "same_rule", defaultValue = "false")
@Configuration(name = "test", settings = {
  "grid_size = 100", "iterations = 10", "thread_count = 2", "rule_count = 1"
})
@Configuration(name = "jmh")
public final class GameOfLife implements Benchmark {

  private static final long SEED = 42L;

  private boolean[] grid;
  private int gridSize;
  private int iterations;
  private int threadCount;
  private int ruleCount;
  private boolean sameRule;
  private int totalCells;
  private Rule[] schedule;
  private long expectedChecksum;
  private ExecutorService executor;

  @Override
  public void setUpBeforeAll(BenchmarkContext c) {
    gridSize = c.parameter("grid_size").toInteger();
    iterations = c.parameter("iterations").toInteger();
    threadCount = c.parameter("thread_count").toInteger();
    ruleCount = c.parameter("rule_count").toInteger();
    sameRule = Boolean.parseBoolean(c.parameter("same_rule").value());
    totalCells = gridSize * gridSize;

    schedule = buildSchedule(ruleCount, sameRule, totalCells);

    grid = new boolean[totalCells];
    seedGrid(grid);

    executor = Executors.newFixedThreadPool(threadCount);

    // warm-up + checksum: run the simulation once before measurement so the
    // expected value is fixed and the JIT has a chance to compile the loop (to stabilize the measurements)
    expectedChecksum = computeChecksum(simulate(copyGrid(grid)));
  }

  @Override
  public void tearDownAfterAll(BenchmarkContext c) {
    executor.shutdown();
    try {
      executor.awaitTermination(10, TimeUnit.SECONDS);
    } catch (InterruptedException e) {
      Thread.currentThread().interrupt();
    }
  }

  @Override
  public BenchmarkResult run(BenchmarkContext c) {
    long startNs = System.nanoTime();
    boolean[] result = simulate(copyGrid(grid));
    long elapsedNs = System.nanoTime() - startNs;

    long checksum = computeChecksum(result);

    double elapsedSec = elapsedNs / 1e9;
    long updatedCells = (long) totalCells * iterations;
    double mcellsPerSec = updatedCells / elapsedSec / 1e6;
    System.out.printf(
        "game-of-life: throughput = %.2f Mcells/s "
        + "(grid_size=%d, iterations=%d, threads=%d, rule_count=%d, same_rule=%b)%n",
        mcellsPerSec, gridSize, iterations, threadCount, ruleCount, sameRule);

    return Validators.simple("checksum", expectedChecksum, checksum);
  }

  private Rule[] buildSchedule(int n, boolean useSame, int cells) {
    Rule[] palette;
    if (useSame) {
      palette = new Rule[n];
      for (int i = 0; i < n; i++) {
        palette[i] = new ConwayRule();
      }
    } else {
      Rule[] all = {
        new ConwayRule(),
        new HighLifeRule(),
        new SeedsRule(),
        new DayAndNightRule(),
        new LifeWithoutDeathRule(),
      };
      if (n < 1 || n > all.length) {
        throw new IllegalArgumentException(
            "rule_count must be between 1 and " + all.length + ", got " + n);
      }
      palette = new Rule[n];
      System.arraycopy(all, 0, palette, 0, n);
    }

    Rule[] sched = new Rule[cells];
    for (int i = 0; i < cells; i++) {
      sched[i] = palette[i % palette.length];
    }
    return sched;
  }

  private void seedGrid(boolean[] g) {
    // Deterministic seed, ~25% of cells alive.
    Random rng = new Random(SEED);
    for (int i = 0; i < totalCells; i++) {
      g[i] = rng.nextInt(4) == 0;
    }
  }

  private boolean[] copyGrid(boolean[] src) {
    boolean[] copy = new boolean[totalCells];
    System.arraycopy(src, 0, copy, 0, totalCells);
    return copy;
  }

  private boolean[] simulate(boolean[] current) {
    int activeThreads = Math.min(threadCount, totalCells);
    int chunk = totalCells / activeThreads;

    try {
      for (int iter = 0; iter < iterations; iter++) {
        boolean[] next = new boolean[totalCells];
        final boolean[] cur = current;
        final Rule[] sched = schedule;

        List<Future<?>> futures = new ArrayList<>(activeThreads);
        for (int thrdIdx = 0; thrdIdx < activeThreads; thrdIdx++) {
          final int start = thrdIdx * chunk;
          final int end = (thrdIdx != activeThreads - 1) ? start + chunk : totalCells;

          futures.add(executor.submit(() -> {
            for (int i = start; i < end; i++) {
              int neighbors = countNeighbors(cur, i);
              next[i] = sched[i].nextState(cur[i], neighbors);
            }
          }));
        }

        for (Future<?> f : futures) {
          f.get();
        }
        current = next;
      }
    } catch (Exception e) {
      throw new RuntimeException(e);
    }

    return current;
  }

  private int countNeighbors(boolean[] g, int i) {
    int row = i / gridSize;
    int col = i % gridSize;
    int count = 0;
    for (int dr = -1; dr <= 1; dr++) {
      for (int dc = -1; dc <= 1; dc++) {
        if (dr == 0 && dc == 0) continue;
        int r = row + dr;
        int c = col + dc;
        if (r >= 0 && r < gridSize && c >= 0 && c < gridSize && g[r * gridSize + c]) {
          count++;
        }
      }
    }
    return count;
  }

  private long computeChecksum(boolean[] g) {
    long sum = 0;
    for (int i = 0; i < totalCells; i++) {
      if (g[i]) {
        sum += (long) i;
      }
    }
    return sum;
  }
}
