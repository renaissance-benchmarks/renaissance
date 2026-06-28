package org.renaissance.scala.stm

import org.renaissance.Benchmark
import org.renaissance.Benchmark._
import org.renaissance.BenchmarkContext
import org.renaissance.BenchmarkResult
import org.renaissance.BenchmarkResult.Validators
import org.renaissance.BenchmarkResult.Assert
import org.renaissance.License

@Name("scala-stm-bench7")
@Group("scala-stm")
@Group("scala")
@Summary("Runs the stmbench7 benchmark using ScalaSTM.")
@Licenses(Array(License.BSD3, License.GPL2))
@Repetitions(60)
@Parameter(
  name = "thread_count",
  defaultValue = "$cpu.count",
  summary = "Number of worker threads to use"
)
@Parameter(
  name = "operation_count",
  defaultValue = "20",
  summary = "Number of operations to perform"
)
@Configuration(name = "test")
@Configuration(name = "jmh")
final class ScalaStmBench7 extends Benchmark {

  // TODO: Consolidate benchmark parameters across the suite.
  //  See: https://github.com/renaissance-benchmarks/renaissance/issues/27

  /**
   * The STMBench7 benchmark instance.
   * Initialized once in setUpBeforeAll, reused across iterations.
   */
  private var stmBench: stmbench7.Benchmark = _

  /** Number of threads to use */
  private var threadCount: Int = _

  /**
   * Duration in seconds (unused when operationCount > 0).
   *
   * Not used, operationCount preferred.
   */
  private var numSeconds: Int = _

  /** Number of operations per thread per iteration */
  private var operationCount: Int = _

  /** Workload type: "r" (read-dominated), "rw" (read-write), "w" (write-dominated) */
  private val Workload: String = "rw"

  /** Synchronization type */
  private val synchType: stmbench7.Parameters.SynchronizationType =
    stmbench7.Parameters.SynchronizationType.STM

  /** Full class name of STM initializer */
  private val StmInitializer: String = "stmbench7.scalastm.ScalaSTMInitializer"

  /** Enable long traversal operations */
  private val LongTraversalsEnabled: Boolean = true

  /** Enable structural modification operations */
  private val StructureModificationEnabled: Boolean = true


  private var SequentialReplayEnabled: Boolean = true

  /** Whether to check opacity after each iteration */
  private val CheckOpacity: Boolean = true

  override def setUpBeforeAll(c: BenchmarkContext): Unit = {
    // Parse params
    threadCount = c.parameter("thread_count").toPositiveInteger
    operationCount = c.parameter("operation_count").toPositiveInteger

    // Initialize the random number generator phase


    // Create the benchmark instance with all configuration.
    stmBench = new stmbench7.Benchmark(
      threadCount,                  // numThreads
      numSeconds,                   // numSeconds (unused when countOfOperations > 0)
      operationCount,               // countOfOperations
      Workload,                     // workload: "r", "rw", or "w"
      synchType,                    // synchronizationType enum
      StmInitializer,               // STM initializer class
      LongTraversalsEnabled,        // longTraversalsEnabled
      StructureModificationEnabled, // structureModificationEnabled
      SequentialReplayEnabled       // sequentialReplayEnabled
    )
  }

  override def setUpBeforeEach(c: BenchmarkContext): Unit = {
    // Reset thread state for a fresh iteration.
    // This recreates BenchThread instances with zeroed counters
    // while reusing the expensive Setup data structure.
    stmBench.resetForNextIteration()
    stmBench.setupClone = null

    // Create initial clone
    // This must be done before start() so we have a copy of the initial state.
    if (SequentialReplayEnabled && CheckOpacity) {
      stmBench.createInitialClone()
    }
  }



  override def run(c: BenchmarkContext): BenchmarkResult = {

    stmBench.start()

    () => {
      val result = stmBench.validateInvariants(false)
      Assert.assertEquals(true, result.invariantsValid, "invariants valid")
      Assert.assertEquals(true, result.successfulOperations > 0, "successful_ops > 0")

      if (CheckOpacity) {
        val opacityResult = stmBench.checkOpacity()
        Assert.assertEquals(true, opacityResult, "opacity check")
      }
    }
  }
  

  override def tearDownAfterAll(c: BenchmarkContext): Unit = {
    // Clean up
    stmBench = null
  }
}