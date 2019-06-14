package org.renaissance

import org.renaissance.util.BenchmarkLoader

abstract class JmhRenaissanceBenchmark {
  val config = new Config
  var benchmark: RenaissanceBenchmark = _

  protected def benchmarkName: String

  protected def defaultSetUpBeforeAll(): Unit = {
    benchmark = BenchmarkLoader.loadBenchmark(benchmarkName)
    benchmark.setUpBeforeAll(config)
  }

  protected def defaultSetUp(): Unit = {
    benchmark.beforeIteration(config)
  }

  protected def defaultTearDown(): Unit = {
    benchmark.afterIteration(config)
  }

  protected def defaultTearDownAfterAll(): Unit = {
    benchmark.tearDownAfterAll(config)
  }

  protected def defaultRun(): Unit = {
    benchmark.runIteration(config)
  }
}
