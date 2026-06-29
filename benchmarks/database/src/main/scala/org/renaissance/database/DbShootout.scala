package org.renaissance.database

import org.lmdbjava.bench.{Chronicle, MvStore, MapDb}
import org.renaissance.Benchmark
import org.renaissance.Benchmark.*
import org.renaissance.BenchmarkContext
import org.renaissance.BenchmarkResult
import org.renaissance.BenchmarkResult.Validators
import org.renaissance.License

import java.io.File
import java.net.URLClassLoader
import java.nio.file.Path
import java.nio.file.Paths
import scala.collection.Seq
import scala.util.{Random, Try}
import scala.jdk.CollectionConverters._

@Name("db-shootout")
@Group("database")
@Summary("Executes a shootout test using several in-memory databases.")
@Licenses(Array(License.APACHE2))
@Repetitions(16)
@Configuration(name = "test")
@Configuration(name = "jmh")
@Parameter(name = "thread_count", defaultValue = "$cpu.count", summary = "Number of worker threads")
@Parameter(name = "run_in_memory", defaultValue = "false", summary = "Run databases in memory instead of on disk")
@Parameter(name = "keys_per_thread", defaultValue = "100", summary = "Number of keys per thread")
@Parameter(name = "values_per_key", defaultValue = "5000", summary = "Number of value updates per key")
@Parameter(name = "delete_probability", defaultValue = "0.2", summary = "Probability that an operation deletes the key")
final class DbShootout extends Benchmark {

  /**
   * The original benchmarks are from https://github.com/lmdbjava/benchmarks
   * and have been slightly adapted.
   * For instance, the JMH dependency has been removed and the location where
   * the benchmark writes on disk has been updated to match the rest of the
   * renaissance suite.
   */
  // TODO: Consolidate benchmark parameters across the suite.
  //  See: https://github.com/renaissance-benchmarks/renaissance/issues/27

  //Db instances
  private var mapDb : MapDb = _
  private var mapDbWriter : MapDb.Writer = _
  private var mapDbReader : MapDb.Reader = _

  private var chronicle: Chronicle = _
  private var chronicleWriter: Chronicle.Writer = _
  private var chronicleReader: Chronicle.Reader = _

  private var mvStore: MvStore = _
  private var mvStoreWriter: MvStore.Writer = _
  private var mvStoreReader: MvStore.Reader = _

  // Parameters
  private var tempDirPath: File = _
  private var threads: Int = _
  private var keysPerThread: Int = _
  private var valuesPerKey: Int = _
  private var deleteProbability: Double = _
  private var runInMemory: Boolean = _

  // Workload data
  private var keys: Array[Array[Int]] = _ // [thread][keyIndex]
  private var values: Array[Array[Array[Int]]] = _ // [thread][keyIndex][valueSeqIndex]

  // Expected values for validation
  private var expectedCount: Long = _
  private var expectedChecksum: Long = _
  private var expectedState: Map[Int, Int] = _ // final expected state for validation

  /**
   * Generate workload data
   */
  private def generateWorkload(seed: Long): Unit = {
    val random = new Random(seed)

    keys = Array.ofDim[Int](threads, keysPerThread)
    values = Array.ofDim[Int](threads, keysPerThread, valuesPerKey)

    var expectedStateBuilder = Map.empty[Int, Int]
    var keyCounter = 0

    for (t <- 0 until threads) {
      for (k <- 0 until keysPerThread) {
        val key = keyCounter
        keyCounter += 1
        keys(t)(k) = key

        var currentValue: Option[Int] = None  // deleted or never written

        for (v <- 0 until valuesPerKey) {
          val value = if (random.nextDouble() < deleteProbability) {
            -1
          } else {
            random.nextInt(Int.MaxValue)
          }
          values(t)(k)(v) = value


          // Track current state for expected result
          if (value == -1) {
            currentValue = None  // deleted
          } else {
            currentValue = Some(value)  // written
          }
        }

        if (currentValue.isDefined)  {
          expectedStateBuilder = expectedStateBuilder + (key -> currentValue.get)
        }
      }
    }

    expectedState = expectedStateBuilder

    // Precompute expected values
    expectedCount = expectedState.size
    expectedChecksum = expectedState.toSeq.sorted.foldLeft(0L) {
      case (acc, (k, v)) => acc * 31 + k * 17 + v
    }

    val totalKeys = threads * keysPerThread
    val totalOperations = totalKeys * valuesPerKey
    val deletedKeys = totalKeys - expectedState.size

    println(s"[DbShootout] Workload generated:")
    println(s"  Threads: $threads")
    println(s"  Keys per thread: $keysPerThread")
    println(s"  Values per key: $valuesPerKey")
    println(s"  Total keys: $totalKeys")
    println(s"  Total operations: $totalOperations")
    println(s"  Delete probability: $deleteProbability")
    println(s"  Deleted keys: $deletedKeys")
    println(s"  Expected final entries: ${expectedState.size}")
  }

  /*
    * Compute checksum from Java Map
  */
  private def computeChecksum(state: java.util.Map[Integer, Integer]): Long = {
    state.asScala.toSeq.sortBy(_._1.intValue()).foldLeft(0L) {
      case (acc, (k, v)) => acc * 31 + k.intValue() * 17 + v.intValue()
    }
  }

  private def buildChronicleClassPath(classPath: String): Seq[Path] = {
    val elements = classPath.split(File.pathSeparatorChar).map(Paths.get(_)).toSeq
    Thread.currentThread.getContextClassLoader match {
      case ucl: URLClassLoader =>
        ucl.getURLs.map(url => Paths.get(url.toURI)).filter { path =>
          val fn = path.getFileName.toString
          fn.startsWith("chronicle-core") || fn.startsWith("chronicle-bytes")
        }
      case _ =>
        // Fall back to current class path.
        // This should be the case in standalone mode.
        elements
    }
  }

  private def newDbInstances(): Unit = {
    mapDb = MapDb.setup(tempDirPath, threads, false)
    mapDbWriter = mapDb.createWriter()
    mapDbReader = mapDb.createReader()
  }

  private def newChronicleInstances(): Unit = {
    //
    // Chronicle needs the 'java.class.path' property to contain certain jars because
    // it is using the Java compiler to compile generated source code and expects the
    // compiler to find libraries through the normal class path. It is enough to set
    // the property during initialization.
    //

    val oldClassPath = System.getProperty("java.class.path")
    val newClassPath = buildChronicleClassPath(oldClassPath).mkString(File.pathSeparator)
    System.setProperty("java.class.path", newClassPath)
    val totalKeys = threads * keysPerThread
    chronicle = Chronicle.setup(tempDirPath, threads, Integer.BYTES, totalKeys, runInMemory)
    chronicleWriter = chronicle.createWriter()
    chronicleReader = chronicle.createReader()
    System.setProperty("java.class.path", oldClassPath)
  }

  private def newMvStoreInstances(): Unit = {
    mvStore = MvStore.setup(tempDirPath, threads, false)
    mvStoreWriter = mvStore.createWriter()
    mvStoreReader = mvStore.createReader()
  }

  override def setUpBeforeAll(c: BenchmarkContext): Unit = {
    //Common Parts
    tempDirPath = c.scratchDirectory().toFile
    threads = c.parameter("thread_count").toPositiveInteger
    keysPerThread = c.parameter("keys_per_thread").toPositiveInteger
    valuesPerKey = c.parameter("values_per_key").toPositiveInteger
    deleteProbability = c.parameter("delete_probability").value().toDouble

    runInMemory = c.parameter("run_in_memory").toBoolean

    require(deleteProbability >= 0 && deleteProbability <= 1,
      "delete_probability must be between 0 and 1")

    generateWorkload(42L)
  }

  override def setUpBeforeEach(context: BenchmarkContext): Unit = {
    newDbInstances()
    newChronicleInstances()
    newMvStoreInstances()
  }

  override def tearDownAfterEach(context: BenchmarkContext): Unit = {
    mapDbWriter.shutdown()
    mapDbReader.shutdown()
    chronicleWriter.shutdown()
    chronicleReader.shutdown()
    mvStoreWriter.shutdown()
    mvStoreReader.shutdown()
    mapDb.close(true)
    chronicle.close(true)
    mvStore.close(true)
  }

  override def run(c: BenchmarkContext): BenchmarkResult = {

    mapDbWriter.write(keys, values)
    val mapDbActual = mapDbReader.read(keys)

    chronicleWriter.write(keys, values)
    val chronicleActual = chronicleReader.read(keys)

    mvStoreWriter.write(keys, values)
    val mvStoreActual = mvStoreReader.read(keys)

    Validators.compound(
      Validators.simple("MapDB entry count", expectedCount, mapDbActual.size()),
      Validators.simple("MapDB checksum", expectedChecksum, computeChecksum(mapDbActual)),

      Validators.simple("Chronicle entry count", expectedCount, chronicleActual.size()),
      Validators.simple("Chronicle checksum", expectedChecksum, computeChecksum(chronicleActual)),

      Validators.simple("MvStore entry count", expectedCount, mvStoreActual.size()),
      Validators.simple("MvStore checksum", expectedChecksum, computeChecksum(mvStoreActual))
    )
  }
}