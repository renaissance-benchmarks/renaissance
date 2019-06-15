import java.io.File
import java.nio.charset.StandardCharsets
import org.renaissance.License
import sbt.io.IO
import sbt.util.Logger

object RenaissanceJmh {

  def generateJmhWrapperBenchmarkClass(
    name: String,
    packageName: String,
    outputDir: File
  ): File = {
    val content = s"""
     package $packageName;

     import java.util.concurrent.TimeUnit;
     import org.openjdk.jmh.annotations.*;
     import org.renaissance.RenaissanceBenchmark;
     import org.renaissance.JmhRenaissanceBenchmark;

     @State(Scope.Benchmark)
     @OutputTimeUnit(TimeUnit.MILLISECONDS)
     public class Jmh_$name extends JmhRenaissanceBenchmark {
       public String benchmarkName() {
           return RenaissanceBenchmark.kebabCase("$name");
       }

       @Setup(Level.Trial)
       public void setUpBeforeAll() {
         defaultSetUpBeforeAll();
       }

       @Setup(Level.Iteration)
       public void setUp() {
         defaultSetUp();
       }

       @TearDown(Level.Iteration)
       public void tearDown() {
         defaultTearDown();
       }

       @TearDown(Level.Trial)
       public void tearDownAfterAll() {
         defaultTearDownAfterAll();
       }

       @Benchmark
       @BenchmarkMode(Mode.AverageTime)
       @OutputTimeUnit(TimeUnit.MILLISECONDS)
       @Measurement(timeUnit = TimeUnit.MILLISECONDS)
       public void run() {
         defaultRun();
       }
     }
   """
    val outputPackageDir =
      new File(outputDir.toString + "/" + packageName.split("\\.").mkString("/"))
    outputPackageDir.mkdirs()
    val outputFile = new File(outputPackageDir, "Jmh_" + name + ".java")
    IO.write(outputFile, content, StandardCharsets.UTF_8)
    outputFile
  }

  def generateJmhWrapperBenchmarkClasses(
    outputDir: File,
    logger: Logger,
    nonGpl: Boolean,
    groupJars: Seq[(String, Seq[File], Seq[File])]
  ) = {
    val perProjectBenchmarkClasses = for ((project, allJars, loadedJars) <- groupJars) yield {
      // Scan project jars for benchmarks and fill the property file.
      logger.info(s"Generating JMH wrappers for project $project")
      for {
        info <- Benchmarks.listBenchmarks(allJars, None)
        if !nonGpl || info.distro() == License.MIT
      } yield {
        generateJmhWrapperBenchmarkClass(
          info.benchClass.getSimpleName,
          info.benchClass.getPackage.getName,
          outputDir
        )
      }
    }

    perProjectBenchmarkClasses.flatten
  }
}
