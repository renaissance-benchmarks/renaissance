package org.renaissance.jdk.streams

import org.renaissance.Benchmark
import org.renaissance.Benchmark._
import org.renaissance.BenchmarkContext
import org.renaissance.BenchmarkResult
import org.renaissance.BenchmarkResult.Validators
import org.renaissance.License

@Name("par-mnemonics")
@Group("jdk-streams")
@Summary("Solves the phone mnemonics problem using parallel JDK streams.")
@Licenses(Array(License.MIT))
@Repetitions(16)
@Parameter(name = "coder_input", defaultValue = "72252762577225276257528249849874238824")
@Parameter(name = "expected_hash", defaultValue = "72b6f7d83bc807c0")
@Configuration(
  name = "test",
  settings = Array("coder_input = 7225276257722527", "expected_hash = b789f159108bb450")
)
@Configuration(name = "jmh")
final class ParMnemonics extends Benchmark {

  private var coderInputParam: String = _

  private var expectedHashParam: String = _

  private var coder: MnemonicsCoderWithStream = _

  override def setUpBeforeAll(c: BenchmarkContext): Unit = {
    coderInputParam = c.parameter("coder_input").value
    expectedHashParam = c.parameter("expected_hash").value

    // TODO Unify Mnemonics and ParMnemonics setup
    coder = new MnemonicsCoderWithStream(
      java.util.Arrays.asList(
        "Scala",
        "rocks",
        "Pack",
        "brocks",
        "GWT",
        "implicit",
        "nice",
        "ScalaGWT",
        "cat",
        "EFPL",
        "Lausanne",
        "sCala",
        "ROcks",
        "pAck",
        "Java",
        "Apple",
        "Google",
        "Rochester",
        "Utah",
        "Rice",
        "wyr",
        "lxm",
        "q",
        "w",
        "e",
        "r",
        "t",
        "y",
        "u",
        "i",
        "o",
        "p",
        "a",
        "s",
        "d",
        "f"
      )
    )
  }

  override def run(c: BenchmarkContext): BenchmarkResult = {
    val result = coder.parallelTranslate(coderInputParam)
    Validators.hashing(expectedHashParam, result)
  }
}
