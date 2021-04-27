package io.reactors



import java.io._
import java.time.LocalDateTime
import java.time.format.DateTimeFormatter
import java.util.UUID
import org.scalacheck._
import org.scalacheck.Gen._
import org.scalacheck.Prop._
import scala.collection._
import scala.concurrent.Await
import scala.concurrent.Promise
import scala.concurrent.duration.Duration
import scala.io.Source
import scala.sys.process._



package test {

  trait ExtendedProperties {
    val deterministicRandom = new scala.util.Random(24)

    def detChoose(low: Int, high: Int): Gen[Int] = {
      if (low > high) fail
      else {
        def draw() = {
          low + math.abs(deterministicRandom.nextInt()) % (1L + high - low)
        }
        const(0).map(_ => math.max(low, math.min(high, draw().toInt)))
      }
    }

    def detChoose(low: Double, high: Double): Gen[Double] = {
      if (low > high) fail
      else {
        def draw() = {
          low + deterministicRandom.nextDouble() * (high - low)
        }
        const(0).map(_ => math.max(low, math.min(high, draw())))
      }
    }

    def detOneOf[T](gens: Gen[T]*): Gen[T] = for {
      i <- detChoose(0, gens.length - 1)
      x <- gens(i)
    } yield x

    def thread[U](body: =>U): Thread = {
      val t = new Thread {
        override def run(): Unit = {
          try body
          catch {
            case t: Throwable =>
              t.printStackTrace()
              throw t
          }
        }
      }
      t.start()
      t
    }
  }

}


package object test {
  def stackTraced[T](p: =>T): T = {
    try {
      p
    } catch {
      case t: Throwable =>
        t.printStackTrace()
        throw t
    }
  }

  private val debugDelays = mutable.Map[AnyRef, AnyRef]()

  def delayTest(obj: AnyRef, millis: Int = 5000): Unit = debugDelays.get(obj) match {
    case Some(_) => // Already initialized.
    case None =>
      debugDelays(obj) = new AnyRef {
        Thread.sleep(millis)
      }
  }

  val osName = {
    val osName = System.getProperty("os.name")
    if (osName == null) ""
    else osName.toLowerCase
  }

  def isLinuxOs: Boolean = osName.contains("nux")

  def isMacOs: Boolean = osName.contains("mac")

  def isWinOs: Boolean = osName.contains("win")

  def runXvfbTest(mainClass: String, recordTo: Option[String] = None): Unit = {
    if (isLinuxOs) {
      if (!sys.env.contains("TRAVIS")) {
        val cwd = new File(".")
        val classpath = System.getProperty("java.class.path")
        val res = "1600x900"
        val servernum = 44
        val xvfbCmd = Seq(
          "xvfb-run", "--listen-tcp", "--server-num", s"$servernum",
          // The --auth-file option seems to be broken, use -f instead.
          "-f", s"${sys.env("HOME")}/.Xauthority",
          "-s", s"-screen 0 ${res}x16",
          "java", "-cp", classpath, mainClass)
        val xvfb = Process(xvfbCmd, cwd).run()
        Thread.sleep(1000)
        val ffmpeg = recordTo.map { dir =>
          val dirFile = new File(dir)
          if (!dirFile.exists) dirFile.mkdirs()
          val nowTime = DateTimeFormatter.ofPattern("yyyy-MM-dd-HH-mm-ss").format(
            LocalDateTime.now())
          val buildId = sys.env.getOrElse("CI_BUILD_ID", "no-build-id")
          val videoFileName =
            s"$dir/test.$buildId.$mainClass.$nowTime-${UUID.randomUUID()}.mp4"
          println("Video file name: " + new File(videoFileName).getAbsolutePath)
          val ffmpegCmd = Seq(
            "ffmpeg", "-loglevel", "panic",
            "-f", "x11grab", "-video_size", res,
            "-i", s"127.0.0.1:$servernum.0", "-codec:v", "libx264", "-r", "24",
            videoFileName)
          val readyToKill = Promise[Boolean]()
          val io = new ProcessIO(
            in => {
              Await.ready(readyToKill.future, Duration.Inf)
              println("Sending quit signal.")
              val writer = new PrintWriter(in)
              writer.print("q")
              writer.flush()
            },
            out => Source.fromInputStream(out).getLines.foreach(println),
            err => Source.fromInputStream(err).getLines.foreach(println))
          (readyToKill, Process(ffmpegCmd, cwd).run(io))
        }
        try {
          assert(xvfb.exitValue == 0)
        } finally {
          ffmpeg.foreach { case (readyToKill, proc) =>
            readyToKill.success(true)
            assert(proc.exitValue == 0)
          }
        }
      } else println("Skipping UI test in Travis!")
    }
  }
}
