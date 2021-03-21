package io.reactors
package http



import io.reactors.test._
import java.io.ByteArrayInputStream
import org.openqa.selenium._
import org.openqa.selenium.chrome._
import org.openqa.selenium.interactions._
import org.openqa.selenium.support.ui._
import org.scalatest._
import scala.collection.JavaConverters._
import org.scalatest.funsuite.AnyFunSuite



class HttpTest extends AnyFunSuite {
  test("test basic http scenarios") {
    runXvfbTest("io.reactors.http.HttpTest", Some("../target/videos"))
  }
}


object HttpTest {
  def main(args: Array[String]) {
    // Initialize driver.
    System.setProperty("webdriver.chrome.driver", "../tools/chromedriver")
    val options = new ChromeOptions
    options.setBinary("/usr/bin/chromium-browser")
    val driver = new ChromeDriver(options)

    // Initialize http server.
    val config = ReactorSystem.customConfig("")
    val bundle = new ReactorSystem.Bundle(JvmScheduler.default, config)
    val system = new ReactorSystem("http-test-system", bundle)

    val server = Reactor[Unit] { self =>
      self.system.service[Http].seq(9500).text("/test-text") { req =>
        Events("Test text.")
      }
      self.system.service[Http].seq(9500).resource("/test-file")("text/javascript") {
        req =>
        Events(new ByteArrayInputStream("var js = 'Test script.';".getBytes))
      }
    }
    system.spawn(server)

    var error: Throwable = null
    try {
      // Run tests.
      runTests(driver, system)
    } catch {
      case t: Throwable =>
        t.printStackTrace()
        error = t
    } finally {
      // Quit.
      Thread.sleep(1000)
      driver.quit()
      system.shutdown()
      Thread.sleep(1000)
      if (error == null) System.exit(0)
      else System.exit(1)
    }
  }

  def runTests(driver: WebDriver, system: ReactorSystem) {
    Thread.sleep(1500)

    driver.get("localhost:9500/test-text")
    assert(driver.getPageSource.contains("Test text."))

    Thread.sleep(1500)

    driver.get("localhost:9500/test-file")
    assert(driver.getPageSource.contains("var js = 'Test script.';"))
  }
}
