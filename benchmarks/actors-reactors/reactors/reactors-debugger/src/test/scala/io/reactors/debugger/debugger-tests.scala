package io.reactors
package debugger



import io.reactors.test._
import org.openqa.selenium._
import org.openqa.selenium.chrome._
import org.openqa.selenium.interactions._
import org.openqa.selenium.support.ui._
import org.scalatest._
import scala.collection.JavaConverters._
import org.scalatest.funsuite.AnyFunSuite



class DebuggerTest extends AnyFunSuite {
  test("test basic debugger scenarios") {
    runXvfbTest("io.reactors.debugger.DebuggerTest", Some("../target/videos"))
  }
}


object DebuggerTest {
  def main(args: Array[String]) {
    // Initialize driver.
    System.setProperty("webdriver.chrome.driver", "../tools/chromedriver")
    val options = new ChromeOptions
    options.setBinary("/usr/bin/chromium-browser")
    val driver = new ChromeDriver(options)

    // Initialize debugger.
    val config = ReactorSystem.customConfig("""
      debug-api = {
        name = "io.reactors.debugger.WebDebugger"
      }
    """)
    val bundle = ReactorSystem.Bundle.default(JvmScheduler.default, config)
    val system = new ReactorSystem("web-debugger-test-system", bundle)

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
      Thread.sleep(2000)
      driver.quit()
      system.shutdown()
      Thread.sleep(1000)
      if (error == null) System.exit(0)
      else System.exit(1)
    }
  }

  def runTests(driver: WebDriver, system: ReactorSystem) {
    Thread.sleep(1500)
    driver.get("localhost:9500")

    // Run shell tests.
    runShellTests(driver, system)
  }

  def runShellTests(driver: WebDriver, system: ReactorSystem) {
    val logButton = driver.findElement(By.id("x-debugger-button-log"))

    def runShellScenario(commands: String*) {
      val shellButton = driver.findElement(By.id("x-debugger-button-shell"))
      shellButton.click()

      // Wait until the shell is ready.
      (new WebDriverWait(driver, 10)).until(new ExpectedCondition[Boolean] {
        def apply(d: WebDriver) = {
          val icon = d.findElement(By.className("x-status-badge-glow"))
          icon.getAttribute("class").split(" ").contains("x-status-badge-ok")
        }
      })

      // Create temporary reactor.
      val shellContainer = driver.findElement(By.className("x-shell-container"))
      shellContainer.click()

      def shellCommand(text: String) {
        val cmdline = driver.findElement(By.className("cmd"))
        val actions = new Actions(driver)
        actions.moveToElement(cmdline)
        actions.click()
        actions.sendKeys(text)
        actions.sendKeys(Keys.RETURN)
        actions.build().perform()
      }

      for (c <- commands) shellCommand(c)

      Thread.sleep(1000)
    }

    def waitUntil(f: WebDriver => Boolean) = {
      (new WebDriverWait(driver, 10)).until(new ExpectedCondition[Boolean] {
        def apply(d: WebDriver) = f(d)
      })
    }

    // Test that reactor creation is correctly logged.
    {
      runShellScenario(
        "val proto = Reactor[String] { self => }",
        "val ch = system.spawn(proto.withName(\"test-reactor-shell\"))"
      )
      logButton.click()
      waitUntil { driver =>
        val tdElements = driver.findElements(By.tagName("td")).asScala
        tdElements.exists(
          _.getText.matches("Reactor 'test-reactor-shell' \\(UID: .*\\) created."))
      }
    }

    // Test that event sends are logged.
    {
      runShellScenario(
        "val proto = Reactor[String] { self => self.main.events.on(self.main.seal()) }",
        "val ch = system.spawn(proto.withName(\"test-receiver\"))",
        "val proto = Reactor[String] { self => ch ! \"test\"; self.main.seal() }",
        "system.spawn(proto.withName(\"test-sender\"))"
      )
      logButton.click()
      waitUntil { driver =>
        val tdElements = driver.findElements(By.tagName("td")).asScala
        tdElements.exists(_.getText.matches(
          "Reactor 'test-receiver' \\(UID: .*\\) created."))
      }
      waitUntil { driver =>
        val tdElements = driver.findElements(By.tagName("td")).asScala
        tdElements.exists(_.getText.matches(
          "Reactor 'test-sender' \\(UID: .*\\) created."))
      }
      waitUntil { driver =>
        val tdElements = driver.findElements(By.tagName("td")).asScala
        tdElements.exists(_.getText.matches(
          "Total of 1 event\\(s\\) sent \\(from 'test-sender' to 'test-receiver'\\)."))
      }
    }

    // Wait for easier debugging.
    Thread.sleep(1000)
  }
}
