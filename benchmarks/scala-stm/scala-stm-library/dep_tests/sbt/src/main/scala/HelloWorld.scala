import scala.concurrent.stm._

object HelloWorld {
  def main(args: Array[String]) {
    val x = Ref("hello world!")
    println(x.single())
  }
}
