package io.reactors
package container



import io.reactors.common.QuadMatrix
import org.scalameter.api._
import org.scalameter.japi.JBench



class MatrixBench extends JBench.OfflineReport {

  class Matrix(val width: Int, val height: Int) {
    val array = new Array[Int](width * height)
    def apply(x: Int, y: Int) = array(y * width + x)
  }

  val maxIterations = 400000

  val sidelengths = Gen.range("sidelength")(500, 2500, 500)

  val matrices = for (sz <- sidelengths) yield new Matrix(sz, sz)

  val hashMatrices = for (sz <- sidelengths) yield {
    val hm = new RHashMatrix[Int]
    for (x <- 0 until sz; y <- 0 until sz) hm(x, y) = x * y + 1
    for (x <- 0 until sz; y <- 0 until sz) assert(hm(x, y) != hm.nil, hm(x, y))
    (sz, hm)
  }

  val quadMatrices = for (sz <- sidelengths) yield {
    val quad = new QuadMatrix[Int]
    for (x <- 0 until sz; y <- 0 until sz) quad(x, y) = x * y + 1
    for (x <- 0 until sz; y <- 0 until sz) assert(quad(x, y) != quad.nil, quad(x, y))
    (sz, quad)
  }

  val sparseQuadMatrices = for (sz <- sidelengths) yield {
    val k = 5
    val quad = new QuadMatrix[Int]
    for (x <- 0 until sz / k; y <- 0 until sz / k) quad(x * k, y * k) = x * y + 1
    (sz, quad)
  }

  override def defaultConfig = Context(
    exec.minWarmupRuns -> 20,
    exec.maxWarmupRuns -> 40,
    exec.benchRuns -> 64,
    exec.independentSamples -> 4
  )

  override def reporter = Reporter.Composite(
    new RegressionReporter(tester, historian),
    new MongoDbReporter[Double],
    new HtmlReporter(true)
  )

  @volatile var load = 0

  @gen("matrices")
  @benchmark("matrix.apply")
  @curve("Array")
  def matrixApply(matrix: Matrix) {
    var i = 0
    var y = 0
    while (y < matrix.height) {
      var x = 0
      while (x < matrix.width) {
        load = matrix(x, y)
        x += 1
        i += 1
        if (i > maxIterations) return
      }
      y += 1
    }
  }

  def outputHashMatrixStats(p: (Int, RHashMatrix[Int])) {
    val stats = p._2.matrix.debugBlockMap
    val collisions = stats.groupBy(_._2.length).map({ case (k, v) => (k, v.size) })
    println("collisions: " + collisions.mkString(", "))
    val numBlocks = stats.map(_._2.length).sum
    println("num blocks:" + numBlocks)
  }

  @gen("hashMatrices")
  @benchmark("matrix.apply")
  @curve("HashMatrix")
  def hashMatrixApply(p: (Int, RHashMatrix[Int])) {
    val sidelength = p._1
    val matrix = p._2
    var i = 0
    var y = 0
    while (y < sidelength) {
      var x = 0
      while (x < sidelength) {
        load = matrix(x, y)
        x += 1
        i += 1
        if (i > maxIterations) return
      }
      y += 1
    }
  }

  @gen("sparseQuadMatrices")
  @benchmark("matrix.apply")
  @curve("QuadMatrix.sparse")
  def sparseQuadMatrixApply(p: (Int, QuadMatrix[Int])) {
    val sidelength = p._1
    val quad = p._2
    var i = 0
    var y = 0
    while (y < sidelength) {
      var x = 0
      while (x < sidelength) {
        load = quad(x, y)
        x += 1
        i += 1
        if (i > maxIterations) return
      }
      y += 1
    }
  }

  @gen("quadMatrices")
  @benchmark("matrix.apply")
  @curve("QuadMatrix")
  def quadMatrixApply(p: (Int, QuadMatrix[Int])) {
    val sidelength = p._1
    val quad = p._2
    var i = 0
    var y = 0
    while (y < sidelength) {
      var x = 0
      while (x < sidelength) {
        load = quad(x, y)
        x += 1
        i += 1
        if (i > maxIterations) return
      }
      y += 1
    }
  }

  val array = new Array[Int](62500000)

  @gen("matrices")
  @benchmark("matrix.copy")
  @curve("Array")
  def matrixCopy(matrix: Matrix) {
    val len = matrix.width * matrix.height
    System.arraycopy(matrix.array, 0, array, 0, len)
  }

  @gen("hashMatrices")
  @benchmark("matrix.copy")
  @curve("HashMatrix")
  def hashMatrixCopy(p: (Int, RHashMatrix[Int])) {
    val (sidelength, matrix) = p
    matrix.copy(array, 0, 0, sidelength, sidelength)
  }

  @gen("sparseQuadMatrices")
  @benchmark("matrix.copy")
  @curve("QuadMatrix.sparse")
  def sparseQuadMatrixCopy(p: (Int, QuadMatrix[Int])) {
    val (sidelength, matrix) = p
    matrix.copy(array, 0, 0, sidelength, sidelength)
  }

  @gen("quadMatrices")
  @benchmark("matrix.copy")
  @curve("QuadMatrix")
  def quadMatrixCopy(p: (Int, QuadMatrix[Int])) {
    val (sidelength, matrix) = p
    matrix.copy(array, 0, 0, sidelength, sidelength)
  }
}
