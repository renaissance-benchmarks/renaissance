package io.reactors
package common



import io.reactors.algebra._



/** Quad-based matrix for spatial querying of sparse data.
 */
class QuadMatrix[@specialized(Int, Long, Double) T](
  private[reactors] val blockExponent: Int = 8,
  private[reactors] val poolSize: Int = 32
)(
  implicit val arrayable: Arrayable[T]
) extends Matrix[T] {
  private[reactors] var blockSize: Int = _
  private[reactors] var blockMask: Int = _
  private[reactors] var removedValue: T = _
  private[reactors] var roots: HashMatrix[QuadMatrix.Node[T]] = _
  private[reactors] var empty: QuadMatrix.Node.Empty[T] = _
  private[reactors] var forkPool: FixedSizePool[QuadMatrix.Node.Fork[T]] = _
  private[reactors] var leafPool: FixedSizePool[QuadMatrix.Node.Leaf[T]] = _
  private[reactors] var flatPool: FixedSizePool[QuadMatrix.Node.Flat[T]] = _
  val nil = arrayable.nil

  private[reactors] def init(self: QuadMatrix[T]) {
    roots = new HashMatrix[QuadMatrix.Node[T]]
    blockSize = 1 << blockExponent
    blockMask = blockSize - 1
    empty = new QuadMatrix.Node.Empty[T]
    forkPool = new FixedSizePool(
      poolSize,
      () => QuadMatrix.Node.Fork.empty(this),
      n => n.clear(self))
    leafPool = new FixedSizePool(
      poolSize,
      () => QuadMatrix.Node.Leaf.empty[T],
      n => n.clear())
    flatPool = new FixedSizePool(
      poolSize,
      () => QuadMatrix.Node.Flat.empty[T],
      n => {})
    removedValue = nil
  }
  init(this)

  private[reactors] def fillPools(self: QuadMatrix[T]) {
    var i = 0
    while (i < poolSize) {
      forkPool.release(QuadMatrix.Node.Fork.empty(self))
      leafPool.release(QuadMatrix.Node.Leaf.empty[T])
      flatPool.release(QuadMatrix.Node.Flat.empty[T])
      i += 1
    }
  }

  private[reactors] def isTopLevelLeafAt(gx: Int, gy: Int): Boolean = {
    val bx = gx >> blockExponent
    val by = gy >> blockExponent
    val quad = roots(bx, by)
    quad != null && quad.isLeaf
  }

  private[reactors] def release(n: QuadMatrix.Node[T]) = n match {
    case l: QuadMatrix.Node.Leaf[T] => leafPool.release(l)
    case f: QuadMatrix.Node.Fork[T] => forkPool.release(f)
    case f: QuadMatrix.Node.Flat[T] => flatPool.release(f)
    case _ => // Not releasing Empty nodes.
  }

  def fillPools() {
    fillPools(this)
  }

  def update(gx: Int, gy: Int, v: T): Unit = applyAndUpdate(gx, gy, v)

  def applyAndUpdate(gx: Int, gy: Int, v: T): T = {
    if (v == nil) remove(gx, gy)
    else {
      val bx = gx >> blockExponent
      val by = gy >> blockExponent
      val qx = gx & blockMask
      val qy = gy & blockMask
      var root = roots(bx, by)
      if (root == null) {
        root = empty
        roots(bx, by) = root
      }
      val nroot = root.update(qx, qy, v, blockExponent, this)
      if (root ne nroot) {
        roots(bx, by) = nroot
      }
      val prev = removedValue
      if (removedValue != nil) removedValue = nil
      prev
    }
  }

  def remove(gx: Int, gy: Int): T = {
    val bx = gx >> blockExponent
    val by = gy >> blockExponent
    val qx = gx & blockMask
    val qy = gy & blockMask
    val root = roots(bx, by)
    if (root == null) nil
    else {
      val nroot = root.remove(qx, qy, blockExponent, this)
      if (nroot ne root) {
        roots(bx, by) = nroot
        release(root)
      }
      if (nroot.isEmpty) roots.remove(bx, by)
      val prev = removedValue
      removedValue = nil
      prev
    }
  }

  protected def clearSpecialized(self: QuadMatrix[T]) {
    roots.clear()
  }

  def clear() {
    clearSpecialized(this)
  }

  def apply(gx: Int, gy: Int): T = {
    val bx = gx >> blockExponent
    val by = gy >> blockExponent
    val qx = gx & blockMask
    val qy = gy & blockMask
    val root = roots(bx, by)
    if (root == null) nil
    else root.apply(qx, qy, blockExponent, this)
  }

  def orElse(xr: Int, yr: Int, v: T): T = {
    val cur = apply(xr, yr)
    if (cur != nil) cur else v
  }

  def foreach(f: XY => Unit): Unit = {
    for (rxy <- roots) {
      val root = roots(rxy.x, rxy.y)
      val x0 = rxy.x << blockExponent
      val y0 = rxy.y << blockExponent
      root.foreach(blockExponent, x0, y0, f)
    }
  }

  def copy(a: Array[T], gxf: Int, gyf: Int, gxu: Int, gyu: Int): Unit = {
    new QuadMatrix.Area[T](this, gxf, gyf, gxu, gyu, true).copy(a)
  }

  def area(gxf: Int, gyf: Int, gxu: Int, gyu: Int): Matrix.Area[T] =
    new QuadMatrix.Area[T](this, gxf, gyf, gxu, gyu, true)

  def nonNilArea(gxf: Int, gyf: Int, gxu: Int, gyu: Int): Matrix.Area[T] =
    new QuadMatrix.Area[T](this, gxf, gyf, gxu, gyu, false)
}


object QuadMatrix {
  private[reactors] class Area[@specialized(Int, Long, Double) T](
    val self: QuadMatrix[T], val gxf: Int, val gyf: Int, val gxu: Int, val gyu: Int,
    val includeNil: Boolean
  ) extends Matrix.Area[T] {
    def foreach(a: Matrix.Action[T]) {
      val exp = self.blockExponent
      var byc = gyf >> exp
      val byt = gyu >> exp
      while (byc <= byt) {
        var bxc = gxf >> exp
        val bxt = gxu >> exp
        while (bxc <= bxt) {
          val root = self.roots(bxc, byc)
          if (root != null) {
            root.areaForeach(
              math.max(bxc << exp, gxf),
              math.max(byc << exp, gyf),
              math.min((bxc << exp) + (1 << exp), gxu),
              math.min((byc << exp) + (1 << exp), gyu),
              (bxc << exp) + (1 << (exp - 1)),
              (byc << exp) + (1 << (exp - 1)),
              1 << (exp - 1),
              a, includeNil, self.nil)
          } else {
            if (includeNil) {
              foreachNil(
                math.max(bxc << exp, gxf),
                math.max(byc << exp, gyf),
                math.min((bxc << exp) + (1 << exp), gxu),
                math.min((byc << exp) + (1 << exp), gyu),
                a)
            }
          }
          bxc += 1
        }
        byc += 1
      }
    }

    def copy(a: Array[T]) {
      val width = gxu - gxf
      val exp = self.blockExponent
      var byc = gyf >> exp
      val byt = gyu >> exp
      while (byc <= byt) {
        var bxc = gxf >> exp
        val bxt = gxu >> exp
        while (bxc <= bxt) {
          val root = self.roots(bxc, byc)
          if (root != null) {
            root.copy(
              math.max(bxc << exp, gxf),
              math.max(byc << exp, gyf),
              math.min((bxc << exp) + (1 << exp), gxu),
              math.min((byc << exp) + (1 << exp), gyu),
              (bxc << exp) + (1 << (exp - 1)),
              (byc << exp) + (1 << (exp - 1)),
              1 << (exp - 1),
              a, this, self.nil)
          } else {
            copyNil(
              math.max(bxc << exp, gxf),
              math.max(byc << exp, gyf),
              math.min((bxc << exp) + (1 << exp), gxu),
              math.min((byc << exp) + (1 << exp), gyu),
              gxf, gyf, width, a)
          }
          bxc += 1
        }
        byc += 1
      }
    }

    def foreachNil(gxf: Int, gyf: Int, gxu: Int, gyu: Int, a: Matrix.Action[T]) {
      val nil = self.nil
      var y = gyf
      while (y < gyu) {
        var x = gxf
        while (x < gxu) {
          a(x, y, nil)
          x += 1
        }
        y += 1
      }
    }

    def copyNil(gxf: Int, gyf: Int, gxu: Int, gyu: Int, x0: Int, y0: Int, width: Int,
      a: Array[T]) {
      val nil = self.nil
      var y = gyf
      while (y < gyu) {
        var x = gxf
        while (x < gxu) {
          a((y - y0) * width + (x - x0)) = nil
          x += 1
        }
        y += 1
      }
    }
  }

  trait Node[@specialized(Int, Long, Double) T] {
    def isEmpty: Boolean
    def isLeaf: Boolean
    def apply(x: Int, y: Int, exp: Int, self: QuadMatrix[T]): T
    def update(x: Int, y: Int, v: T, exp: Int, self: QuadMatrix[T]): Node[T]
    def remove(x: Int, y: Int, exp: Int, self: QuadMatrix[T]): Node[T]
    def foreach(exp: Int, x0: Int, y0: Int, f: XY => Unit): Unit
    def areaForeach(gxf: Int, gyf: Int, gxu: Int, gyu: Int, gxm: Int, gym: Int,
      hsz: Int, a: Matrix.Action[T], includeNil: Boolean, nil: T): Unit
    def copy(gxf: Int, gyf: Int, gxu: Int, gyu: Int, gxm: Int, gym: Int,
      hsz: Int, a: Array[T], area: Area[T], nil: T): Unit
  }

  object Node {
    class Empty[@specialized(Int, Long, Double) T]
    extends Node[T] {
      def isEmpty = true
      def isLeaf = false
      def apply(x: Int, y: Int, exp: Int, self: QuadMatrix[T]): T =
        self.arrayable.nil
      def update(x: Int, y: Int, v: T, exp: Int, self: QuadMatrix[T]): Node[T] = {
        val leaf = self.leafPool.acquire()
        leaf.update(x, y, v, exp, self)
        leaf
      }
      def remove(x: Int, y: Int, exp: Int, self: QuadMatrix[T]): Node[T] = this
      def foreach(exp: Int, x0: Int, y0: Int, f: XY => Unit): Unit = {}
      def areaForeach(gxf: Int, gyf: Int, gxu: Int, gyu: Int, gxm: Int, gym: Int,
        hsz: Int, a: Matrix.Action[T], includeNil: Boolean, nil: T) {
        if (includeNil) {
          var y = gyf
          while (y < gyu) {
            var x = gxf
            while (x < gxu) {
              a(x, y, nil)
              x += 1
            }
            y += 1
          }
        }
      }
      def copy(gxf: Int, gyf: Int, gxu: Int, gyu: Int, gxm: Int, gym: Int,
        hsz: Int, a: Array[T], area: Area[T], nil: T): Unit = {
        val x0 = area.gxf
        val y0 = area.gyf
        val width = area.gxu - x0
        var y = gyf
        while (y < gyu) {
          var x = gxf
          while (x < gxu) {
            a((y - y0) * width + (x - x0)) = nil
            x += 1
          }
          y += 1
        }
      }
    }

    class Fork[@specialized(Int, Long, Double) T]
    extends Node[T] {
      private[reactors] var children: Array[Node[T]] = _

      private[reactors] def init(self: Fork[T]) {
        children = new Array(4)
      }
      init(this)

      def isEmpty = false

      def isLeaf = false

      def clear(self: QuadMatrix[T]) {
        children(0) = self.empty
        children(1) = self.empty
        children(2) = self.empty
        children(3) = self.empty
      }

      def apply(x: Int, y: Int, exp: Int, self: QuadMatrix[T]): T = {
        val nexp = exp - 1
        val xidx = x >>> nexp
        val yidx = y >>> nexp
        val idx = (yidx << 1) + (xidx)
        val nx = x - (xidx << nexp)
        val ny = y - (yidx << nexp)
        children(idx).apply(nx, ny, nexp, self)
      }

      def update(x: Int, y: Int, v: T, exp: Int, self: QuadMatrix[T]): Node[T] = {
        val nexp = exp - 1
        val xidx = x >>> nexp
        val yidx = y >>> nexp
        val idx = (yidx << 1) + (xidx)
        val nx = x - (xidx << nexp)
        val ny = y - (yidx << nexp)
        val child = children(idx)
        val nchild = child.update(nx, ny, v, nexp, self)
        if (child ne nchild) {
          children(idx) = nchild
          self.release(child)
        }
        this
      }

      def remove(x: Int, y: Int, exp: Int, self: QuadMatrix[T]): Node[T] = {
        val nexp = exp - 1
        val xidx = x >>> nexp
        val yidx = y >>> nexp
        val idx = (yidx << 1) + (xidx)
        val nx = x - (xidx << nexp)
        val ny = y - (yidx << nexp)
        val child = children(idx)
        val nchild = child.remove(nx, ny, nexp, self)
        if (child ne nchild) {
          children(idx) = nchild
          self.release(child)
          if (nchild.isEmpty || nchild.isLeaf) {
            val cs = children
            var emptynum = 0
            if (cs(0).isEmpty) emptynum += 1
            if (cs(1).isEmpty) emptynum += 1
            if (cs(2).isEmpty) emptynum += 1
            if (cs(3).isEmpty) emptynum += 1
            if (emptynum == cs.length) self.empty
            else if (emptynum == cs.length - 1) {
              var i = 0
              while (i < cs.length) {
                if (cs(i).isInstanceOf[Leaf[_]]) {
                  val leaf = cs(i).asInstanceOf[Leaf[T]]
                  leaf.rise((i % 2) * (1 << nexp), (i / 2) * (1 << nexp))
                  return leaf
                }
                i += 1
              }
              this
            } else this
          } else this
        } else this
      }

      def foreach(exp: Int, x0: Int, y0: Int, f: XY => Unit): Unit = {
        val nexp = exp - 1
        val m = 1 << nexp
        children(0).foreach(nexp, x0, y0, f)
        children(1).foreach(nexp, x0 + m, y0, f)
        children(2).foreach(nexp, x0, y0 + m, f)
        children(3).foreach(nexp, x0 + m, y0 + m, f)
      }

      def areaForeach(gxf: Int, gyf: Int, gxu: Int, gyu: Int, gxm: Int, gym: Int,
        hsz: Int, a: Matrix.Action[T], includeNil: Boolean, nil: T) {
        val nhsz = hsz >> 1
        if (gxf < gxm && gyf < gym)
          children(0).areaForeach(
            gxf, gyf, math.min(gxm, gxu), math.min(gym, gyu),
            gxm - nhsz, gym - nhsz, nhsz, a, includeNil, nil)
        if (gxu >= gxm && gyf < gym)
          children(1).areaForeach(
            math.max(gxf, gxm), gyf, gxu, math.min(gym, gyu),
            gxm + nhsz, gym - nhsz, nhsz, a, includeNil, nil)
        if (gxf < gxm && gyu >= gym)
          children(2).areaForeach(
            gxf, math.max(gyf, gym), math.min(gxm, gxu), gyu,
            gxm - nhsz, gym + nhsz, nhsz, a, includeNil, nil)
        if (gxu >= gxm && gyu >= gym)
          children(3).areaForeach(
            math.max(gxf, gxm), math.max(gyf, gym), gxu, gyu,
            gxm + nhsz, gym + nhsz, nhsz, a, includeNil, nil)
      }

      def copy(gxf: Int, gyf: Int, gxu: Int, gyu: Int, gxm: Int, gym: Int,
        hsz: Int, a: Array[T], area: Area[T], nil: T): Unit = {
        val nhsz = hsz >> 1
        if (gxf < gxm && gyf < gym)
          children(0).copy(
            gxf, gyf, math.min(gxm, gxu), math.min(gym, gyu),
            gxm - nhsz, gym - nhsz, nhsz, a, area, nil)
        if (gxu >= gxm && gyf < gym)
          children(1).copy(
            math.max(gxf, gxm), gyf, gxu, math.min(gym, gyu),
            gxm + nhsz, gym - nhsz, nhsz, a, area, nil)
        if (gxf < gxm && gyu >= gym)
          children(2).copy(
            gxf, math.max(gyf, gym), math.min(gxm, gxu), gyu,
            gxm - nhsz, gym + nhsz, nhsz, a, area, nil)
        if (gxu >= gxm && gyu >= gym)
          children(3).copy(
            math.max(gxf, gxm), math.max(gyf, gym), gxu, gyu,
            gxm + nhsz, gym + nhsz, nhsz, a, area, nil)
      }
    }

    object Fork {
      def empty[@specialized(Int, Long, Double) T](quad: QuadMatrix[T]) = {
        val fork = new Fork[T]
        fork.clear(quad)
        fork
      }
    }

    class Leaf[@specialized(Int, Long, Double) T](
      implicit val arrayable: Arrayable[T]
    ) extends Node[T] {
      private[reactors] var coordinates: Array[Int] = _
      private[reactors] var elements: Array[T] = _

      private[reactors] def init(self: Leaf[T]) {
        coordinates = new Array(8)
        elements = arrayable.newArray(4)
      }
      init(this)

      def isEmpty = false

      def isLeaf = true

      def apply(x: Int, y: Int, exp: Int, self: QuadMatrix[T]): T = {
        var i = 0
        val nil = self.nil
        while (i < elements.length && elements(i) != nil) {
          val cx = coordinates(i * 2 + 0)
          val cy = coordinates(i * 2 + 1)
          if (cx == x && cy == y) {
            return elements(i)
          }
          i += 1
        }
        self.arrayable.nil
      }

      def update(x: Int, y: Int, v: T, exp: Int, self: QuadMatrix[T]): Node[T] = {
        var i = 0
        val nil = self.nil
        while (i < elements.length && elements(i) != nil) {
          val cx = coordinates(i * 2 + 0)
          val cy = coordinates(i * 2 + 1)
          if (cx == x && cy == y) {
            self.removedValue = elements(i)
            elements(i) = v
            return this
          }
          i += 1
        }
        if (i < elements.length) {
          elements(i) = v
          coordinates(i * 2 + 0) = x
          coordinates(i * 2 + 1) = y
          return this
        } else {
          assert(exp >= 2)
          var forkOrFlat: Node[T] = {
            if (exp > 2) self.forkPool.acquire()
            else self.flatPool.acquire()
          }
          var i = 0
          while (i < elements.length) {
            val cx = coordinates(i * 2 + 0)
            val cy = coordinates(i * 2 + 1)
            val cv = elements(i)
            forkOrFlat = forkOrFlat.update(cx, cy, cv, exp, self)
            i += 1
          }
          forkOrFlat = forkOrFlat.update(x, y, v, exp, self)
          forkOrFlat
        }
      }

      def remove(x: Int, y: Int, exp: Int, self: QuadMatrix[T]): Node[T] = {
        val nil = self.nil
        var i = elements.length - 1
        var lasti = -1
        while (i >= 0) {
          val elem = elements(i)
          if (elem != nil) {
            val cx = coordinates(i * 2 + 0)
            val cy = coordinates(i * 2 + 1)
            if (cx == x && cy == y) {
              self.removedValue = elem
              if (lasti != -1) {
                elements(i) = elements(lasti)
                elements(lasti) = nil
                coordinates(i * 2 + 0) = coordinates(lasti * 2 + 0)
                coordinates(i * 2 + 1) = coordinates(lasti * 2 + 1)
                return this
              } else {
                elements(i) = nil
                if (i == 0) return self.empty
                else return this
              }
            }
            if (lasti == -1) lasti = i
          }
          i -= 1
        }
        return this
      }

      def rise(x: Int, y: Int) {
        var i = 0
        val nil = arrayable.nil
        while (i < elements.length && elements(i) != nil) {
          coordinates(i * 2 + 0) += x
          coordinates(i * 2 + 1) += y
          i += 1
        }
      }

      def clear() {
        val nil = arrayable.nil
        elements(0) = nil
        elements(1) = nil
        elements(2) = nil
        elements(3) = nil
      }

      def foreach(exp: Int, x0: Int, y0: Int, f: XY => Unit): Unit = {
        var i = 0
        val nil = arrayable.nil
        while (i < elements.length && elements(i) != nil) {
          val x = x0 + coordinates(i * 2 + 0)
          val y = y0 + coordinates(i * 2 + 1)
          f(XY(x, y))
          i += 1
        }
      }

      def areaForeach(gxf: Int, gyf: Int, gxu: Int, gyu: Int, gxm: Int, gym: Int,
        hsz: Int, a: Matrix.Action[T], includeNil: Boolean, nil: T) {
        if (!includeNil) {
          var i = 0
          while (i < elements.length && elements(i) != nil) {
            val cx = gxm - hsz + coordinates(i * 2 + 0)
            val cy = gym - hsz + coordinates(i * 2 + 1)
            if (cx >= gxf && cx < gxu && cy >= gyf && cy < gyu) {
              a(cx, cy, elements(i))
            }
            i += 1
          }
        } else {
          val cx0 = gxm - hsz + coordinates(0 * 2 + 0)
          val cy0 = gym - hsz + coordinates(0 * 2 + 1)
          val cx1 = gxm - hsz + coordinates(1 * 2 + 0)
          val cy1 = gym - hsz + coordinates(1 * 2 + 1)
          val cx2 = gxm - hsz + coordinates(2 * 2 + 0)
          val cy2 = gym - hsz + coordinates(2 * 2 + 1)
          val cx3 = gxm - hsz + coordinates(3 * 2 + 0)
          val cy3 = gym - hsz + coordinates(3 * 2 + 1)
          var y = gyf
          while (y < gyu) {
            var x = gxf
            while (x < gxu) {
              if (x == cx0 && y == cy0) a(x, y, elements(0))
              else if (x == cx1 && y == cy1) a(x, y, elements(1))
              else if (x == cx2 && y == cy2) a(x, y, elements(2))
              else if (x == cx3 && y == cy3) a(x, y, elements(3))
              else a(x, y, nil)
              x += 1
            }
            y += 1
          }
        }
      }

      def copy(gxf: Int, gyf: Int, gxu: Int, gyu: Int, gxm: Int, gym: Int,
        hsz: Int, a: Array[T], area: Area[T], nil: T): Unit = {
        val cx0 = gxm - hsz + coordinates(0 * 2 + 0)
        val cy0 = gym - hsz + coordinates(0 * 2 + 1)
        val cx1 = gxm - hsz + coordinates(1 * 2 + 0)
        val cy1 = gym - hsz + coordinates(1 * 2 + 1)
        val cx2 = gxm - hsz + coordinates(2 * 2 + 0)
        val cy2 = gym - hsz + coordinates(2 * 2 + 1)
        val cx3 = gxm - hsz + coordinates(3 * 2 + 0)
        val cy3 = gym - hsz + coordinates(3 * 2 + 1)
        val x0 = area.gxf
        val y0 = area.gyf
        val width = area.gxu - x0
        var y = gyf
        while (y < gyu) {
          var x = gxf
          while (x < gxu) {
            val idx = (y - y0) * width + (x - x0)
            if (x == cx0 && y == cy0) a(idx) = elements(0)
            else if (x == cx1 && y == cy1) a(idx) = elements(1)
            else if (x == cx2 && y == cy2) a(idx) = elements(2)
            else if (x == cx3 && y == cy3) a(idx) = elements(3)
            else a(idx) = nil
            x += 1
          }
          y += 1
        }
      }
    }

    object Leaf {
      def empty[@specialized(Int, Long, Double) T: Arrayable] = new Leaf[T]
    }

    class Flat[@specialized(Int, Long, Double) T](
      implicit val arrayable: Arrayable[T]
    ) extends Node[T] {
      private[reactors] var matrix: Array[T] = _
      private[reactors] var count: Int =_

      private[reactors] def init(self: Flat[T]) {
        matrix = arrayable.newArray(16)
        count = 0
      }
      init(this)

      def isEmpty = false

      def isLeaf = false

      def apply(x: Int, y: Int, exp: Int, self: QuadMatrix[T]): T =
        matrix(y * 4 + x)

      def update(x: Int, y: Int, v: T, exp: Int, self: QuadMatrix[T]): Node[T] = {
        val nil = self.nil
        val prev = matrix(y * 4 + x)
        matrix(y * 4 + x) = v
        if (prev != nil) count -= 1
        if (v != nil) count += 1
        this
      }

      def remove(x: Int, y: Int, exp: Int, self: QuadMatrix[T]): Node[T] = {
        val nil = self.nil
        val prev = matrix(y * 4 + x)
        if (prev != nil) {
          self.removedValue = prev
          matrix(y * 4 + x) = nil
          count -= 1
          if (count <= 2) {
            var leaf: Node[T] = self.leafPool.acquire()
            var y = 0
            while (y < 4) {
              var x = 0
              while (x < 4) {
                val v = matrix(y * 4 + x)
                if (v != nil) {
                  leaf = leaf.update(x, y, v, exp, self)
                  matrix(y * 4 + x) = nil
                }
                x += 1
              }
              y += 1
            }
            leaf
          } else this
        } else this
      }

      def foreach(exp: Int, x0: Int, y0: Int, f: XY => Unit): Unit = {
        var y = 0
        while (y < 4) {
          var x = 0
          while (x < 4) {
            f(XY(x0 + x, y0 + y))
            x += 1
          }
          y += 1
        }
      }

      def areaForeach(gxf: Int, gyf: Int, gxu: Int, gyu: Int, gxm: Int, gym: Int,
        hsz: Int, a: Matrix.Action[T], includeNil: Boolean, nil: T) {
        var y = gyf
        while (y < gyu) {
          var x = gxf
          while (x < gxu) {
            val cx = x - (gxm - hsz)
            val cy = y - (gym - hsz)
            val v = matrix(cy * 4 + cx)
            if (includeNil || v != nil) a(x, y, v)
            x += 1
          }
          y += 1
        }
      }

      def copy(gxf: Int, gyf: Int, gxu: Int, gyu: Int, gxm: Int, gym: Int,
        hsz: Int, a: Array[T], area: Area[T], nil: T): Unit = {
        val x0 = area.gxf
        val y0 = area.gyf
        val width = area.gxu - x0
        var y = gyf
        while (y < gyu) {
          var x = gxf
          while (x < gxu) {
            val cx = x - (gxm - hsz)
            val cy = y - (gym - hsz)
            val v = matrix(cy * 4 + cx)
            a((y - y0) * width + (x - x0)) = v
            x += 1
          }
          y += 1
        }
      }
    }

    object Flat {
      def empty[@specialized(Int, Long, Double) T: Arrayable] = new Flat[T]
    }
  }
}
