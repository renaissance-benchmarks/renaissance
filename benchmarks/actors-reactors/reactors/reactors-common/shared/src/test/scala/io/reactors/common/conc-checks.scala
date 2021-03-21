package io.reactors.common



import scala.annotation.tailrec
import scala.collection._
import org.scalacheck._
import org.scalacheck.Prop._
import io.reactors.test._
import Conc._
import ConcRope._
import Conqueue._



object ConcChecks extends Properties("Conc") with ConcSnippets
  with ExtendedProperties {

  /* conc tree */

  val genLeaf = for (n <- detChoose(0, 500)) yield new Conc.Single(n)

  def genTree(level: Int): Gen[Conc[Int]] = if (level <= 0) genLeaf else for {
    tp <- detOneOf(0, 1, 2)
    left <- if (tp == 0) genTree(level - 2) else genTree(level - 1)
    right <- if (tp == 2) genTree(level - 2) else genTree(level - 1)
  } yield new <>(left, right)

  def trees(maxlevel: Int) = for {
    level <- detChoose(0, maxlevel + 1)
    tree <- genTree(level)
  } yield tree

  property("<> correctness") = forAll(detChoose(0, 1024), detChoose(0, 1024)) {
    testConcatCorrectness
  }

  property("<> balance") = forAll(detChoose(0, 1024), detChoose(0, 1024)) {
    testConcatBalance
  }

  property("apply correctness") = forAll(detChoose(1, 1024)) {
    testApply
  }

  property("update correctness") = forAll(detChoose(1, 2048)) { n =>
    testUpdate(n)
    testRopeUpdate(n)
    testConqueueUpdate(1)
    testConqueueUpdate(2)
    testConqueueUpdate(n)
  }

  property("insert correctness") = forAll(detChoose(0, 1024), detChoose(0, 20),
    detChoose(0, 1024)) {
    testInsert
  }

  property("split correctness") = forAll(for {
    sz <- detChoose(0, 4096)
    at <- detChoose(0, sz)
  } yield (sz, at)) { case (sz, at) =>
    testSplit(concList(0 until sz), at)
    testSplit(concChunkRope(0 until sz, 32), at)
  }

  property("generated trees") = forAll(trees(10)) { tree =>
    s"invariants: $tree" |: checkInvs(tree)
  }

  property("left shake") = forAll(trees(10)) { tree =>
    val shaken = ConcUtils.shakeLeft(tree)
    all(
      s"invariants: $shaken" |: checkInvs(shaken),
      s"leaning left: $shaken" |: (shaken.level <= 1 ||
          shaken.level < tree.level || shaken.left.level >= shaken.right.level)
    )
  }

  property("right shake") = forAll(trees(10)) { tree =>
    val shaken = ConcUtils.shakeRight(tree)
    all(
      s"invariants: $shaken" |: checkInvs(shaken),
      s"leaning right: $shaken" |: (shaken.level <= 1 ||
        shaken.level < tree.level || shaken.left.level <= shaken.right.level)
    )
  }

  /* conc queue */

  property("Conc.Queue operations") = forAll(detChoose(0, 1024)) { sz =>
    stackTraced {
      var q = new Queue[Int]()
      for (i <- 0 until sz) {
        q = q.enqueue(i)
        assert(q.head == i)
        assert(q.last == 0)
      }
      assert(q.size == sz)
      assert(q.toArray.toSeq == (0 until sz).reverse)
      val seen = mutable.Buffer[Int]()
      for (x <- q) seen += x
      assert(seen == (0 until sz).reverse)
      for (i <- 0 until sz) assert(q(i) == (sz - 1 - i), (i, q(i)))
      for (i <- 0 until sz) {
        assert(q.head == (sz - 1))
        assert(q.last == i)
        q = q.dequeue()
      }
      assert(q.size == 0)
      true
    }
  }

  /* conc rope */

  property("append correctness") = forAll(detChoose(1, 1000),
    detChoose(1, 5000)) {
    testAppendCorrectness
  }

  property("append balance") = forAll(detChoose(1, 1000), detChoose(1, 5000)) {
    testAppendBalance
  }

  property("unprepend correctness") = forAll(trees(14)) { tree =>
    val expected = mutable.Buffer[Int]()
    for (x <- tree) expected += x
    val observed = mutable.Buffer[Int]()
    @tailrec def extract(xs: Conc[Int]): Unit = if (xs != Empty) {
      val (head, tail) = ConcRope.unprepend(xs)
      observed += head
      assert(ConcRope.invariant(tree))
      extract(tail)
    }
    extract(tree)

    s"want: $expected, got: $observed" |: expected == observed
  }

  /* conqueue */

  def genSequence[T](length: Int, g: Gen[T]): Gen[Seq[T]] = for {
    head <- g
    tail <- if (length <= 1) detOneOf(Nil, Nil) else genSequence(length - 1, g)
  } yield head +: tail

  def genNum(num: Int, rank: Int) = for {
    xs <- genSequence(num, genTree(rank))
  } yield xs.length  match {
    case 0 => Zero
    case 1 => One(xs(0))
    case 2 => Two(xs(0), xs(1))
    case 3 => Three(xs(0), xs(1), xs(2))
    case 4 => Four(xs(0), xs(1), xs(2), xs(3))
  }

  def genTip(rank: Int) = for {
    num <- detOneOf(2, 3)
    xs <- genNum(num, rank)
  } yield Tip(xs)

  def genSpine(rank: Int, maxRank: Int): Gen[Spine[Int]] = for {
    leftNum <- detOneOf(2, 3)
    rightNum <- detOneOf(2, 3)
    leftWing <- genNum(leftNum, rank)
    rightWing <- genNum(rightNum, rank)
    tail <- genConqueue(rank + 1, maxRank)
  } yield new Spine(leftWing, rightWing, () => tail)

  def genConqueue(rank: Int, maxRank: Int) = for {
    conqueue <- if (rank == maxRank) genTip(rank) else genSpine(rank, maxRank)
  } yield conqueue

  def queues(rankLimit: Int) = for {
    maxRank <- detChoose(0, rankLimit)
    conqueue <- genConqueue(0, maxRank)
  } yield conqueue

  def lazyQueues(rankLimit: Int) = for {
    queue <- queues(rankLimit)
  } yield Conqueue.Lazy(Nil, queue, Nil)

  property("conqueue invariants") = forAll(queues(5)) { conq =>
    checkConqueueInvs(conq, 0)
  }

  property("head correctness") = forAll(queues(5)) { conq =>
    val buffer = mutable.Buffer[Int]()
    for (x <- conq) buffer += x
    buffer.head == ConcUtils.head(conq).asInstanceOf[Single[Int]].x
  }

  property("last correctness") = forAll(queues(5)) { conq =>
    val buffer = mutable.Buffer[Int]()
    for (x <- conq) buffer += x
    val queueStr = ConcUtils.queueString(conq)
    s"$queueStr\n: ${buffer.last} vs ${ConcUtils.last(conq)}" |:
      buffer.last == ConcUtils.last(conq).asInstanceOf[Single[Int]].x
  }

  property("conqueue pushHeadTop") = forAll(queues(9)) { conq =>
    val pushed = ConcUtils.pushHeadTop(conq, new Single(-1))
    //println(ConcUtils.queueString(conq))
    //println("after:")
    //println(ConcUtils.queueString(pushed))
    //println("--------------")
    all(
      s"Head is the value just pushed." |:
        ConcUtils.head(pushed).asInstanceOf[Single[Int]].x == -1,
      s"Invariants are met." |: checkConqueueInvs(pushed, 0),
      s"Correctly prepended." |: toSeq(pushed) == (-1 +: toSeq(conq))
    )
  }

  property("conqueue pushHeadTop many times") = forAll(queues(9),
    detChoose(1, 10000)) { (conq, n) =>
    var pushed = conq
    for (i <- 0 until n) {
      var units = 0
      pushed = ConcUtils.pushHeadTop(pushed, new Single(-i), () => units += 1)
      //println("Work done: " + units)
    }
    //println("n = " + n)
    //println(ConcUtils.queueString(conq))
    //println("after:")
    //println(ConcUtils.queueString(pushed))
    //println("--------------")
    all(
      s"Invariants are met." |: checkConqueueInvs(pushed, 0),
      s"Correctly prepended." |:
        toSeq(pushed) == ((0 until n).map(-_).reverse ++ toSeq(conq))
    )
  }

  property("conqueue pushLastTop") = forAll(queues(9)) { conq =>
    val pushed = ConcUtils.pushLastTop(conq, new Single(-1))
    //println(ConcUtils.queueString(conq))
    //println("after:")
    //println(ConcUtils.queueString(pushed))
    //println("--------------")
    all(
      s"Last is the value just pushed." |:
        ConcUtils.last(pushed).asInstanceOf[Single[Int]].x == -1,
      s"Invariants are met." |: checkConqueueInvs(pushed, 0),
      s"Correctly appended." |: toSeq(pushed) == (toSeq(conq) :+ -1)
    )
  }

  property("conqueue pushLastTop many times") = forAll(queues(9),
    detChoose(1, 10000)) { (conq, n) =>
    var pushed = conq
    for (i <- 0 until n) {
      var units = 0
      pushed = ConcUtils.pushLastTop(pushed, new Single(-i), () => units += 1)
      //println("Work done: " + units)
    }
    //println("n = " + n)
    //println(ConcUtils.queueString(conq))
    //println("after:")
    //println(ConcUtils.queueString(pushed))
    //println("--------------")
    all(
      s"Invariants are met." |: checkConqueueInvs(pushed, 0),
      s"Correctly appended." |:
        toSeq(pushed) == (toSeq(conq) ++ (0 until n).map(-_))
    )
  }

  property("lazy conqueue pushHeadTop constant work") = forAll(lazyQueues(9),
    detChoose(1, 10000)) { (lazyq, n) =>
    var pushed: Conqueue[Int] = lazyq
    val workHistory = for (i <- 0 until n) yield {
      var units = 0
      pushed = ConcUtils.pushHeadTop(pushed, new Single(-i), () => units += 1)
      units
    }
    val mostWork = workHistory.max
    all(
      s"Most work ever done <= 4: $mostWork" |: mostWork <= 4,
      s"Invariants are met." |: checkConqueueInvs(pushed, 0),
      s"Correctly prepended." |:
        toSeq(pushed) == ((0 until n).map(-_).reverse ++ toSeq(lazyq))
    )
  }

  property("lazy conqueue pushLastTop constant work") = forAll(lazyQueues(9),
    detChoose(1, 10000)) { (lazyq, n) =>
    var pushed: Conqueue[Int] = lazyq
    val workHistory = for (i <- 0 until n) yield {
      var units = 0
      pushed = ConcUtils.pushLastTop(pushed, new Single(-i), () => units += 1)
      units
    }
    val mostWork = workHistory.max
    all(
      s"Most work ever done <= 4: $mostWork" |: mostWork <= 4,
      s"Invariants are met." |: checkConqueueInvs(pushed, 0),
      s"Correctly appended." |:
        toSeq(pushed) == (toSeq(lazyq) ++ (0 until n).map(-_))
    )
  }

  property("lazy conqueue alternating pushHeadTop/pushLastTop constant work") =
    forAll(lazyQueues(9), detChoose(1, 10000), detChoose(1, 1000)) {
      (lazyq, n, seed) =>
      val random = new scala.util.Random(seed)
      var buffer = toSeq(lazyq)
      var pushed: Conqueue[Int] = lazyq
      val workHistory = for (i <- 0 until n) yield {
        var units = 0
        if (random.nextBoolean()) {
          pushed = ConcUtils.pushHeadTop(pushed,
            new Single(-i), () => units += 1)
          buffer = -i +: buffer
        } else {
          pushed = ConcUtils.pushLastTop(pushed, new Single(-i),
            () => units += 1)
          buffer = buffer :+ -i
        }
        units
      }
      val mostWork = workHistory.max
      all(
        s"Most work ever done <= 4: $mostWork" |: mostWork <= 4,
        s"Invariants are met." |: checkConqueueInvs(pushed, 0),
        s"Correctly appended." |: toSeq(pushed) == buffer
      )
    }

  property("conqueue popHeadTop") = forAll(queues(9)) { conq =>
    var popped = conq
    var list: List[Int] = toSeq(conq).toList
    val buffer = mutable.Buffer[Int]()
    while (list.nonEmpty) {
      list = list.tail
      //println(ConcUtils.queueString(popped))
      //println("-------------------------")
      buffer += ConcUtils.head(popped).asInstanceOf[Single[Int]].x
      popped = ConcUtils.popHeadTop(popped)
      checkConqueueInvs(popped, 0)
    }
    //println(ConcUtils.queueString(popped))
    all(
      s"Invariants are met." |: checkConqueueInvs(popped, 0),
      s"Correctly popped." |: toSeq(conq) == buffer,
      s"Conqueue is empty." |: popped == Tip(Zero)
    )
  }

  property("lazy conqueue popHeadTop constant work") = forAll(lazyQueues(12)) { conq =>
    var popped: Conqueue[Int] = conq
    var list: List[Int] = toSeq(conq).toList
    val buffer = mutable.Buffer[Int]()
    val workHistory = mutable.Buffer[Int]()
    while (list.nonEmpty) {
      var units = 0
      list = list.tail
      buffer += ConcUtils.head(popped).asInstanceOf[Single[Int]].x
      popped = ConcUtils.popHeadTop(popped, () => units += 1)
      workHistory += units
    }
    val mostWork = workHistory.max
    all(
      s"Invariants are met." |: checkConqueueInvs(popped, 0),
      s"Correctly popped." |: toSeq(conq) == buffer,
      s"Conqueue is empty." |: popped == Lazy(Nil, Tip(Zero), Nil),
      s"Most work ever done <= 4: $mostWork in $workHistory" |: mostWork <= 4
    )
  }

  property("conqueue popLastTop") = forAll(queues(9)) { conq =>
    var popped = conq
    var list: List[Int] = toSeq(conq).toList
    val buffer = mutable.Buffer[Int]()
    while (list.nonEmpty) {
      list = list.tail
      //println(ConcUtils.queueString(popped))
      //println("-------------------------")
      buffer += ConcUtils.last(popped).asInstanceOf[Single[Int]].x
      popped = ConcUtils.popLastTop(popped)
      checkConqueueInvs(popped, 0)
    }
    //println(ConcUtils.queueString(popped))
    all(
      s"Invariants are met." |: checkConqueueInvs(popped, 0),
      s"Correctly popped." |: toSeq(conq).reverse == buffer,
      s"Conqueue is empty." |: popped == Tip(Zero)
    )
  }

  property("lazy conqueue popHeadTop constant work") = forAll(lazyQueues(12)) { conq =>
    var popped: Conqueue[Int] = conq
    var list: List[Int] = toSeq(conq).toList
    val buffer = mutable.Buffer[Int]()
    val workHistory = mutable.Buffer[Int]()
    while (list.nonEmpty) {
      var units = 0
      list = list.tail
      buffer += ConcUtils.last(popped).asInstanceOf[Single[Int]].x
      popped = ConcUtils.popLastTop(popped, () => units += 1)
      workHistory += units
    }
    val mostWork = workHistory.max
    all(
      s"Invariants are met." |: checkConqueueInvs(popped, 0),
      s"Correctly popped." |: toSeq(conq) == buffer.reverse,
      s"Conqueue is empty." |: popped == Lazy(Nil, Tip(Zero), Nil),
      s"Most work ever done <= 4: $mostWork in $workHistory" |: mostWork <= 4
    )
  }

  property("lazy conqueue constant amount of work for any operation") =
    forAll(lazyQueues(15), detChoose(1, 1000000)) { (conq, seed) =>
      var modified: Conqueue[Int] = conq
      val random = new scala.util.Random(seed)
      val workHistory = mutable.Buffer[Int]()
      for (i <- 0 until 10000) {
        var units = 0
        val ops = modified match {
          case Lazy(Nil, Tip(Zero), Nil) => 2
          case _ => 4
        }
        random.nextInt(ops) match {
          case 0 =>
            modified = ConcUtils.pushHeadTop(modified, new Single(i), () => units += 1)
          case 1 =>
            modified = ConcUtils.pushLastTop(modified, new Single(i), () => units += 1)
          case 2 =>
            modified = ConcUtils.popHeadTop(modified, () => units += 1)
          case 3 =>
            modified = ConcUtils.popLastTop(modified, () => units += 1)
        }
        workHistory += units
      }
      val mostWork = workHistory.max
      all(
        s"Most work ever done <= 4: $mostWork in $workHistory" |: mostWork <= 4
      )
    }

  property("conqueue normalized") = forAll(
    queues(15), detChoose(1, 1000000), detChoose(1, 10000)
  ) { (conq, seed, numops) =>
    var modified: Conqueue[Int] = conq
    val random = new scala.util.Random(seed)
    for (i <- 0 until numops) {
      val ops = modified match {
        case Tip(Zero) => 2
        case _ => 4
      }
      random.nextInt(ops) match {
        case 0 =>
          modified = ConcUtils.pushHeadTop(modified, new Single(i))
        case 1 =>
          modified = ConcUtils.pushLastTop(modified, new Single(i))
        case 2 =>
          modified = ConcUtils.popHeadTop(modified)
        case 3 =>
          modified = ConcUtils.popLastTop(modified)
      }
    }
    val flushed = toSeq(modified)
    val normalized = modified.normalized
    val normalizedFlushed = toSeq(normalized)
    all(
      s"Invariants are met." |: checkInvs(normalized),
      s"Same sequence after normalization: $normalizedFlushed vs $flushed\n" +
      s"; conq:\n${ConcUtils.queueString(conq, (num: Num[Int]) => num.toString)}\n" +
      s"; lwings:${toSeq(ConcUtils.normalizeLeftWingsAndTip(modified, Conc.Empty))}\n" +
      s"; rwings:${toSeq(ConcUtils.normalizeRightWings(modified, Conc.Empty))}\n" +
      s"; length:${normalizedFlushed.length} vs ${flushed.length}" |:
      normalizedFlushed == flushed
    )
  }

  val numFormatter = ConcUtils.contentsFormatter[Int] _

  property("conqueue normalized toConqueue") = forAll(queues(12)) { conq =>
    var conq2string: String = null
    var simplestring: String = null
    val log = ConcUtils.bufferedLog(ConcUtils.printLog)
    try {
      import scala.language.reflectiveCalls

      val normalized = conq.normalized
      val conq2 = ConcUtils.toConqueue(normalized, log)
      val conqseq = toSeq(conq)
      val conq2seq = toSeq(conq2)
      simplestring = ConcUtils.queueString(conq2, ConcUtils.levelFormatter[Int] _)
      conq2string = ConcUtils.queueString(conq2, numFormatter)
      //println(ConcUtils.queueString(conq2))
      //println("------------------")
      all(
        s"Conqueue invariants met:\n$simplestring" |: checkConqueueInvs(conq2, 0),
        s"Normalization was correct." |: conqseq == toSeq(normalized),
        s"log: ${log.buffer.mkString("\n")}\n" +
        s"Represents the same sequence:\n$conqseq\n---- vs ----\n$conq2seq\n" +
        s"Original conqueues:\n${ConcUtils.queueString(conq, numFormatter)}\n" +
        s"---- vs ----\n" +
        s"${ConcUtils.queueString(conq2, numFormatter)}\n" +
        s"; length: ${conqseq.length} vs ${conq2seq.length}" |: conqseq == conq2seq
      )
    } catch {
      case t: Throwable =>
        s"log: ${log.flush()}\n" +
        s"toString:\n$simplestring \n" +
        s"Should not cause exceptions: $t\n${t.getStackTrace.mkString("\n")}" |: false
    }
  }

  def noExceptions(msg: String = "")(body: =>Prop) = {
    try {
      body
    } catch {
      case t: Throwable =>
        s"$msg\n" +
        s"Should not cause exceptions: $t\n${t.getStackTrace.mkString("\n")}" |: false
    }
  }

  property("conqueue concat") = forAll(lazyQueues(12), lazyQueues(12)) { (c1, c2) =>
    val s1 = toSeq(c1)
    val s2 = toSeq(c2)
    val appended = s1 ++ s2
    val concatenated = c1 <|> c2
    val labelString = {
      s"""
        ${ConcUtils.queueString(c1)}\n
        ---- concat with ----\n
        ${ConcUtils.queueString(c2)}\n
        $s1\n---- ++ ----\n$s2\n==========\n
        ${toSeq(concatenated)}\n---- vs ----\n$appended\n
      """ +
      s"\n------\n" +
      s"c1.normalized = ${toSeq(c1.normalized)}\n" +
      s"c2.normalized = ${toSeq(c2.normalized)}\n"
    }
    noExceptions(labelString) {
      ("Represent same sequence:\n" + labelString) |: appended == toSeq(concatenated)
    }
  }

  property("conc buffer correct") = forAll(detChoose(1, 10000)) { num =>
    val cb = new ConcBuffer[Int](32)
    for (i <- 0 until num) cb += i
    val conc = cb.extractConc()
    s"""
      Conc buffer contains correct elements:\n
      $conc\n${toSeq(conc)}\n---- vs ----\n${0 until num}
    """ |: toSeq(conc) == (0 until num)
  }

  property("conqueue buffer correct pushLast") = forAll(detChoose(1, 10000)) { num =>
    noExceptions(s"num = $num") {
      val cb = new ConqueueBuffer[Int](32)
      for (i <- 0 until num) cb.pushLast(i)
      val conq = cb.extractConqueue()
      s"""
        Conqueue buffer contains correct elements:\n
        $conq\n${toSeq(conq)}\n---- vs ----\n${0 until num}}
      """ |: toSeq(conq) == (0 until num)
    }
  }

  property("conqueue buffer correct pushHead") = forAll(detChoose(1, 10000)) { num =>
    noExceptions(s"num = $num") {
      val cb = new ConqueueBuffer[Int](32)
      for (i <- 0 until num) cb.pushHead(i)
      val conq = cb.extractConqueue()
      s"""
        Conqueue buffer contains correct elements:\n
        $conq\n${toSeq(conq)}\n---- vs ----\n${(0 until num).reverse}}
      """ |: toSeq(conq) == (0 until num).reverse
    }
  }

  property("conqueue buffer correct popLast") = forAll(detChoose(1, 10000)) { num =>
    noExceptions(s"num = $num") {
      val cb = new ConqueueBuffer[Int](32)
      for (i <- 0 until num) cb.pushLast(i)
      val buffer = mutable.Buffer[Int]()
      while (cb.nonEmpty) buffer += cb.popLast()
      s"""
        Conqueue buffer pops correct elements:\n
        buffer\n---- vs ----\n${(0 until num).reverse}}
      """ |: buffer == (0 until num).reverse
    }
  }

  property("conqueue buffer correct popHead") = forAll(detChoose(1, 10000)) { num =>
    noExceptions(s"num = $num") {
      val cb = new ConqueueBuffer[Int](32)
      for (i <- 0 until num) cb.pushLast(i)
      val buffer = mutable.Buffer[Int]()
      while (cb.nonEmpty) buffer += cb.popHead()
      s"""
        Conqueue buffer pops correct elements:\n
        buffer\n---- vs ----\n${(0 until num)}}
      """ |: buffer == (0 until num)
    }
  }

  property("conqueue buffer all combinations of operations correct") = forAll(
    detChoose(1, 64), detChoose(1, 64), detChoose(1, 10000), detChoose(1, 1000000)
  ) { (prehead, prelast, numops, seed) =>
    noExceptions(s"$prehead, $prelast, $numops, $seed") {
      val cb = new ConqueueBuffer[Int](32)
      var v = Vector[Int]()
      val random = new scala.util.Random(seed)
      for (i <- 0 until prehead) {
        val j = 100 - i
        cb.pushHead(j)
        v = j +: v
      }
      for (i <- 0 until prelast) {
        val j = 100 - i
        cb.pushLast(j)
        v = v :+ j
      }
      val opHistory = mutable.Buffer[Int]()
      for (j <- 0 until numops) {
        val i = -j - 1
        val ops = if (cb.isEmpty) 2 else 4
        val op = random.nextInt(ops)
        opHistory += op
        op match {
          case 0 =>
            cb.pushHead(i)
            v = i +: v
          case 1 =>
            cb.pushLast(i)
            v = v :+ i
          case 2 =>
            cb.popHead()
            v = v.tail
          case 3 =>
            cb.popLast()
            v = v.init
        }
        val bothEmpty = (cb.isEmpty && v.isEmpty)
        val condition = if (bothEmpty) s"both empty" else s"both non-empty"
        if (!(bothEmpty || (cb.head == v.head && cb.last == v.last))) {
          println(cb.diagnosticString)
          println(s"op: $op")
          println(v)
          println(condition)
          println("assertion!")
          assert(false, s"""
            op: $op, i: $i\n$cb\n$v\noperation history: $opHistory\n
            condition: $condition
          """)
        }
      }
      val conq = cb.extractConqueue()
      val seq = toSeq(conq)
      all(
        s"""
          Represents the same sequence:\n
          ${v.mkString(", ")}\n---- vs ----\n${seq.mkString(", ")}
        """ |: v == seq
      )
    }
  }

}
