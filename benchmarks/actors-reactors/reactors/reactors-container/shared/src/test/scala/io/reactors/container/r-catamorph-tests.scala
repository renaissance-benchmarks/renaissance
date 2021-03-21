package io.reactors
package container



import org.scalacheck._
import org.scalacheck.Gen._
import org.scalacheck.Prop._
import io.reactors.algebra._
import io.reactors.test._



class RCatamorphCheck extends Properties("RCatamorph") with ExtendedProperties {

  val sizes = detChoose(0, 500)

  property("balanced CommuteCatamorph") = forAllNoShrink(sizes) { sz =>
    val tree = CommuteCatamorph(Commute(0)(_ + _))

    for (i <- 0 until sz) tree += i

    def check(node: CommuteCatamorph.Node[Int]): Prop = node match {
      case in: CommuteCatamorph.Inner[Int] =>
        val locallyBalanced = s"locally balanced: ${node.localString}" |:
          in.height == (1 + math.max(in.left.height, in.right.height))
        val leftBalanced = s"left balanced: ${node.localString}" |:
          (in.left.height == (in.height - 1) || in.left.height == (in.height - 2))
        val rightBalanced = s"right balanced: ${node.localString}" |:
          (in.right.height == (in.height - 1) || in.right.height == (in.height - 2))
        locallyBalanced && leftBalanced && rightBalanced && check(in.left) &&
          check(in.right)
      case leaf: CommuteCatamorph.Leaf[Int] =>
        "leaf height 0" |: leaf.height == 0
      case empty: CommuteCatamorph.Empty[Int] =>
        "empty height 0" |: empty.height == 0
    }

    check(tree.root)
  }

  property("balanced MonoidCatamorph") = forAllNoShrink(sizes) { sz =>
    val tree = MonoidCatamorph(Monoid(0)(_ + _))

    for (i <- 0 until sz) tree += i

    def check(node: MonoidCatamorph.Node[Int]): Prop = node match {
      case in: MonoidCatamorph.Inner[Int] =>
        val locallyBalanced = s"locally balanced: ${node.localString}" |:
          in.height == (1 + math.max(in.left.height, in.right.height))
        val leftBalanced = s"left balanced: ${node.localString}" |:
          (in.left.height == (in.height - 1) || in.left.height == (in.height - 2))
        val rightBalanced = s"right balanced: ${node.localString}" |:
          (in.right.height == (in.height - 1) || in.right.height == (in.height - 2))
        locallyBalanced && leftBalanced && rightBalanced && check(in.left) &&
          check(in.right)
      case leaf: MonoidCatamorph.Leaf[Int] =>
        "leaf height 0" |: leaf.height == 0
      case empty: MonoidCatamorph.Empty[Int] =>
        "empty height 0" |: empty.height == 0
    }

    check(tree.root)
  }

}