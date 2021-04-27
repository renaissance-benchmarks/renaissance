package smtlib.trees


/** Generic and useful operations on entire trees
  *
  * This contains most traversal operations that can be
  * simply described as applying some function over the whole
  * tree. Mappings are more complex as they need to return
  * new trees, and would usually be defined as a full tree transformer
  * as it needs to return different type for each exact tree.
  */
object TreesOps {

  def count(p: (Tree) => Boolean)(t: Tree): Int = {
    val folder = new TreeFolder {
      type R = Int
      override def combine(node: Tree, counts: Seq[Int]) = 
        counts.sum + (if(p(node)) 1 else 0)
    }
    folder.fold(t)
  }

  def exists(p: (Tree) => Boolean)(t: Tree): Boolean = {
    val folder = new TreeFolder {
      type R = Boolean
      override def combine(node: Tree, cs: Seq[Boolean]) = 
        cs.exists(b => b) || p(node)
    }
    folder.fold(t)
  }

  def forall(p: (Tree) => Boolean)(t: Tree): Boolean = {
    val folder = new TreeFolder {
      type R = Boolean
      override def combine(node: Tree, cs: Seq[Boolean]) = 
        cs.forall(b => b) && p(node)
    }
    folder.fold(t)
  }

  def fold[T](f: (Tree, Seq[T]) => T)(t: Tree): T = {
    val folder = new TreeFolder {
      type R = T
      override def combine(node: Tree, cs: Seq[T]): T = f(node, cs)
    }
    folder.fold(t)
  }


  def foreach(f: (Tree) => Unit)(t: Tree): Unit = {
    val traverser = new TreeTraverser {
      override def combine(tree: Tree): Unit = f(tree)
    }
    traverser.traverse(t)
  }

}
