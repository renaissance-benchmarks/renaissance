package smtlib.trees

import Terms._

object TermsOps {

  /* ========================
        Operations on Sort
     ========================
   */

  /** Applies a function to each sort in post-order
    *
    * The mapping is done starting from the leaf of the sort tree. For
    * each node, first apply recursively the postMap on the children
    * from left to right, then apply the function to the current sort
    * with the new children.
    *
    * @param f the function to apply. If it returns None then do not
    *          update the corresponding node.
    * @param sort the sort to traverse
    * @return the new sort after applying the mapping
    */
  def postMap(f: (Sort) => Option[Sort])(sort: Sort): Sort = {
    val rec = postMap(f) _
    val Sort(id, subSorts) = sort

    val recSorts = subSorts.map(rec)

    val newSort = {
      if( recSorts.zip(subSorts).exists{ case (bef, aft) => bef ne aft } )
        Sort(id, recSorts)
      else
        sort
    }

    f(newSort).getOrElse(newSort)
  }


  /** Applies a function to each sort in pre-order
    *
    * The mapping is done starting from the root of the sort tree. For
    * each node, first apply the function to the current node, then
    * do it recursively on the children from left to right.
    *
    * @param f the function to apply. If it returns None then do not
    *          update the corresponding node
    * @param sort the sort to traverse
    * @return the new sort after applying the mapping
    * @note this operation can diverge if f is not well formed
    */
  def preMap(f: (Sort) => Option[Sort])(sort: Sort): Sort = {
    val rec = preMap(f) _
    val newSort = f(sort).getOrElse(sort)
    val Sort(id, subSorts) = newSort

    val recSorts = subSorts.map(rec)

    if( recSorts.zip(subSorts).exists{ case (bef, aft) => bef ne aft } )
      Sort(id, recSorts)
    else
      newSort
  }


  def postTraversal(f: (Sort) => Unit)(sort: Sort): Unit = {
    val rec = postTraversal(f) _
    val Sort(_, subSorts) = sort
    subSorts.foreach(rec)
    f(sort)
  }

  def preTraversal(f: (Sort) => Unit)(sort: Sort): Unit = {
    val rec = preTraversal(f) _
    val Sort(_, subSorts) = sort
    f(sort)
    subSorts.foreach(rec)
  }


  def fold[T](f: (Sort, Seq[T]) => T)(sort: Sort): T = {
    val rec = fold(f) _
    val Sort(_, ss) = sort
    f(sort, ss.map(rec))
  }


  def exists(matcher: (Sort) => Boolean)(sort: Sort): Boolean =
    fold[Boolean]({ (s, subs) => matcher(s) || subs.contains(true) } )(sort)

}
