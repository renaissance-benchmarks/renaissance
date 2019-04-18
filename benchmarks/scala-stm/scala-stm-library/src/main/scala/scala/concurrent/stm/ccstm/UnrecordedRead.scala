/* scala-stm - (c) 2009-2010, Stanford University, PPL */

package scala.concurrent.stm.ccstm


/** Holds the result of an unrecorded read, which may be used to avoid
 *  transaction conflicts, or to detect ABA changes when performing
 *  single-operation transactions.  `ReleasableRead`s provide a
 *  related functionality.
 *
 *  When an unrecorded read is performed in a transaction, the caller is
 *  responsible for guaranteeing that the transaction's behavior is correct,
 *  even if the read becomes invalid prior to commit.  Unrecorded reads may be
 *  useful for heuristic decisions that can tolerate inconsistent or stale
 *  data, for methods that register transaction handlers to perform
 *  validation at a semantic level, or for optimistically traversing linked
 *  data structures while tolerating mutations to earlier links.  When used in
 *  combination with transaction resource callbacks, it is important to
 *  consider the case that the unrecorded read is already invalid before it is
 *  returned to the requester.
 *
 *  Writes by the same transaction that performed the unrecorded read are
 *  '''not''' considered to invalidate the read.  
 *
 *  When called from a non-transactional context the returned instance can be
 *  used to determine if a value has remained unchanged for a particular
 *  interval, which may be useful to detect ABA situations.
 *
 *  @author Nathan Bronson
 */
private[ccstm] trait UnrecordedRead[+T] {

  /** Returns the value observed by this `UnrecordedRead`, regardless of
   *  whether it is still valid.
   */
  def value: T

  /** Returns true if definitely no writes have been performed by a context
   *  other than the one that performed this unrecorded read.
   */
  def stillValid: Boolean

  /** Returns true if the unrecorded read was performed in a transaction, and
   *  the source of this read is known to be in the transaction's read or write
   *  set, in which case `stillValid` will definitely be true at the
   *  transaction's commit (linearization) point if the transaction commits.
   *  Returns false for non-transactional unrecorded reads.  This method is for
   *  optimization purposes only, a false result does not guarantee that the
   *  read is not in the transaction's read or write set.  If this method
   *  returns true for an `UnrecordedRead` instance it will always
   *  return true.
   *  @return true if the caller may assume that `stillValid` will
   *      be true for this `UnrecordedRead` if the bound transaction
   *      is successfully committed.
   */
  def recorded: Boolean
}

