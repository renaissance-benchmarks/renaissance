/* scala-stm - (c) 2009-2010, Stanford University, PPL */

package scala.concurrent.stm
package examples

import util.Random

class IndexedMap[A, B] {

  private class Index[C](view: (A, B) => Iterable[C]) extends (C => Map[A, B]) {
    val mapping = TMap.empty[C, Map[A, B]]

    def apply(derived: C) = mapping.single.getOrElse(derived, Map.empty[A, B])

    def += (kv: (A, B))(implicit txn: InTxn) {
      for (c <- view(kv._1, kv._2))
        mapping(c) = apply(c) + kv
    }

    def -= (kv: (A, B))(implicit txn: InTxn) {
      for (c <- view(kv._1, kv._2)) {
        val after = mapping(c) - kv._1
        if (after.isEmpty)
          mapping -= c
        else
          mapping(c) = after
      }
    }
  }

  private val contents = TMap.empty[A, B]
  private val indices = Ref(List.empty[Index[_]])

  def addIndex[C](view: (A, B) => Iterable[C]): (C => Map[A, B]) = atomic { implicit txn =>
    val index = new Index(view)
    indices() = index :: indices()
    contents foreach { index += _ }
    index
  }

  def get(key: A): Option[B] = contents.single.get(key)

  def put(key: A, value: B): Option[B] = atomic { implicit txn =>
    val prev = contents.put(key, value)
    for (p <- prev; i <- indices())
      i -= (key -> p)
    for (i <- indices())
      i += (key -> value)
    prev
  }

  def remove(key: A): Option[B] = atomic { implicit txn =>
    val prev = contents.remove(key)
    for (p <- prev; i <- indices())
      i -= (key -> p)
    prev
  }
}

object IndexedMap {
  
  case class User(id: Int, name: String, likes: Set[String])

  val users = new IndexedMap[Int, User]
  val byName = users.addIndex { (id, u) => Some(u.name) }
  val byLike = users.addIndex { (id, u) => u.likes }

  //////// data

  val topBabyNames = Array(
      "Ethan", "Isabella", "Jacob", "Olivia", "Noah", "Sophia", "Logan", "Emma", "Liam", "Ava", "Aiden", "Abigail",
      "Mason", "Chloe", "Jackson", "Madison", "Jack", "Ella", "Jayden", "Addison", "Ryan", "Emily", "Matthew", "Lily",
      "Lucas", "Mia", "Michael", "Avery", "Alexander", "Grace", "Nathan", "Hannah")

  val languages = Array("scala", "java", "C++", "haskell", "clojure", "python", "ruby", "pascal", "perl")
  val sports = Array("climbing", "cycling", "hiking", "football", "baseball", "underwater hockey")

  val numIDs = 1000

  //////// operations

  def pick[A](a: Array[A])(implicit rand: Random) = a(rand.nextInt(a.length))

  def newName(id: Int)(implicit rand: Random) {
    atomic { implicit txn =>
      val before = users.get(id).getOrElse(User(id, "John Doe", Set.empty))
      val after = before copy (name = pick(topBabyNames))
      users.put(id, after)
    }
  }

  def newLikes(id: Int)(implicit rand: Random) {
    atomic { implicit txn =>
      val before = users.get(id).getOrElse(User(id, "John Doe", Set.empty))
      val after = before copy (likes = Set(pick(languages), pick(sports)))
      users.put(id, after)
    }
  }

  def randomOp(implicit rand: Random) {
    val pct = rand.nextInt(100)
    if (pct < 10) {
      // query by ID
      users.get(rand.nextInt(numIDs))
    } else if (pct < 50) {
      // query by name
      byName(pick(topBabyNames))
    } else if (pct < 70) {
      // query by sport
      byLike(pick(sports))
    } else if (pct < 90) {
      // query by language
      byLike(pick(languages))
    } else if (pct < 95) {
      newName(rand.nextInt(numIDs))
    } else {
      newLikes(rand.nextInt(numIDs))
    }
  }

  def populate() {
    implicit val rand = new Random
    for (id <- 0 until numIDs) {
      newName(id)
      newLikes(id)
    }
  }

  def run(numThreads: Int, opsPerThread: Int): Long = {
    val threads = Array.tabulate(numThreads) { _ =>
      new Thread() {
        override def run {
          implicit val rand = new Random
          for (i <- 0 until opsPerThread) randomOp
        }
      }
    }
    val begin = System.currentTimeMillis
    for (t <- threads) t.start
    for (t <- threads) t.join
    System.currentTimeMillis - begin
  }

  def main(args: Array[String]) {
    populate()

    for (pass <- 0 until 3; tc <- List(1, 2, 4, 8)) {
      val elapsed = run(tc, 1000000 / tc)
      printf("%d thread: %4.2f usec/op total throughput (90%% read)\n", tc, elapsed * 0.001)
    }
  }
}
