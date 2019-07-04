package cafesat.common

object Math {

  def fix[A](fun: (A => A), t: A): A = {
    val t2 = fun(t)
    if (t == t2) t2 else fix(fun, t2)
  }

//  def comp[A,B,C](f: (A => B), g: (C => A)): (C => B) = ((x: C) => f(g(x)))

  def lcm(a: BigInt, b: BigInt) : BigInt = (a * b) / a.gcd(b)

  def divide(a: Int, b: Int): (Int, Int) = (a / b, a % b)

  def gcd(a: Int, b: Int): Int = {
    def gcd0(a: Int, b: Int): Int = {
      require(a >= b)
      if(b == 0) a else gcd0(b, a % b)
    }
    if(a > b) gcd0(a, b) else gcd0(b, a)
  }

  //return (x, y) such that ax + by = gcd(a, b)
  def extendedEuclid(a: Int, b: Int): (Int, Int) = if(b == 0) (1, 0) else {
    val (q, r) = divide(a, b)
    val (s, t) = extendedEuclid(b, r)
    (t, s - q * t)
  }
}
