package lift
package arithmetic

private[arithmetic] object ComputeGCD {

  /**
    * Find the Greatest Common Divisor in two expressions.
    *
    * @param a The first expression.
    * @param b The second expression.
    * @return The greatest common divisor.
    */
  def apply(a: ArithExpr, b: ArithExpr): ArithExpr = {
    val g: ArithExpr = (a, b) match {
      // GCD of constants
      case (Cst(x), Cst(y)) => gcdLong(x, y)

      case (i: IntDiv, _) => Cst(1)

      // GCD of two identical things is itself
      case (x, y) if x == y => x

      // GCD of powers, go through bases and find a match, return smallest exp
      // TODO: handle negative exp
      case (Pow(_, Cst(x)), _) if x < 0 => Cst(1)
      case (_, Pow(_, Cst(x))) if x < 0 => Cst(1)
      case (x, Pow(ob, e)) if ob == x => x // pow 1 (implicit)
      case (Pow(b1, e1), Pow(b2, e2)) if b1 == b2 => b1 pow ArithExpr.min(e1, e2)
      case (Pow(ob, e), Prod(factors)) if factors.contains(ob) => ob // pow 1 (implicit)
      case (Prod(factors), Pow(ob, e)) if factors.contains(ob) => ob // pow 1 (implicit)
      case (Pow(ob, e), x) if ob == x => x // pow 1 (implicit)
      case (x, Pow(ob, e)) if ob == x => x // pow 1 (implicit)

      // GCD of products: find GCD in factor pairs
      case (Prod(fs1), Prod(fs2)) => (for {f1 <- fs1; f2 <- fs2} yield ComputeGCD(f1, f2)).reduce(_ * _)
      case (Prod(f), c: Cst) => ComputeGCD(b, a)
      case (c: Cst, Prod(f)) => f.find(_.isInstanceOf[Cst]) match {
        case Some(x) => ComputeGCD(c, x)
        case _ => Cst(1)
      }
      case (Prod(f), x) if f.contains(x) && !ArithExpr.hasDivision(f) => x
      case (x, Prod(f)) if f.contains(x) && !ArithExpr.hasDivision(f) => x

      // GCD of sums: find common factor across all terms
        // Naums: sums are handled iby Sum.asProd inside Prod.unapply()
//      case (s1: Sum, s2: Sum) =>
//        // Compute the common factors
//        val fac1 = factorizeSum(s1)
//        if (fac1 == Cst(1)) return Cst(1)
//        val fac2 = factorizeSum(s2)
//        if (fac2 == Cst(1)) return Cst(1)
//
//        // The GCD could be either the factor or the remainder, so we compute the intersection
//        val common = List(fac1, s1 /^ fac1).intersect(List(fac2, s2 /^ fac2))
//        if (common.isEmpty) Cst(1)
//        else common.head
//
//      case (x, s: Sum) => ComputeGCD(b, a)
//      case (s: Sum, x) =>
//        // compute the common factor
//        val factor = factorizeSum(s)
//        // If there is none, there is no possible common factor
//        if (factor == Cst(1)) factor
//        // otherwise see if there is a common factor with the sum's terms
//        else ComputeGCD(factor, x) match {
//          // If there isn't, we still have a chance with the remainder
//          //case Cst(x) if x == 1 => gcd(x, s /^ factor)
//          case y => y
//        }

      case (x, y) => Cst(1)
    }
    // Never factorize by a fraction
    g match {
      case Pow(x, Cst(-1)) => Cst(1)
      case i: IntDiv => Cst(1)
      case x => x
    }
  }

  // Factorize a sum: find a factor common to all terms
  private def factorizeSum(s: Sum): ArithExpr = {
    factorizeList(s.terms)
  }

  def factorizeList(terms: List[ArithExpr]): ArithExpr = {
    val fac = for {
      t1 <- terms
      t2 <- terms
      if t1.HashSeed < t2.HashSeed || (t1.HashSeed == t2.HashSeed && t1.digest < t2.digest)
    } yield ComputeGCD(t1, t2)

    if (fac.isEmpty) Cst(1)
    else fac.reduce((l, r) => ComputeGCD(l, r))
  }

  def gcdLong(terms: List[Long]): Long = {
    terms.length match {
      case 0 => throw new IllegalArgumentException
      case 1 => terms.head
      case _ => terms.foldLeft[Long](terms.head)(gcdLong)
    }
  }

  def gcdLong(x: Long, y: Long): Long = {
    if (y == 0) scala.math.abs(x) else gcdLong(scala.math.abs(y), scala.math.abs(x) % y)
  }

}
