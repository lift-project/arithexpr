package apart
package arithmetic
package simplifier

import scala.language.postfixOps

object SimplifyMod {

  def simplify(dividend: ArithExpr, divisor: ArithExpr): Option[ArithExpr] = (dividend, divisor) match {

    // Simplify operands
    case (x, y) if !x.simplified => Some(ExprSimplifier(x) % y)
    case (x, y) if !y.simplified => Some(x % ExprSimplifier(y))

    ///////////////////////////////////////////////////////////////////////////////////
    // SPECIAL CASES //todo combine cases which only differ in order of args
    ///////////////////////////////////////////////////////////////////////////////////

    // FACTORIZATION
    // e + ca + ma % c+m == a(m+c) + e % c+m => e % c+m
    case (Sum(
              (e:ArithExpr) ::
              Prod(Cst(c1) :: (a2:ArithExpr) :: Nil) ::
              Prod((m1: Var) :: (a1:ArithExpr) :: Nil) ::
              Nil),
          Sum(Cst(c2) :: (m2: Var) :: Nil))
      if m1 == m2 && a1 == a2 && c1 == c2 =>
      Some(SimplifyMod(e, Cst(c1) + m1))

    // i + k + ca + ma % c+m == a(c+m) + i + k % c+m => i + k % c+m
    case (Sum(
              (i:ArithExpr) ::
              (k:ArithExpr) ::
              Prod(Cst(c1) :: (a2:ArithExpr) :: Nil) ::
              Prod((m1: Var) :: (a1:ArithExpr) :: Nil) ::
              Nil),
          Sum(Cst(c2) :: (m2: Var) :: Nil))
      if m1 == m2 && a1 == a2 && c1 == c2 =>
      Some(SimplifyMod(Sum(k :: i :: Nil), Sum(Cst(c1) :: m1 :: Nil)))

    // j + ck + ci + ni + nk % c+n == (n+2)(i+k)+j % 2+n => j%(2+n)
    case (Sum(
              (j:Var) ::
              Prod(Cst(c1) :: (i2:Var) :: Nil) ::
              Prod(Cst(c2) :: (k2:Var) :: Nil) ::
              Prod((n1:Var) :: (i1:Var) :: Nil) ::
              Prod((n2:Var) :: (k1:Var) :: Nil) ::
              Nil),
          Sum(Cst(c3) :: (n3:Var) :: Nil))
      if n1 == n2 && n1 == n3 && i1 == i2 && k1 == k2 && c1 == c2 && c1 == c3 =>
      Some(SimplifyMod(j, Cst(c1) + n1))

    // a%n + bn % n = a%n
    case (Sum(
              (Mod(a, n1)) ::
              Prod((n2:Var) :: (b: ArithExpr) :: Nil) ::
              Nil),
          (n3:Var))
      if n1 == n2 && n1 == n3 =>
      Some(SimplifyMod(a, n1))

    // a%n + bn + cn % n = a%n
    case (Sum(
              (Mod(a, n1)) ::
              Prod((n2:Var) :: (b: ArithExpr) :: Nil) ::
              Prod((n3:Var) :: (c: ArithExpr) :: Nil) ::
              Nil),
          (n4:Var))
      if n1 == n2 && n1 == n3  && n1 == n4 =>
      Some(SimplifyMod(a, n1))

    // 2 + m + i + 2j + mj % 2+m == 2+m + j(m+2) + i % 2+m => i % 2+m
    // 4 + m + i + 2j + mj % 2+m == (2+m)(j+1) + i + 2 => i + 2 % 2+m
    case (Sum(Cst(c1) ::
              (m2:Var) ::
              (i:Var) ::
              Prod(Cst(c2) :: (j2:Var) :: Nil) ::
              Prod((m1: Var) :: (j1:Var) :: Nil) ::
              Nil),
          Sum(Cst(c3) :: (m3: Var) :: Nil))
      if m1 == m2 && m1 == m3 && j1 == j2 /*&& c1 == c2*/ && c2 == c3 =>
     Some(SimplifyMod(i + c1-c2, c3+m3))

    // 4 + i + 2m + 2j + mj % (2+m) = (2+m)(2+j) + i % (2+m) => i
    // 5 + i + 2m + 2j + mj % (2+m) = (2+m)(2+j) + i+1 % (2+m) => i
    case (Sum(Cst(c) ::
              (i:Var) ::
              Prod(Cst(c2) :: (m2:Var) :: Nil) ::
              Prod(Cst(c1) :: (j2:Var) :: Nil) ::
              Prod((m1: Var) :: (j1:Var) :: Nil) ::
              Nil),
          Sum(Cst(c3) :: (m3: Var) :: Nil))
      if m1 == m2 && m1 == m3 && j1 == j2 && c1 == c2 && c1 == c3 =>
     Some(i + c-(c1*c2))

    // c1+n+j % c2+n = c1-c2+j % c+n
    case (Sum(Cst(c1) :: (n1:Var) :: (j:Var) :: Nil),
          Sum(Cst(c2) :: (n2: Var) :: Nil))
      if n1 == n2 && c1 >= c2 && c1 >= 0 && c2 >= 0 &&
        n1.sign == Sign.Positive && j.sign == Sign.Positive =>
     Some(SimplifyMod(c1-c2+j, c2+n2))

    // 3 + n + j + 2i + ni % 2+n == (n+2)(i+1)+j+1 % 2+n => j+1 % 2+n // try to generalise a bit more
    case (Sum(
              Cst(3) ::
              (n2:Var) ::
              (j:Var) ::
              Prod(Cst(2) :: (i2:Var) :: Nil) ::
              Prod((n1:Var) :: (i1:Var) :: Nil) ::
              Nil),
          Sum(Cst(2) :: (n3: Var) :: Nil))
      if n1 == n2 && n1 == n3 && i1 == i2 =>
     Some(SimplifyMod(j+1, n1+2))

    // Modulo 1
    case (_, Cst(1)) => Some(Cst(0))

    // 0 or 1 modulo anything
    case (Cst(x), _) if x == 0 || x == 1 => Some(dividend)

    // Constant modulo
    case (Cst(x), Cst(y)) => Some(Cst(x % y))

    case (x, y) if x == y => Some(Cst(0))

    case (x, y) if ArithExpr.isSmaller(abs(x), abs(y)).getOrElse(false) => Some(x)

    case (x, y) if ArithExpr.multipleOf(x, y) => Some(Cst(0))

    case (m: Mod, d) if m.divisor == d => Some(m)

    // If the divident is a product, try to find the divisor. Finding the GCD below should make this redundant, but the
    // GCD method does not return fractions, but the divisor could be one.
    case (Prod(factors), x) if factors.contains(x) && !ArithExpr.hasDivision(factors) => Some(Cst(0))

    // If there exists a common denominator, simplify
    case (x, y) if ArithExpr.gcd(x,y) == y => Some(Cst(0))

    // Isolate the terms which are multiple of the mod and eliminate
    case (s@Sum(terms), d) if !ArithExpr.mightBeNegative(s) =>
      val (multiple, _) = terms.partition(t => (t, d) match {
        case (Prod(factors1), Prod(factors2)) => factors2 forall (factors1 contains)
        case (Prod(factors), x) if factors.contains(x) => true
        case (x, y) if ArithExpr.multipleOf(x, y) => true
        case (x, y) => ArithExpr.gcd(x, y) == y
      })
      val shorterSum = s.withoutTerm(multiple)
      if (multiple.nonEmpty && !ArithExpr.mightBeNegative(shorterSum)) Some(shorterSum % d)
      else None

    case (x, y) if ArithExpr.multipleOf(x, y) => Some(Cst(0))

    case _ => None
  }

  def apply(dividend: ArithExpr, divisor: ArithExpr): ArithExpr = {
    val simplificationResult = if (PerformSimplification()) simplify(dividend, divisor) else None
    simplificationResult match {
      //case Some(toReturn) => println(s"$dividend % $divisor simplified to $toReturn"); toReturn
      case None => println(s"$dividend % $divisor not simplified");
        new Mod(dividend, divisor) with SimplifiedExpr
      case Some(toReturn) => toReturn
      //case None => new Mod(dividend, divisor) with SimplifiedExpr
    }
  }
}
