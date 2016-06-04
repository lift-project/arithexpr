package apart
package arithmetic
package simplifier

import scala.language.postfixOps

object SimplifyMod {

  def simplify(dividend: ArithExpr, divisor: ArithExpr): Option[ArithExpr] = (dividend, divisor) match {

    // Simplify operands
    case (x, y) if !x.simplified => Some(ExprSimplifier(x) % y)
    case (x, y) if !y.simplified => Some(x % ExprSimplifier(y))

     // special cases: todo combine the cases which only differ in order
      // Ni + nk + 2i + 2k + j % 2+N = (N+2)(i+k)+j % 2+N = j%(2+N)
    case (Sum(
              Prod(Cst(c1) :: (i2:Var) :: Nil) ::
              Prod((i1:Var) :: (n1:Var) :: Nil) ::
              Prod((n2:Var) :: (k1:Var) :: Nil) ::
              Prod(Cst(c2) :: (k2:Var) :: Nil) ::
              (j:Var) ::
              Nil),
          Sum(Cst(c3) :: (n3:Var) :: Nil))
      if n1 == n2 && n1 == n3 && i1 == i2 && k1 == k2 && c1 == c2 && c1 == c3 =>
      Some(SimplifyMod(j, Sum(Cst(c3) :: (n3:Var) :: Nil)))

    case (Sum(
              Prod((n1:Var) :: (i1:Var) :: Nil) ::
              Prod((n2:Var) :: (k1:Var) :: Nil) ::
              Prod(Cst(c1) :: (i2:Var) :: Nil) ::
              Prod(Cst(c2) :: (k2:Var) :: Nil) ::
              (j:Var) ::
              Nil),
          Sum(Cst(c3) :: (n3:Var) :: Nil))
      if n1 == n2 && n1 == n3 && i1 == i2 && k1 == k2 && c1 == c2 && c1 == c3 =>
      Some(SimplifyMod(j, Sum(Cst(c3) :: (n3:Var) :: Nil)))

    case (Sum(
              Prod(Cst(c1) :: (a2:ArithExpr) :: Nil) ::
              Prod((a1:ArithExpr) :: (m1: Var) :: Nil) ::
              (e:ArithExpr) ::
              Nil),
          Sum(Cst(c2) :: (m2: Var) :: Nil))
      if m1 == m2 && a1 == a2 && c1 == c2 =>
      Some(SimplifyMod(e, Sum(Cst(c1) :: m1 :: Nil)))

    case (Sum(
              Prod((a2:ArithExpr) :: Cst(c1) :: Nil) ::
              Prod((a1:ArithExpr) :: (m1: Var) :: Nil) ::
              (e:ArithExpr) ::
              Nil),
          Sum(Cst(c2) :: (m2: Var) :: Nil))
      if m1 == m2 && a1 == a2 && c1 == c2 =>
      Some(SimplifyMod(e, Sum(Cst(c1) :: m1 :: Nil)))

    case (Sum(
              Prod((a1:ArithExpr) :: (m1: Var) :: Nil) ::
              Prod((a2:ArithExpr) :: Cst(c1) :: Nil) ::
              (e:ArithExpr) ::
              Nil),
          Sum(Cst(c2) :: (m2: Var) :: Nil))
      if m1 == m2 && a1 == a2 && c1 == c2 =>
      Some(SimplifyMod(e, Sum(Cst(c1) :: m1 :: Nil)))

    case (Sum(
              (e:ArithExpr) ::
              Prod((m1: Var) :: (a1:ArithExpr) :: Nil) ::
              Prod(Cst(c1) :: (a2:ArithExpr) :: Nil) ::
              Nil),
          Sum(Cst(c2) :: (m2: Var) :: Nil))
      if m1 == m2 && a1 == a2 && c1 == c2 =>
      Some(SimplifyMod(e, Sum(Cst(c1) :: m1 :: Nil)))

    // j(2+m) + k + i % 2+m = i+k % 2+m
    case (Sum(
              Prod(Cst(c1) :: (a2:ArithExpr) :: Nil) ::
              Prod((a1:ArithExpr) :: (m1: Var) :: Nil) ::
              (k:ArithExpr) ::
              (i:ArithExpr) ::
              Nil),
          Sum(Cst(c2) :: (m2: Var) :: Nil))
      if m1 == m2 && a1 == a2 && c1 == c2 =>
      Some(SimplifyMod(Sum(k :: i :: Nil), Sum(Cst(c1) :: m1 :: Nil)))

    case (Sum(
              Prod((a2:ArithExpr) :: Cst(c1) :: Nil) ::
              Prod((a1:ArithExpr) :: (m1: Var) :: Nil) ::
              (k:ArithExpr) ::
              (i:ArithExpr) ::
              Nil),
          Sum(Cst(c2) :: (m2: Var) :: Nil))
      if m1 == m2 && a1 == a2 && c1 == c2 =>
      Some(SimplifyMod(Sum(k :: i :: Nil), Sum(Cst(c1) :: m1 :: Nil)))

    // (AE1 % N + AE2 * N) % N = AE1 % N
    case (Sum(
              (Mod(ae1, n1)) ::
              Prod((ae2: ArithExpr) :: (n2:Var) :: Nil) ::
              Nil),
          (n3:Var))
      if n1 == n2 && n1 == n3 =>
      Some(SimplifyMod(ae1, n1))

    case (Sum(
              (Mod(ae1, n1)) ::
              Prod((n2:Var) :: (ae2: ArithExpr) :: Nil) ::
              Nil),
          (n3:Var))
      if n1 == n2 && n1 == n3 =>
      Some(SimplifyMod(ae1, n1))

    // (AE1 % N + AE2 * N + AE3 * N) % N = AE1 % N
    case (Sum(
              (Mod(ae1, n1)) ::
              Prod((n2:Var) :: (ae2: ArithExpr) :: Nil) ::
              Prod((n3:Var) :: (ae3: ArithExpr) :: Nil) ::
              Nil),
          (n4:Var))
      if n1 == n2 && n1 == n3  && n1 == n4 =>
      Some(SimplifyMod(ae1, n1))

    // (((M * j) + (2 * j) + i) % (2 + M))  == (j * (M + 2) + i) % (M + 2) == i % (M + 2)
    case (Sum(Prod((m1: Var) :: (j1:Var) :: Nil) ::
              Prod(Cst(c1) :: (j2:Var) :: Nil) ::
              (i:Var) :: Nil), Sum(Cst(c2) :: (m2: Var) :: Nil)) if m1 == m2 && j1 == j2 && c1 == c2 =>
     Some(SimplifyMod(i, Sum(m1 :: Cst(c1) :: Nil)))

    // 1_+ Ni + 2i + j % (2+N) = 1+j % (2+N) // further simplified in some cases
    case (Sum(Cst(a) ::
              Prod((n1: Var) :: (i1:Var) :: Nil) ::
              Prod(Cst(c1) :: (i2:Var) :: Nil) ::
              (j:Var) :: Nil),
          Sum(Cst(c2) :: (n2: Var) :: Nil)) if n1 == n2 && i1 == i2 && c1 == c2 =>
     Some(SimplifyMod(a + j, Sum(n1 :: Cst(c2) :: Nil)))

    // 2 + Mj + 2j + M + i % 2+M = i
    case (Sum(Cst(c1) ::
              Prod((m1: Var) :: (j1:Var) :: Nil) ::
              Prod(Cst(c2) :: (j2:Var) :: Nil) ::
              (m2:Var) :: (i:Var) :: Nil),
          Sum(Cst(c3) :: (m3: Var) :: Nil)) if m1 == m2 && m1 == m3 && j1 == j2 && c1 == c2 && c1 == c3 =>
     Some(i)

    // 4 + Mj + 2j + 2M + i % (2+M) = (2+M)(2+j) + i %  i
    case (Sum(Cst(cDouble) ::
              Prod((m1: Var) :: (j1:Var) :: Nil) ::
              Prod(Cst(c1) :: (j2:Var) :: Nil) ::
              Prod(Cst(c2) :: (m2:Var) :: Nil) ::
              (i:Var) :: Nil),
          Sum(Cst(c3) :: (m3: Var) :: Nil))
      if m1 == m2 && m1 == m3 && j1 == j2 && c1 == c2 && c1 == c3 && c1*c2 == cDouble =>
     Some(i)

    // 2+N+j % 2+N = j % 2+N if j.sign = +
    case (Sum(Cst(c1) :: (n1:Var) :: (j:Var) :: Nil),
          Sum(Cst(c2) :: (n2: Var) :: Nil))
      if n1 == n2 && c1 == c2 && j.sign == Sign.Positive =>
     Some(SimplifyMod(j, Sum(Cst(c2) :: (n2: Var) :: Nil)))

    // 1 + 2X + i + MX % 2+M = 1+i % 2+M todo think about if true in general when refactoring
    // todo do this for all special cases - how to simplify mod in sums - what about the sign of terms?
    case (Sum(Cst(c) ::
              Prod((a1:ArithExpr) :: Cst(c1) :: Nil) ::
              Prod((a2:ArithExpr) :: (m1:Var) :: Nil) ::
              (i:Var) :: Nil),
          Sum(Cst(c2) :: (m2: Var) :: Nil))
      if m1 == m2 && a1 == a2 && c1 == c2  =>
     Some(SimplifyMod(i+c, Sum(Cst(c1) :: (m2: Var) :: Nil)))

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
      case Some(toReturn) => toReturn
      case None => println(s"$dividend % $divisor not simplified"); new Mod(dividend, divisor) with SimplifiedExpr
    }
  }
}
