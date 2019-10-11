package lift
package arithmetic
package simplifier

import scala.language.postfixOps

object SimplifyMod {
  // TODO: what are the semantics for negatives?
  def simplify(dividend: ArithExpr with SimplifiedExpr, divisor: ArithExpr with SimplifiedExpr):
  Option[ArithExpr with SimplifiedExpr] =
    (dividend, divisor) match {
  
    case (arithmetic.?, _) | (_, arithmetic.?) => Some(?)

    // Simplify operands
//    case (x, y) if !x.simplified => Some(ExprSimplifier(x) % y)
//    case (x, y) if !y.simplified => Some(x % ExprSimplifier(y))

    ///////////////////////////////////////////////////////////////////////////////////
    // SPECIAL CASES //todo combine cases which only differ in order of args
    ///////////////////////////////////////////////////////////////////////////////////

    // (a + bn) % (c + n)
    // => (a + bn - b(c + n)) + b(c + n) % (c + n)
    // => (a + b(n - c + n)) % (c + n)
    // => (a - cb) % (c + n)
    case (
      Sum(Cst(a) :: Prod(Cst(b) :: n1 :: Nil) :: Nil),
      cpn @ Sum(Cst(c) :: n2 :: Nil)
      ) if n1 == n2 && (a - c * b) >= 0 =>
      Some((a - c * b) % cpn)

    // (a + x + n/b) % (c + n/db)
    // => a + x + d(c + n/db) - dc % (c + n/db)
    // => a - dc + x % (c + n/db)
    case (Sum(xs), cpndb) if {
      val a = xs match {
        case Cst(a) :: _ => a
        case _ => 0: Long
      }
      (cpndb match {
        case Sum(Cst(c) :: AnyDiv(n, Cst(db)) :: Nil) => Some(c, n, db)
        case AnyDiv(n, Cst(db)) => Some(0: Long, n, db)
        case _ => None
      }) match {
        case Some((c, n, db)) =>
          xs.exists {
            case AnyDiv(n2, Cst(b)) =>
              (n == n2) && (db % b == 0) && (a - (db / b)*c >= 0)
            case _ => false
          }
        case _ => false
      }
    } =>
      val a = xs match {
        case Cst(a) :: _ => a
        case _ => 0: Long
      }
      val (c, n, db) = cpndb match {
        case Sum(Cst(c) :: AnyDiv(n, Cst(db)) :: Nil) => (c, n, db)
        case AnyDiv(n, Cst(db)) => (0: Long, n, db)
      }
      val ndbs = xs collect { case ndb @ AnyDiv(n2, Cst(b)) if (n == n2) && (db % b == 0) && (a - (db / b)*c >= 0) => ndb }
      val ndb = ndbs.head
      val b = ndb match { case AnyDiv(_, Cst(b)) => b }
      val d = db / b
      val rest = xs.diff(Seq(ndb)).fold(-d*c: ArithExpr)(_+_)
      Some(rest % cpndb)

    // x + cn + mn % c+m  =>  x + n(c+m) % c+m  =>  x % c+m
    case (Sum(xs), cpm @ Sum(Cst(c) :: m :: Nil)
      ) if {
      xs.exists {
        case Prod(Cst(c2) :: n :: Nil) if c == c2 =>
          xs.exists {
            case Prod(a :: b :: Nil) => (a == n && b == m) || (a == m && b == n)
            case _ => false
          }
        case _ => false
      }
    } =>
      val ns = xs collect { case Prod(Cst(c2) :: n :: Nil) if c == c2 => n }
      val nms = xs collect {
        case nm @ Prod(a :: b :: Nil)
          if (a == m && ns.contains(b)) || (b == m && ns.contains(a)) => nm
      }
      nms.head match {
        case nm @ Prod(a :: b :: Nil) =>
          val n = if (b == m) { a } else { b }
          val x = xs.diff(Seq(Prod(Cst(c) :: n :: Nil), nm))
            .fold(0: ArithExpr)(_+_)
          Some(x % cpm)
      }

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
      Some(SimplifyMod(SimplifySum(k :: i :: Nil), SimplifySum(Cst(c1) :: m1 :: Nil)))

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

    // a + j + bn / n+b = b(n+b) + j + a-2b % n+b
    // 4 + j + 2n % 2+n == 2(n+2)+j % n+2 => j % n+2
    // 5 + j + 2n % 2+n == 2(n+2)+j+1 % n+2 => j+1 % n+2
    case (Sum(
              Cst(c1) ::
              (j:Var) ::
              Prod(Cst(c2) :: (n1:Var) :: Nil)::
              Nil),
          Sum(Cst(c3) :: (n2: Var) :: Nil))
      if n1 == n2 && c2 == c3 && c1 >= 0 && c2 >= 0 &&
        n1.sign == Sign.Positive && j.sign == Sign.Positive =>
     Some(SimplifyMod((j + c1-c2*c2), n1+c3))

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

    // (m1 + .. + mN + x1 + .. + xN) % (m1 + .. + mN)
    // => (x1 + .. + xN) % (m1 + .. + mN)
    case (Sum(mxs), Sum(ms)) if ms.intersect(mxs) == ms =>
      Some(mxs.diff(ms).fold(0: ArithExpr)(_+_) % Sum(ms))
    // (a + m1 + .. + mN + x1 + .. + xN) % (b + m1 + .. + mN)
    // => ((a - b) + x1 + .. + xN) % (b + m1 + .. + mN)
    case (Sum(Cst(a) :: mxs), Sum(Cst(b) :: ms)) if ms.intersect(mxs) == ms =>
      val x = mxs.diff(ms).fold[ArithExpr](a - b)(_+_)
      Some(x % Sum(Cst(b) :: ms))

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

    // If the dividend is a product, try to find the divisor. Finding the GCD below should make this redundant, but the
    // GCD method does not return fractions, but the divisor could be one.
    case (Prod(factors), x) if factors.contains(x) && !ArithExpr.hasDivision(factors) => Some(Cst(0))

    // If there exists a common denominator, simplify
    case (x, y) if ArithExpr.gcd(x,y) == y => Some(Cst(0))

    // Apply mod to constants
    case (s@Sum(terms), Cst(d))
      if terms.collect({ case Cst(_) => }).nonEmpty &&
        terms.collect({ case Cst(v) => v }).head >= d &&
        // none of the terms can be negative: (3 - i))  % 3
        //                                       ^ might be negative
        !terms.map(t => ArithExpr.mightBeNegative(t)).fold(false)(_ || _) =>

      val c = terms.collect({ case Cst(v) => v }).head
      Some((s - c + c%d) % d)

    // Isolate the terms which are multiple of the mod and eliminate
    case (s: Sum, d) if !ArithExpr.mightBeNegative(s) =>
      val (multiple, _) = s.terms.partition(t => (t, d) match {
        case (Prod(factors1), Prod(factors2)) => factors2 forall (factors1 contains)
        case (Prod(factors), x) if factors.contains(x) => true
        case (x, y) if ArithExpr.multipleOf(x, y) => true
        case (x, y) => ArithExpr.gcd(x, y) == y
      })
      val shorterSum = s.withoutTerm(multiple)
      if (multiple.isEmpty) return None
      if (ArithExpr.mightBeNegative(shorterSum)) {
        (shorterSum, d) match {
          // TODO: generalize
          case (Cst(a), Cst(b)) if a < 0 && b > 0 && (a + b) >= 0 =>
            return Some((a + b) % d)
          case _ =>
            return None
        }
      }
      Some(shorterSum % d)

    case _ => None
  }

  def apply(dividend: ArithExpr with SimplifiedExpr, divisor: ArithExpr with SimplifiedExpr):
  ArithExpr with SimplifiedExpr = {
    val simplificationResult = if (PerformSimplification()) simplify(dividend, divisor) else None
    simplificationResult match {
      case Some(toReturn) => toReturn
      case None => new Mod(dividend, divisor) with SimplifiedExpr
    }
  }
}
