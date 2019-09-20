package lift
package arithmetic
package simplifier

object SimplifyIntDiv {

  /**
    * Try to replace the expression with an equivalent simplified expression.
    *
    * @param numerator   The numerator.
    * @param denominator The denominator.
    * @return An option set a to an expression if a simpler form exists, or `None` if there is no simplification.
    */
  private def simplify(numerator: ArithExpr with SimplifiedExpr, denominator: ArithExpr with SimplifiedExpr):
  Option[ArithExpr with SimplifiedExpr] =
    (numerator, denominator) match {

      case (lift.arithmetic.?, _) | (_, lift.arithmetic.?) => Some(lift.arithmetic.?)

      case (PosInf, PosInf) | (NegInf, NegInf) | (PosInf, NegInf) | (NegInf, PosInf) => Some(?)
      case (_, PosInf) => Some(Cst(0))
      case (_, NegInf) => Some(Cst(0))
      case (PosInf, y) => y.sign match {
        case Sign.Unknown => Some(?)
        case Sign.Positive => Some(PosInf)
        case Sign.Negative => Some(NegInf)
      }
      case (NegInf, y) => y.sign match {
        case Sign.Unknown => Some(?)
        case Sign.Positive => Some(NegInf)
        case Sign.Negative => Some(PosInf)
      }

      // Simplify operands
      //    case (x, y) if !x.simplified => Some(ExprSimplifier(x) / y)
      //    case (x, y) if !y.simplified => Some(x / ExprSimplifier(y))

      // Dividing by one is a no-op
      case (numer, Cst(1)) => Some(numer)

      // Dividing zero yields zero
      case (x@Cst(0), _) => Some(x)

      // If there exists a common denominator, simplify
      case (x, y) if ArithExpr.gcd(x, y) != Cst(1) =>
        val fac = ArithExpr.gcd(x, y)
        Some((x /^ fac) / (y /^ fac))

      // Compute for constants
      case (Cst(x), Cst(y)) if y != 0 => Some(Cst(x / y))

      // Return zero if the denominator is smaller than the numerator
      case (x, y) if ArithExpr.isSmaller(x, y).getOrElse(false) => Some(Cst(0))

      // Flip division in the numerator
      case (IntDiv(numer, denom1), denom2) => Some(numer / (denom1 * denom2))

      // Flip fractions in the denominator
      case (numer, Pow(base, Cst(-1))) => Some(numer * base)

      // (AE % div) / div = 0
      case (Mod(ae1: ArithExpr, div1: ArithExpr), (div2: ArithExpr)) if (div1 == div2) => Some(Cst(0))

    // (m1 + .. + mN + x1 + .. + xN) / (m1 + .. + mN)
    // => 1 + (x1 + .. + xN) / (m1 + .. + mN)
    case (Sum(mxs), Sum(ms)) if ms.intersect(mxs) == ms =>
      Some(Cst(1) + (mxs.diff(ms).fold(0: ArithExpr)(_+_) / Sum(ms)))
    // (a + m1 + .. + mN + x1 + .. + xN) / (b + m1 + .. + mN)
    // => 1 + ((a - b) + x1 + .. + xN) / (b + m1 + .. + mN)
    case (Sum(Cst(a) :: mxs), Sum(Cst(b) :: ms))
      if ms.intersect(mxs) == ms && a >= b =>
      val x = mxs.diff(ms).fold[ArithExpr](a - b)(_+_)
      Some(Cst(1) + x / Sum(Cst(b) :: ms))

    // SPECIAL CASES

    // (a + bn) / (c + n)
    // => (a + bn - b(c + n)) + b(c + n) / (c + n)
    // => (a + b(n - c + n)) + b(c + n) / (c + n)
    // => (a - cb) + b(c + n) / (c + n)
    // => (a - cb) / (c + n) + b
    case (
      Sum(Cst(a) :: Prod(Cst(b) :: n1 :: Nil) :: Nil),
      cpn @ Sum(Cst(c) :: n2 :: Nil)
      ) if n1 == n2 && (a - c * b) >= 0 =>
      Some((a - c * b) / cpn + b)

      // cn + mn / c+m == n(c+m) / c+m => n
      case (Sum(
      Prod(Cst(c1) :: (n2: Var) :: Nil) ::
        Prod((m1: Var) :: (n1: Var) :: Nil) ::
        Nil),
      Sum(Cst(c2) :: (m2: Var) :: Nil))
        if m1 == m2 && n1 == n2 && c1 == c2 =>
        Some(n1)

      // i + ca + ma / c+m == a(c+m) + i / c+m => a true if i < c+m
      case (Sum(
      (i: Var) ::
        Prod(Cst(c1) :: (a2: ArithExpr) :: Nil) ::
        Prod((m1: Var) :: (a1: ArithExpr) :: Nil) ::
        Nil),
      Sum(Cst(c2) :: (m2: Var) :: Nil))
        if m1 == m2 && a1 == a2 && c1 == c2 &&
          ArithExpr.isSmaller(i, Cst(c2) + m2).getOrElse(false) =>
        Some(a1)

      // i + k + ca + ma / c+m == a(c+m) + k + i / c+m => a + (k+i)/(c+m) possibly often 0
      case (Sum(
      (i: ArithExpr) ::
        (k: ArithExpr) ::
        Prod(Cst(c1) :: (a2: ArithExpr) :: Nil) ::
        Prod((m1: Var) :: (a1: ArithExpr) :: Nil) ::
        Nil),
      Sum(Cst(c2) :: (m2: Var) :: Nil))
        if m1 == m2 && a1 == a2 && c1 == c2 =>
        Some(SimplifySum(a2, SimplifyIntDiv(SimplifySum(List(k: ArithExpr, i: ArithExpr)),
          SimplifySum(Cst(c2) :: (m2: Var) :: Nil))))

      // j + ck + ci + ni + nk / c+n == ((c+n)(i+k) + j) / c+n => i+k [+ j/c+n] //rather create intdiv instead?
      case (Sum(
      (j: Var) ::
        Prod((Cst(c1)) :: (i2: Var) :: Nil) ::
        Prod((Cst(c2)) :: (k2: Var) :: Nil) ::
        Prod((n1: Var) :: (i1: Var) :: Nil) ::
        Prod((n2: Var) :: (k1: Var) :: Nil) ::
        Nil),
      Sum((Cst(c3)) :: (n3: Var) :: Nil))
        if n1 == n2 && n1 == n3 && i1 == i2 && k1 == k2 && c1 == c2 && c1 == c3 &&
          ArithExpr.isSmaller(j, SimplifySum(Cst(c3) :: (n3: Var) :: Nil)).getOrElse(false) =>
        Some(SimplifySum(List(i1: Var, k1: Var)))

      // b + ca + ma / (cn + mn) == (a(m + c) + b) / n(m + c) => 0 [b/(n(c+m)) + a/n] // a=x%n
      case (Sum(
      (b: ArithExpr) ::
        Prod(Cst(c1) :: (a2: ArithExpr) :: Nil) ::
        Prod((m1: Var) :: (a1: ArithExpr) :: Nil) ::
        Nil),
      Sum(
      Prod(Cst(c2) :: (n2: Var) :: Nil) ::
        Prod((m2: Var) :: (n1: Var) :: Nil) ::
        Nil))
        if m1 == m2 && n1 == n2  && c1 == c2 && a1 == a2 &&
          ArithExpr.isSmaller(b, SimplifyProd(SimplifySum(m1 :: Cst(c1) :: Nil) :: n1 :: Nil)).getOrElse(false) &&
          ArithExpr.isSmaller(a1, n1).getOrElse(false) =>
        Some(Cst(0))

      // c1+m + i + c2j + mj / c2+m == c+m + i + j(c+m) => j+1  + c1-c2+i/c2+m
      // 3+n+j+2i+ni => (2+n)(i+1)+1+j / 2+n
      // 4+n+j+2i+ni => (2+n)(i+1)+2+j / 2+n
      case (Sum(
      Cst(c1) ::
        (m2: Var) ::
        (i: Var) ::
        Prod(Cst(c2) :: (j2: Var) :: Nil) ::
        Prod((m1: Var) :: (j1: Var) :: Nil) ::
        Nil),
      Sum(Cst(c3) :: (m3: Var) :: Nil))
        if m1 == m2 && m1 == m3 && c2 == c3 =>
        Some(SimplifySum((j1 + 1), SimplifyIntDiv(c1-c2+i, c2+m1)))

      // 4 + i + 2m + 2j + mj / 2+m = (2+m)(2+j)+i / (2+m) = 2+j true if i < 2+m
      case (Sum(
      Cst(c) ::
        (i: Var) ::
        Prod(Cst(c2) :: (m2: Var) :: Nil) ::
        Prod(Cst(c1) :: (j2: Var) :: Nil) ::
        Prod((m1: Var) :: (j1: Var) :: Nil) ::
        Nil),
      Sum(Cst(c3) :: (m3: Var) :: Nil))
        if m1 == m2 && m1 == m3 && c1 == c2 && c1 == c3  =>
        Some(SimplifySum(j1 + c2, SimplifyIntDiv(i + c-(c1*c2), c1+m1)))

      // c+n+j / c+n = 1 true if j<c+n
      case (Sum(
      Cst(c1) :: (n1: Var) :: (j: Var) :: Nil),
      Sum(Cst(c2) :: (n2: Var) :: Nil))
        if n1 == n2 && c1 == c2 &&
          ArithExpr.isSmaller(j, SimplifySum(List(c1, n2))).getOrElse(false) =>
        Some(Cst(1))

      // 3+n+j / 2+n = 1 true if 1+j < 2+n
      case (Sum(
      Cst(c1) :: (n1: Var) :: (j: Var) :: Nil),
      Sum(Cst(c2) :: (n2: Var) :: Nil))
        if n1 == n2 && c1 > c2 &&
          ArithExpr.isSmaller(c1 - c2 + j, c2 + n2).getOrElse(false) =>
        Some(Cst(1))

      // a + j + bn / n+b = b + (j + a-2b) / n+b
      // 4 + j + 2n / 2+n == 2(n+2)+j % n+2 => 2 [+ j / n+2]
      // 5 + j + 2n / 2+n == 2(n+2)+j+1 % n+2 => 2 [+ j / n+2]
      case (Sum(
      Cst(c1) ::
        (j:Var) ::
        Prod(Cst(c2) :: (n1:Var) :: Nil)::
        Nil),
      Sum(Cst(c3) :: (n2: Var) :: Nil))
        if n1 == n2 && c2 == c3 && c1 >= 0 && c2 >= 0 &&
          n1.sign == Sign.Positive && j.sign == Sign.Positive =>
        Some(SimplifySum(c2, SimplifyIntDiv(j + c1 - c2*c2, n2+c3)))

      // Pull out multiples from constants
      case (s@Sum(terms), Cst(d))
        if terms.collect({ case Cst(_) => }).nonEmpty &&
          terms.collect({ case Cst(v) => v }).head >= d =>

        val c = terms.collect({ case Cst(v) => v }).head
        Some(c/d + (s - c + c%d) / d)

      // Simplify common factors in the numerator and the denominator
      case (Sum(terms), denom) =>
        val (multiples, newTerms) = terms.partition(ArithExpr.multipleOf(_, denom))
        val newIntDivs = multiples.map(_ / denom)

        if (newIntDivs.nonEmpty) {
          if (newTerms.nonEmpty) Some(((newTerms.reduce(_ + _) / denom) :: newIntDivs).reduce(_ + _))
          else Some(newIntDivs.reduce(_ + _))
        }
        else None

      case _ => None
    }

  def apply(numer: ArithExpr with SimplifiedExpr, denom: ArithExpr with SimplifiedExpr):
  ArithExpr with SimplifiedExpr = {
    val simplificationResult = if (PerformSimplification()) simplify(numer, denom) else None
    simplificationResult match {
      case Some(toReturn) => toReturn
      case None => new IntDiv(numer, denom) with SimplifiedExpr
    }
  }
}
