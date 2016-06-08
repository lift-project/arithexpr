package apart
package arithmetic
package simplifier

object SimplifyIntDiv {

  //  private def simplifyIntDivConstants(factors: List[ArithExpr], denomFactors: List[ArithExpr]): Option[ArithExpr] = {
  //    val (numerConstant, numerother) = factors.partition(_.isInstanceOf[Cst])
  //    val (denomConstant, demonother) = denomFactors.partition(_.isInstanceOf[Cst])
  //
  //    if (denomConstant.nonEmpty && numerConstant.nonEmpty)
  //      ExprSimplifier(numerConstant.head /^ denomConstant.head) match {
  //        case Pow(b, e) =>
  //          Some((e * Cst(-1) :: numerother).reduce(_*_) / (b :: demonother).reduce(_*_))
  //        case c: Cst =>
  //          val numer = if(numerother.nonEmpty) (c :: numerother).reduce(_*_) else c
  //          val denom = if(demonother.nonEmpty) demonother.reduce(_*_) else Cst(1)
  //          Some(numer / denom)
  //        case _ => None
  //      }
  //    else None
  //  }

  /**
    * Try to replace the expression with an equivalent simplified expression.
    *
    * @param numerator   The numerator.
    * @param denominator The denominator.
    * @return An option set a to an expression if a simpler form exists, or `None` if there is no simplification.
    */
  private def simplify(numerator: ArithExpr, denominator: ArithExpr): Option[ArithExpr] = (numerator, denominator) match {

    case (apart.arithmetic.?, _) | (_, apart.arithmetic.?) => Some(apart.arithmetic.?)

    case (PosInf, PosInf) | (NegInf, NegInf) | (PosInf, NegInf) | (NegInf, PosInf) => Some(?)
    case (_, PosInf) => Some(0)
    case (_, NegInf) => Some(0)
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
    case (x, y) if !x.simplified => Some(ExprSimplifier(x) / y)
    case (x, y) if !y.simplified => Some(x / ExprSimplifier(y))

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

    ///////////////////////////////////////////////////////////////////////////////////
    // SPECIAL CASES //todo combine cases which only differ in order of args
    ///////////////////////////////////////////////////////////////////////////////////

    // FACTORIZATION | FRACTION REDUCTION | SPLIT FRACTION IN PARTS
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
      Some(SimplifySum(a2, SimplifyIntDiv(Sum((k: ArithExpr) :: (i: ArithExpr) :: Nil),
                                          Sum(Cst(c2) :: (m2: Var) :: Nil))))

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
        ArithExpr.isSmaller(j, Sum(Cst(c3) :: (n3: Var) :: Nil)).getOrElse(false) =>
      Some(Sum((i1: Var) :: (k1: Var) :: Nil))

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
        ArithExpr.isSmaller(b, Prod(Sum(m1 :: Cst(c1) :: Nil) :: n1 :: Nil)).getOrElse(false) &&
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
        ArithExpr.isSmaller(j, Sum(c1 :: n2 :: Nil)).getOrElse(false) =>
      Some(Cst(1))

    // 3+n+j / 2+n = 1 true if 1+j < 2+n
    case (Sum(
              Cst(c1) :: (n1: Var) :: (j: Var) :: Nil),
          Sum(Cst(c2) :: (n2: Var) :: Nil))
      if n1 == n2 && c1 > c2 &&
        ArithExpr.isSmaller(c1 - c2 + j, c2 + n2).getOrElse(false) =>
      Some(Cst(1))

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

  def apply(numer: ArithExpr, denom: ArithExpr): ArithExpr = {
    val simplificationResult = if (PerformSimplification()) simplify(numer, denom) else None
    simplificationResult match {
      case Some(toReturn) => toReturn
      case None => new IntDiv(numer, denom) with SimplifiedExpr
    }
  }
}
