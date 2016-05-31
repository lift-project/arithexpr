package apart
package arithmetic
package simplifier

object SimplifyIntDiv {

  private def simplifyIntDivConstants(factors: List[ArithExpr], denomFactors: List[ArithExpr]): Option[ArithExpr] = {
    val (numerConstant, numerother) = factors.partition(_.isInstanceOf[Cst])
    val (denomConstant, demonother) = denomFactors.partition(_.isInstanceOf[Cst])

    if (denomConstant.nonEmpty && numerConstant.nonEmpty)
      ExprSimplifier(numerConstant.head /^ denomConstant.head) match {
        case Pow(b, e) =>
          Some((e * Cst(-1) :: numerother).reduce(_*_) / (b :: demonother).reduce(_*_))
        case c: Cst =>
          val numer = if(numerother.nonEmpty) (c :: numerother).reduce(_*_) else c
          val denom = if(demonother.nonEmpty) demonother.reduce(_*_) else Cst(1)
          Some(numer / denom)
        case _ => None
      }
    else None
  }

  /**
   * Try to replace the expression with an equivalent simplified expression.
    *
    * @param numer The numerator.
   * @param denom The denominator.
   * @return An option set a to an expression if a simpler form exists, or `None` if there is no simplification.
   */
  private def simplify(numer: ArithExpr, denom: ArithExpr): Option[ArithExpr] = (numer, denom) match {

    case (?,_) | (_,?) => Some(?)

    case (PosInf, PosInf) | (NegInf, NegInf) | (PosInf, NegInf) | (NegInf, PosInf)  => Some(?)
    case (_, PosInf) => Some(0)
    case (_, NegInf) => Some(0)
    case (PosInf, y) => y.sign match {
      case Sign.Unknown => Some(?)
      case Sign.Positive => Some(PosInf)
      case Sign.Negative => Some(NegInf)
    }
    case (NegInf, y) =>  y.sign match {
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
    case (x, y) if ArithExpr.gcd(x,y) != Cst(1) =>
      val fac = ArithExpr.gcd(x,y)
      Some((x/^fac) / (y/^fac))

    // Compute for constants
    case (Cst(x), Cst(y)) if y != 0 => Some(Cst(x / y))

    // Return zero if the denominator is smaller than the numerator
    case (x, y) if ArithExpr.isSmaller(x, y).getOrElse(false) => Some(Cst(0))

    // Flip division in the numerator
    case (IntDiv(numer, denom1), denom2) => Some(numer / (denom1 * denom2))

    // Flip fractions in the denominator
    case (numer, Pow(base, Cst(-1))) => Some(numer * base)

    // (AE % div) / div = 0
    case (Mod(ae1:ArithExpr, div1: ArithExpr), (div2: ArithExpr)) if (div1 == div2) => Some(Cst(0))

    // special cases //todo combine cases which only differ in order of args
     case (Sum(
              Prod(Mod((ae1: ArithExpr), (n1:Var)) :: (m1:Var) :: Nil) ::
              Prod(Mod((ae2: ArithExpr), (n2:Var)) :: Cst(c1) :: Nil) ::
              (ae3: ArithExpr) :: Nil),
          Sum(
              Prod((m2:Var) :: (n3:Var) :: Nil) ::
              Prod(Cst(c2) :: (n4: Var) :: Nil) :: Nil))
      if m1 == m2 && n1 == n2 && n1 == n3 && n1 == n4 && c1 == c2 &&
        ArithExpr.isSmaller(ae3, Prod(Sum(m1 :: Cst(c1) :: Nil) :: n1 :: Nil)).getOrElse(false) =>
      Some(Cst(0))

    // (j * (c + m) + i) / (c + m) = j true if i < (4+M)
    case (Sum(
              Prod((m1: Var) :: (j1: ArithExpr) :: Nil) ::
              Prod(Cst(c1) :: (j2: ArithExpr) :: Nil) ::
              (i:Var) ::
              Nil),
          Sum(Cst(c2) :: (m2: Var) :: Nil))
      if m1 == m2 && j1 == j2 && c1 == c2 && ArithExpr.isSmaller(i, Sum(Cst(c2) :: (m2: Var) :: Nil)).getOrElse(false) =>
      Some(j1)

    case (Sum(
              Prod((i1: ArithExpr) :: Cst(c1) :: Nil) ::
              Prod((i2: ArithExpr) :: (n1: Var) :: Nil) ::
              (j:Var) ::
              Nil),
          Sum(Cst(c2) :: (n2: Var) :: Nil))
      if n1 == n2 && i1 == i2 && c1 == c2 && ArithExpr.isSmaller(j, Sum(Cst(c2) :: (n2: Var) :: Nil)).getOrElse(false) =>
      Some(i1)

    case (Sum(
              Prod(Cst(c1) :: (i1: ArithExpr) :: Nil) ::
              Prod((i2: ArithExpr) :: (n1: Var) :: Nil) ::
              (j:Var) ::
              Nil),
          Sum(Cst(c2) :: (n2: Var) :: Nil))
      if n1 == n2 && i1 == i2 && c1 == c2 && ArithExpr.isSmaller(j, Sum(Cst(c2) :: (n2: Var) :: Nil)).getOrElse(false) =>
      Some(i1)

    // recreate ((2+M) * (2+N)) / (2+M) = 2+N
    case (Sum(
              Cst(c1) ::
              Prod((n1: Var) :: (m1: Var) :: Nil) ::
              Prod(Cst(c2) :: (n2: Var) :: Nil) ::
              Prod(Cst(c3) :: (m2: Var) :: Nil) ::
              Nil),
          Sum(Cst(c4) :: (m3: Var) :: Nil))
      if m1 == m2 && m2 == m3 && n1 == n2 && c4 == c2 && c2 == c3 && c1 == c2*c3 =>
      Some(c2 + n1)

    // recreate ((2+M) * (2+N)) / (2+N) = 2+M
    case (Sum(
              Cst(c1) ::
              Prod((n1: Var) :: (m1: Var) :: Nil) ::
              Prod(Cst(c2) :: (n2: Var) :: Nil) ::
              Prod(Cst(c3) :: (m2: Var) :: Nil) ::
              Nil),
          Sum(Cst(c4) :: (n3: Var) :: Nil))
      if m1 == m2 && n2 == n3 && n1 == n2 && c4 == c2 && c2 == c3 && c1 == c2*c3 =>
      Some(c2 + m1)

    case (Sum(
             Prod((a1:ArithExpr) :: (m1:Var) :: Nil) ::
             Prod(Cst(c1) :: (a2:ArithExpr) :: Nil) ::
             (e:ArithExpr) :: Nil),
         Sum(Cst(c2) :: (m2: Var) :: Nil))
     if m1 == m2 && a1 == a2 && c1 == c2 && ArithExpr.isSmaller(e, m1+2).getOrElse(false) =>
      Some(a1)

    case (Sum(
             Prod((a1:ArithExpr) :: (m1:Var) :: Nil) ::
             Prod((a2:ArithExpr) :: Cst(c1) :: Nil) ::
             (e:ArithExpr) :: Nil),
         Sum(Cst(c2) :: (m2: Var) :: Nil))
     if m1 == m2 && a1 == a2 && c1 == c2 && ArithExpr.isSmaller(e, m1+2).getOrElse(false) =>
      Some(a1)

    case (Sum(
             Prod((a2:ArithExpr) :: Cst(c1) :: Nil) ::
             Prod((a1:ArithExpr) :: (m1:Var) :: Nil) ::
             (e:ArithExpr) :: Nil),
         Sum(Cst(c2) :: (m2: Var) :: Nil))
     if m1 == m2 && a1 == a2 && c1 == c2 && ArithExpr.isSmaller(e, m1+2).getOrElse(false) =>
      Some(a1)

    case (Sum(
             Prod(Cst(c1) :: (j2:Var) :: Nil) ::
             Prod((j1:Var) :: (m1: Var) :: Nil) ::
             (i:Var) :: Nil),
         Sum(Cst(c2) :: (m2: Var) :: Nil))
     if m1 == m2 && j1 == j2 && c1 == c2 && ArithExpr.isSmaller(i, m1+2).getOrElse(false) =>
      Some(j1)

    // ((M * j) + (2 * j) + i) / (2 + M) == j + i/(M+2) == j true if i < (M+2)
    case (Sum(
             Prod((m1: Var) :: (j1:Var) :: Nil) ::
             Prod(Cst(c1) :: (j2:Var) :: Nil) ::
             (i:Var) :: Nil),
         Sum(Cst(c2) :: (m2: Var) :: Nil))
     if m1 == m2 && j1 == j2 && c1 == c2 && ArithExpr.isSmaller(i, m1+2).getOrElse(false) =>
      Some(j1)

    // (M*N + 2*N) / (2+M) = N
    case (Sum(
              Prod((m1: Var) :: (n1: Var) :: Nil) ::
              Prod(Cst(c1) :: (n2: Var) :: Nil) ::
              Nil),
          Sum(Cst(c2) :: (m2: Var) :: Nil))
      if m1 == m2 && n1 == n2 && c1 == c2 =>
      Some(n1)

    case (Sum(
              Prod((n1: Var) :: (m1: Var) :: Nil) ::
              Prod(Cst(c1) :: (n2: Var) :: Nil) ::
              Nil),
          Sum(Cst(c2) :: (m2: Var) :: Nil))
      if m1 == m2 && n1 == n2 && c1 == c2 =>
      Some(n1)

    // Simplify common factors in the numerator and the denominator
    case (Sum(terms), denom) =>
      val (multiples,newTerms) = terms.partition(ArithExpr.multipleOf(_, denom))
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
