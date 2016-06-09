package apart
package arithmetic
package simplifier

object SimplifyIntDiv {

  /**
   * Try to replace the expression with an equivalent simplified expression.
    *
    * @param numerator The numerator.
   * @param denominator The denominator.
   * @return An option set a to an expression if a simpler form exists, or `None` if there is no simplification.
   */
  private def simplify(numerator: ArithExpr, denominator: ArithExpr): Option[ArithExpr] = (numerator, denominator) match {

    case (apart.arithmetic.?,_) | (_,apart.arithmetic.?) => Some( apart.arithmetic.? )

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

    // special cases //todo combine cases which only differ in order of args
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

    // Pull out multiples from constants
    case (s@Sum(terms), Cst(d))
      if terms.collect({ case Cst(_) => }).nonEmpty &&
        terms.collect({ case Cst(v) => v }).head >= d =>

      val c = terms.collect({ case Cst(v) => v }).head
      Some(c/d + (s - c + c%d) / d)

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
