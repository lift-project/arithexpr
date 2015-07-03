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
   * @param numer The numerator.
   * @param denom The denominator.
   * @return An option set a to an expression if a simpler form exists, or `None` if there is no simplification.
   */
  private def simplify(numer: ArithExpr, denom: ArithExpr): Option[ArithExpr] = (numer, denom) match {
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
    case (Cst(x), Cst(y)) => Some(Cst(x / y))

    // Return zero if the denominator is smaller than the numerator
    case (x, y) if ArithExpr.isSmaller(x, y) => Some(Cst(0))

    // Flip division in the numerator
    case (IntDiv(numer, denom1), denom2) => Some(numer / (denom1 * denom2))

    // Flip fractions in the denominator
    case (numer, Pow(base, Cst(-1))) => Some(numer * base)

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

  def apply(numer: ArithExpr, denom: ArithExpr): ArithExpr = simplify(numer, denom) match {
    case Some(toReturn) => toReturn
    case None => new IntDiv(numer, denom) with SimplifiedExpr
  }
}
