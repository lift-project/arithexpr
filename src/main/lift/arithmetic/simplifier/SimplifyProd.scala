package lift
package arithmetic
package simplifier
import ArithExprUtils.replaceAt

/**
 * Product simplifier
 */
object SimplifyProd {

  // TODO: documentation
  def addFactor(factors: List[ArithExpr], factor: ArithExpr): ArithExpr = {
    factors.zipWithIndex.foreach{
      case (x, i) => {
        val newfac = combineFactors(factor, x)
        if (newfac.isDefined) return replaceAt(i, newfac.get, factors).reduce(_ * _)
      }}
    new Prod((factor +: factors).sortWith(ArithExpr.sort)) with SimplifiedExpr
  }

  /**
   * Try to combine a pair of factors.
   * @param lhs The first factor.
   * @param rhs The second factor.
   * @return An option containing an expression if the factors can be combined, None otherwise
   */
  def combineFactors(lhs: ArithExpr, rhs: ArithExpr): Option[ArithExpr] = (lhs, rhs) match {

    case (lift.arithmetic.?,_) | (_,lift.arithmetic.?) => Some( lift.arithmetic.? )

    case (PosInf, NegInf) | (NegInf, PosInf)  => Some(NegInf)
    case (PosInf, PosInf) | (NegInf, NegInf)  => Some(PosInf)
    case (PosInf, y) => y.sign match {
      case Sign.Unknown => Some(?)
      case Sign.Positive => Some(PosInf)
      case Sign.Negative => Some(NegInf)
    }
    case (x, PosInf) =>  x.sign match {
      case Sign.Unknown => Some(?)
      case Sign.Positive => Some(PosInf)
      case Sign.Negative => Some(NegInf)
    }
    case (NegInf, y) =>  y.sign match {
      case Sign.Unknown => Some(?)
      case Sign.Positive => Some(NegInf)
      case Sign.Negative => Some(PosInf)
    }
    case (x, NegInf) =>  x.sign match {
      case Sign.Unknown => Some(?)
      case Sign.Positive => Some(NegInf)
      case Sign.Negative => Some(PosInf)
    }

    // Factor simplification
    case (x, y) if !x.simplified => Some(ExprSimplifier(x) * y)
    case (x, y) if !y.simplified => Some(x * ExprSimplifier(y))

    // Constant product
    case (Cst(x), Cst(y)) => Some(Cst(x * y))

    // Multiplication by zero
    case (Cst(0), _) | (_, Cst(0)) => Some(Cst(0))

    // TODO enable this when min and max are tested
    // The the evaluation yields 0, return 0
    //case (x, y) if x.max == 0 => Some(Cst(0))
    //case (x, y) if y.max == 0 => Some(Cst(0))

    // Multiplication by one
    case (Cst(1), _) => Some(rhs)
    case (_, Cst(1)) => Some(lhs)

    /********** Constant cases **********/

    // Compute powers when all bases and exponents are positive constants
    case (Pow(Cst(b1), Cst(e1)), Pow(Cst(b2), Cst(e2))) if e1 > 0 && e2 > 0 =>
      Some(Cst((Math.pow(b1, e1) * Math.pow(b2, e2)).toInt))

    // Compute powers when all bases and exponents are negative constants
    case (Pow(Cst(b1), Cst(e1)), Pow(Cst(b2), Cst(e2))) if e1 < 0 && e2 < 0 =>
      Some(Pow(Cst((Math.pow(b1, -e1) * Math.pow(b2, -e2)).toInt), -1))

    case (Cst(x), Pow(Cst(y), Cst(e2))) if e2 < 0 && x % y == 0 =>
      Some(Cst(x / y) * Pow(Cst(y), Cst(e2 + 1)))
    case (Pow(Cst(y), Cst(e1)), Cst(x)) if e1 < 0 && x % y == 0 =>
      Some(Cst(x / y) * Pow(Cst(y), Cst(e1 + 1)))

    /********** Non-constant cases **********/

    case (x, y) if x == y => Some(x pow Cst(2))

    case (x, Pow(b2, e2)) if x == b2 => Some(x pow (e2 + 1))
    case (Pow(b1, e1), x) if x == b1 => Some(x pow (e1 + 1))
    case (Pow(b1, e1), Pow(b2, e2)) if b1 == b2 => Some(b1 pow (e1 + e2))

    case (v: Var, y) if v.range.min == v.range.max && v.range.min != ? => Some(v.range.min * y)
    case (x, v: Var) if v.range.min == v.range.max && v.range.min != ? => Some(x * v.range.min)

//    case (x, y) if x == y => Some(x pow 2)
    case (Pow(b1, e1), Pow(b2, e2)) if e1 == e2 => Some((b1 * b2) pow e1)

    // Distribute sums
    case (x, s: Sum) => Some(s.terms.map(_ * x).reduce(_ + _))
    case (s: Sum, x) => Some(s.terms.map(_ * x).reduce(_ + _))


    case (x, y) => None
  }

  /**
    * TODO: update documentation
   * Try to promote the product into another expression, then try to combine factors. If all fails the expression is simplified.
   * @param lhs The left-hand side.
   * @param rhs The right-hand side.
   * @return A promoted expression or a simplified Prod object.
   */
  def apply(lhs: ArithExpr, rhs: ArithExpr): ArithExpr = {
    if (PerformSimplification())
      (lhs, rhs) match {
        case (Prod(lhsFactors), Prod(rhsFactors)) =>
          addFactor(lhsFactors, rhsFactors.head) * (
            if (rhsFactors.tail.length == 1)
              rhsFactors.tail.head
            else
              new Prod(rhsFactors.tail) with SimplifiedExpr)
        case (Prod(lhsFactors), _) => addFactor(lhsFactors, rhs)
        case (_, Prod(rhsFactors)) => addFactor(rhsFactors, lhs)
        case _ =>                     addFactor(List(lhs), rhs)
      }
    else
      new Prod(List(lhs, rhs).sortWith(ArithExpr.sort)) with SimplifiedExpr
    // TODO: There might be simplifications that require access to all or a subset of
    //  factors in the two products (lhs and rhs), then they have to be handled in
    //  apply() after addFactor.
  }
}