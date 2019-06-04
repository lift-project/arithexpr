package lift
package arithmetic
package simplifier
import ArithExprUtils._

/**
 * Product simplifier
 */
object SimplifyProd {

  // TODO: documentation
  // Power merge is prohibited in case one of the factors is the result of temporary power
  // distribution (i.e. through extractor) since merging the powers again won't make the product simpler
  def addFactor(factors: List[ArithExpr with SimplifiedExpr], factor: ArithExpr with SimplifiedExpr,
                someFactorsComeFromSum: Boolean = true,
                someFactorsComeFromPow: Boolean = true): ArithExpr with SimplifiedExpr = {

    factors.zipWithIndex.foreach{
      case (x, i) => {
        val newfac = combineFactors(factor, x,
          distributionAllowed = !someFactorsComeFromSum,
          powerMergeAllowed = !someFactorsComeFromPow)

        if (newfac.isDefined)
          return replaceAt(i, newfac.get, factors).reduce(_ * _)
      }
    }

    // We didn't manage to combine the new factor with any of the old factors.
    // At this point, `factors` are either factors of a product in a normal form, or a non-normal "view" of another
    // operator expressed as a product product (see Prod.unapply for examples).
    // Example 1: (x*a + x*b + x*c) viewed as (x*(a+b+c)) (non-normal form)
    // Example 2: ((a * b * c)^e) viewed as (a^e * b^e * c^e) (normal form)

    // First, transform `factors` back into normal form
    // Example 1: List(x, (a+b+c)) -> x*a + x*b + x*c
    // Example 2: List(d, e, f) -> d * e * f
    val simplifiedOriginalProd: ArithExpr = if (factors.length > 1) SimplifyProd(factors) else factors.head
    // Then, try to combine `factor` with reconstructed normal-form product of `factors`
    // Example 1: combineFactors(x*a + x*b + x*c, y) => y*x*a + y*x*b + y*x*c
    // Example 2: combineFactors(d * e * f, y) => None
    combineFactors(simplifiedOriginalProd, factor) match {
      case Some(simplifiedResult) => simplifiedResult
      // If simplified combination is not possible, it is safe to just prepend the factor to `factors`
      // for a simplified product
      case None =>
        new Prod(
          (simplifiedOriginalProd match {
            case p: Prod =>
              factor +: p.factors
            case _ =>
              List(factor, simplifiedOriginalProd)
          }).sortWith(ArithExpr.sort)) with SimplifiedExpr
    }
  }

  /**
   * Try to combine a pair of factors.
   * @param lhs The first factor.
   * @param rhs The second factor.
   * @return An option containing an expression if the factors can be combined, None otherwise
   */
  def combineFactors(lhs: ArithExpr with SimplifiedExpr, rhs: ArithExpr with SimplifiedExpr,
                     distributionAllowed: Boolean = true,
                     powerMergeAllowed: Boolean = true): Option[ArithExpr with SimplifiedExpr] = {
//    assert(lhs.simplified && rhs.simplified)
    (lhs, rhs) match {

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
      // TODO: get rid of this since we expect the arguments to be simplified
//      case (x, y) if !x.simplified => Some(ExprSimplifier(x) * y)
//      case (x, y) if !y.simplified => Some(x * ExprSimplifier(y))

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
        Some(SimplifyPow(Cst((Math.pow(b1, -e1) * Math.pow(b2, -e2)).toInt), -1))

      case (Cst(x), Pow(Cst(y), Cst(e2))) if e2 < 0 && x % y == 0 =>
        Some(Cst(x / y) * SimplifyPow(Cst(y), Cst(e2 + 1)))
      case (Pow(Cst(y), Cst(e1)), Cst(x)) if e1 < 0 && x % y == 0 =>
        Some(Cst(x / y) * SimplifyPow(Cst(y), Cst(e1 + 1)))

      case (Cst(x), Pow(Cst(y), Cst(-1))) if y % x == 0 && x != -1 =>
        Some(SimplifyPow(Cst(y / x), Cst(-1)))
      case (Pow(Cst(y), Cst(-1)), Cst(x)) if y % x == 0  && x != -1 =>
        Some(SimplifyPow(Cst(y / x), Cst(-1)))


      /********** Non-constant cases **********/

      case (x, y) if x == y => Some(x pow Cst(2))

      case (x, Pow(b2, e2)) if x == b2 => Some(x pow (e2 + 1))
      case (Pow(b1, e1), x) if x == b1 => Some(x pow (e1 + 1))
      case (Pow(b1, e1), Pow(b2, e2)) if b1 == b2 => Some(b1 pow (e1 + e2))

      case (v: Var, y) if v.range.min == v.range.max && v.range.min != ? => Some(v.range.min * y)
      case (x, v: Var) if v.range.min == v.range.max && v.range.min != ? => Some(x * v.range.min)

      //    case (x, y) if x == y => Some(x pow 2)
      case (Pow(b1, e1), Pow(b2, e2)) if e1 == e2 && powerMergeAllowed => Some((b1 * b2) pow e1)

      // Distribute sums
      // distributionAllowed flag is used when trying to simplify a sum of products in SimplifySum to see if two
      // expressions can be simplified through multiplication
      case (x, s: Sum) if distributionAllowed => Some(s.terms.map(_ * x).reduce(_ + _))
      case (s: Sum, x) if distributionAllowed => Some(s.terms.map(_ * x).reduce(_ + _))


      case (x, y) => None
    }
  }

  /**
    * TODO: update documentation
   * Try to promote the product into another expression, then try to combine factors. If all fails the expression is simplified.
   * @param lhs The left-hand side.
   * @param rhs The right-hand side.
   * @return A promoted expression or a simplified Prod object.
   */
  def apply(lhs: ArithExpr with SimplifiedExpr, rhs: ArithExpr with SimplifiedExpr): ArithExpr with SimplifiedExpr = {
    if (PerformSimplification()) {
      // Whenever we unpack an expression using an extractor, set the safety flags (distributionAllowed and
      // powerMergeAllowed) based on the original type of the unpacked expression
      (lhs, rhs) match {
        case (p1: Prod, p2: Prod) => p2.factors.foldLeft[ArithExpr with SimplifiedExpr](p1)(_ * _)

        case (Prod(lhsFactors), Prod(rhsFactors)) =>
          val someFactorsComeFromSum = lhs.isInstanceOf[Sum] || rhs.isInstanceOf[Sum]
          val someFactorsComeFromPow = lhs.isInstanceOf[Pow] || rhs.isInstanceOf[Pow]

          lhsFactors.tail.foldLeft[ArithExpr with SimplifiedExpr](
            addFactor(rhsFactors, lhsFactors.head, someFactorsComeFromSum, someFactorsComeFromPow)) {

            case (acc: Prod, lhsFactor) => addFactor(acc.factors, lhsFactor, someFactorsComeFromSum, someFactorsComeFromPow)

            case (acc: ArithExpr, lhsFactor) => addFactor(List(acc), lhsFactor, someFactorsComeFromSum, someFactorsComeFromPow)
          }


        case (Prod(lhsFactors), _) => addFactor(lhsFactors, rhs,
          someFactorsComeFromSum = lhs.isInstanceOf[Sum] || rhs.isInstanceOf[Sum],
          someFactorsComeFromPow = lhs.isInstanceOf[Pow] || rhs.isInstanceOf[Pow])

        case (_, Prod(rhsFactors)) => addFactor(rhsFactors, lhs,
          someFactorsComeFromSum = lhs.isInstanceOf[Sum] || rhs.isInstanceOf[Sum],
          someFactorsComeFromPow = lhs.isInstanceOf[Pow] || rhs.isInstanceOf[Pow])

        case _ => addFactor(List(lhs), rhs)
      }
    }
    else
      new Prod(List(lhs, rhs).sortWith(ArithExpr.sort)) with SimplifiedExpr
    // TODO: There might be simplifications that require access to all or a subset of
    //  factors in the two products (lhs and rhs), then they have to be handled in
    //  apply() after addFactor.
  }

  /**
    * TODO: documentation
    */
  def apply(factors: List[ArithExpr with SimplifiedExpr]): ArithExpr with SimplifiedExpr = {
//    assume(factors.length > 1)
    factors.foldLeft[ArithExpr with SimplifiedExpr](Cst(1)) {
      case (acc, factor) => acc * factor
    }
  }
}