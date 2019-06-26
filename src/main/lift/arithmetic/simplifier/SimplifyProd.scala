package lift
package arithmetic
package simplifier

/**
 * Product simplifier
 */
object SimplifyProd {

  /**
    * Tries to simplify two expressions where one is a product by adding the new factor to
    * the list of factors of the existing product.
    *
    * First, it tries to merge the new factor with one of the factors from the list.
    * Here, we make sure to indicate whether factor distribution and power merge are allowed because if
    * either left or right hand-side expressions are temporary representations (factorised Sums or factorised Powers),
    * the distribution and power merge would simply undo the conversion and will try to simplify the result
    * resulting in an infinite recursion.
    *
    * If the factorwise simplification was not possible, we use combineFactors to simplify as if neither
    * of the two expressions where products.
    *
    * @param factors The product from the first expression represented as its factors
    * @param factor The second expression
    * @param factorsComeFromProd    Indicates whether the first expression is a product (then we don't need
    *                               to reconstruct the expression through costly SimplifyProd)
    * @param someFactorsComeFromSum Indicates whether one of the factors in `factors` or the `factor` come from a
    *                               temporary representation of a Sum as a product -- since that would be achieved
    *                               by factorisation, we have to prevent its reversal
    * @param someFactorsComeFromPow Indicates whether one of the factors in `factors` or the `factor` come from a
    *                               temporary representation of a Pow as a product -- since that would be achieved
    *                               by factorisation, we have to prevent its reversal
    * @return                       A simplified expression as Right if simplification was successful; a Prod object
    *                               where the new factor is appended to the unchanged list of old terms as Left otherwise
    */
  def addFactor(factors: List[ArithExpr with SimplifiedExpr], factor: ArithExpr with SimplifiedExpr,
                factorsComeFromProd: Boolean = false,
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
    val simplifiedOriginalProd: ArithExpr =
    if (factors.length > 1) {
      // Example 1: List(d, e, f) -> d * e * f
      if (factorsComeFromProd) new Prod(factors) with SimplifiedExpr
      else {
        // TODO: investigate whether we can reconstruct the first expression without
        //  simplification even if it is not a Prod
        // Example 2: List(x, (a+b+c)) -> x*a + x*b + x*c
        SimplifyProd(factors)
      }
    } else factors.head

    // Then, try to combine `factor` with reconstructed normal-form product of `factors`
    combineFactors(simplifiedOriginalProd, factor) match {
      // Example 2: combineFactors(x*a + x*b + x*c, y) => y*x*a + y*x*b + y*x*c
      case Some(simplifiedResult) => simplifiedResult
      // Example 1: combineFactors(d * e * f, y) => None
      // If simplified combination is not possible, it is safe to just prepend the factor to `factors`
      // for a simplified product
      case None =>
        new Prod(
          (simplifiedOriginalProd match {
            case p: Prod =>
              factor +: p.factors
            case _ =>
              List(factor, simplifiedOriginalProd)
          }).sortWith(ArithExpr.isCanonicallySorted)) with SimplifiedExpr
    }
  }

  /**
    * Try to combine a pair of factors.
    * If one or both of the factors are Prods themselves, no Prod-specific optimisations are applied;
    * addFactor takes care of that. If one or both of the factors are Prods that can be represented
    * as something else using extractors, then simplification is possible.
    *
    * @param lhs The first factor
    * @param rhs The second factor
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
    * Try to promote the product into another expression.
    *
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
            addFactor(rhsFactors, lhsFactors.head, rhs.isInstanceOf[Prod],
              someFactorsComeFromSum, someFactorsComeFromPow)) {

            case (acc: Prod, lhsFactor) => addFactor(acc.factors, lhsFactor, factorsComeFromProd = true,
              someFactorsComeFromSum, someFactorsComeFromPow)

            case (acc: ArithExpr, lhsFactor) => addFactor(List(acc), lhsFactor, factorsComeFromProd = true,
              someFactorsComeFromSum, someFactorsComeFromPow)
          }


        case (Prod(lhsFactors), _) => addFactor(lhsFactors, rhs,
          factorsComeFromProd = lhs.isInstanceOf[Prod],
          someFactorsComeFromSum = lhs.isInstanceOf[Sum] || rhs.isInstanceOf[Sum],
          someFactorsComeFromPow = lhs.isInstanceOf[Pow] || rhs.isInstanceOf[Pow])

        case (_, Prod(rhsFactors)) => addFactor(rhsFactors, lhs,
          factorsComeFromProd = rhs.isInstanceOf[Prod],
          someFactorsComeFromSum = lhs.isInstanceOf[Sum] || rhs.isInstanceOf[Sum],
          someFactorsComeFromPow = lhs.isInstanceOf[Pow] || rhs.isInstanceOf[Pow])

        case _ => addFactor(List(lhs), rhs)
      }
    }
    else
      new Prod(List(lhs, rhs).sortWith(ArithExpr.isCanonicallySorted)) with SimplifiedExpr
  }

  /**
    * Try to promote the product into another expression.
    *
    * @param factors The factors of the product to simplify
    * @return
    */
  def apply(factors: List[ArithExpr with SimplifiedExpr]): ArithExpr with SimplifiedExpr = {
    factors.foldLeft[ArithExpr with SimplifiedExpr](Cst(1)) {
      case (acc, factor) => acc * factor
    }
  }
}
