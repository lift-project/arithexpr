package lift
package arithmetic
package simplifier
import ArithExprUtils.replaceAt

import scala.collection.mutable


/**
  * Simplify binary addition.
 */
object SimplifySum {

  /**
    * TODO: documentation
    * @param terms
    * @param term
    * @return
    */
  def addTerm(terms: List[ArithExpr with SimplifiedExpr], term: ArithExpr with SimplifiedExpr):
  ArithExpr with SimplifiedExpr = {
    terms.zipWithIndex.foreach {
      case (x, i) => {
        val newterm = combineTerms(term, x)
        if (newterm.isDefined) return replaceAt(i, newterm.get, terms).reduce(_ + _)
      }}

    // We didn't manage to combine the new term with any of the old terms.
    // At this point, `terms` are either terms of a sum in a normal form, or a non-normal "view" of another
    // operator expressed as a sum.
    // Note: such examples exist only if there is Sum.unapply which can construct non-normal views. Currently,
    // Sum.unapply does not exist and the logic below is in just in case it is added in the future.
    // First, transform `terms` back into normal form
    val simplifiedOriginalSum: ArithExpr with SimplifiedExpr = if (terms.length > 1) SimplifySum(terms) else terms.head
    // Then, try to combine `term` with reconstructed normal-form sum of `terms`
    combineTerms(simplifiedOriginalSum, term) match {
      case Some(simplifiedResult) => simplifiedResult
      // If simplified combination is not possible, it is safe to just prepend the term to `terms`
      // for a simplified sum
      case None =>
        new Sum((term +: terms).sortWith(ArithExpr.sort)) with SimplifiedExpr
    }
  }

  /**
   * TODO: update documentation
   * Try to combine a pair of terms.
    *
    * @param lhs The first term.
    * @param rhs The second term.
    * @return An option containing an expression if the terms can be combined, None otherwise
    */
  def combineTerms(lhs: ArithExpr with SimplifiedExpr, rhs: ArithExpr with SimplifiedExpr):
  Option[ArithExpr with SimplifiedExpr] = {
    assert(lhs.simplified && rhs.simplified)
    (lhs, rhs) match {

      case (lift.arithmetic.?, _) | (_, lift.arithmetic.?) => Some(lift.arithmetic.?)

      case (PosInf, NegInf) | (NegInf, PosInf) => Some(?)
      case (PosInf, _) | (_, PosInf) => Some(PosInf)
      case (NegInf, _) | (_, NegInf) => Some(NegInf)

      case (Cst(x), Cst(y)) => Some(Cst(x + y))
      case (Cst(0), _) => Some(rhs)
      case (_, Cst(0)) => Some(lhs)

      // Simplify terms
      // TODO: get rid of this
      // Expressions should be simplified at this point, so we shouldn't need this
//      case (x, y) if !x.simplified => Some(ExprSimplifier(x) + y)
//      case (x, y) if !y.simplified => Some(x + ExprSimplifier(y))

      // Prune zeroed vars (a Var with a range that can only be 0 should have been simplified!)
      case (x, v: Var) if v.range.min == v.range.max && v.range.min != ? => Some(x + v.range.min)
      case (v: Var, y) if v.range.min == v.range.max && v.range.min != ? => Some(y + v.range.min)

      // Modulo Identity: a = a / b * b + a % b
      case (Prod(factors), m@Mod(a, b)) if factors.reduce(_*_) == (a / b) * b => Some(a)
      case (m@Mod(a, b), Prod(factors)) if factors.reduce(_*_) == (a / b) * b => Some(a)

      // Avoid duplicates in the term list
      case (x, y) if x == y => Some(2 * x)

      case x =>
        val termsAsProds = x match {
          /* First, convert lhs and rhs to a list of factors */
          // Try to factorise in hope that the factorised sum will be simpler
          case (Prod(fs1), Prod(fs2)) => Some((fs1, fs2))

          // Merge products if they only differ by a constant fac?tor
          //      case (x, p: Prod) if p.withoutFactor(p.cstFactor) == x => Some(x * (p.cstFactor + 1))
          case (ox, Prod(fs2)) => Some((List(ox), fs2))

          //      case (p: Prod, x) if p.withoutFactor(p.cstFactor) == x => Some(x * (p.cstFactor + 1))
          case (Prod(fs1), ox) => Some((fs1, List(ox)))
          case _ => None
        }

        termsAsProds match {
          case Some((factors1, factors2)) => simplifiableByFactorisation(factors1, factors2)
          case None => None
        }
    }
  }



  /**
    * Try to factorise a sum of products in hope that the sum without common factors can be simplified
    */
  def simplifiableByFactorisation(term1factors: List[ArithExpr with SimplifiedExpr],
                                  term2factors: List[ArithExpr with SimplifiedExpr]):
  Option[ArithExpr with SimplifiedExpr] = {
    getCommonFactors(term1factors, term2factors) match {
      case (Cst(1), Nil) => None
      case (cstCommonFactor, nonCstCommonFactors) =>

        val (term1CstFactor, term1NonCstFactors) = Prod.partitionFactorsOnCst(term1factors, simplified = true)
        val (term2CstFactor, term2NonCstFactors) = Prod.partitionFactorsOnCst(term2factors, simplified = true)

        val term1WithoutCommonFactors = SimplifyProd(Cst(term1CstFactor.c / cstCommonFactor.c) +: Prod.removeFactors(term1NonCstFactors, nonCstCommonFactors))
        val term2WithoutCommonFactors = SimplifyProd(Cst(term2CstFactor.c / cstCommonFactor.c) +: Prod.removeFactors(term2NonCstFactors, nonCstCommonFactors))

        val commonFactors = cstCommonFactor match {
          case Cst(1) => nonCstCommonFactors
          case _ => cstCommonFactor +: nonCstCommonFactors
        }

        combineTerms(term1WithoutCommonFactors, term2WithoutCommonFactors) match {

          case Some(simplifiedAE) =>
            // Remaining sum has been collapsed (simplified)
            Some(simplifiedAE * SimplifyProd(commonFactors))

          case None =>
            val sumWithoutCommonFactors = term1WithoutCommonFactors + term2WithoutCommonFactors
            // No simplification of remaining sum is possible.
            // Check if it can be simplified by multiplying it by each common factor
            // We prevent infinite loop here using a flag preventing us from distributing that will lead us back here
            var simplificationAchieved: Boolean = false

            val possiblySimplifiedCommonFactors = commonFactors.map(commonFactor =>
              if (!simplificationAchieved) {
                SimplifyProd.combineFactors(sumWithoutCommonFactors, commonFactor,
                  distributionAllowed = false) match {
                  case Some(simplifiedExpr) =>
                    simplificationAchieved = true
                    simplifiedExpr

                  case None => commonFactor
                }
              } else commonFactor
            )

            if (simplificationAchieved) Some(possiblySimplifiedCommonFactors.reduce(_ * _)) else None
        }
    }
  }


  // toPowOfSum is specific to the power of 2, but is generic to any length of the sum
  def toPowOfSum(terms: List[ArithExpr with SimplifiedExpr]): Option[ArithExpr] = {
    // (a^2 + b^2 + c^2) + (2ab + 2ac + 2bc) == (a + b + c)^2
    // powerTerms + productTerms == squaredSumTerms^2
    val powerTerms: List[Pow] = terms.flatMap {
      case p: Pow => Some(p)
      case _ => None
    }
    val productTerms: List[Prod] = terms.flatMap {
      case p: Prod => Some(p) // TODO: maybe use unapply here
      case _ => None
    }

    val squaredSumTerms = powerTerms.map(_.b)

    val requiredProductTermsLength = (1 until squaredSumTerms.length).sum

    /* Check the pattern: check powers and products */
    if (terms.length != powerTerms.length + productTerms.length ||
      !powerTerms.forall(_.e == Cst(2)) ||
      // Check the number of product terms
      productTerms.length != requiredProductTermsLength ||
      // Check that each product term contains constant factor of 2
      !productTerms.forall(_.cstFactor == Cst(2)) ||
      // Check that each product term has 3 factors only
      !productTerms.forall(_.factors.length == 3) ||
      // Check that all factors of each product term are either 2 or one of the squaredSumTerms
      !productTerms.forall(_.factors.forall(factor => factor == Cst(2) ||
        squaredSumTerms.contains(factor))))
      None
    else {

      // Populate the matrix where for each pair of productTerms, their corresponding sign is saved
      var productTermSigns: mutable.Map[ArithExpr, Map[ArithExpr, Sign.Sign]] = mutable.Map()
      productTerms.foreach(productTerm => {
        val factors = productTerm.factors.filter(factor => !(factor == Cst(2)) && !(factor == Cst(-2)))
        //      val (factor0, factor1) =
        //        if (squaredSumTerms.indexOf(factors(0)) < squaredSumTerms.indexOf(factors(1))) (factors(0), factors(1))
        //        else (factors(1), factors(0))
        //
        //      if (!productTermSigns.contains(factor0)) productTermSigns += (factor0 -> Map())
        //      productTermSigns(factor0) += (factor1 -> productTerm.sign)
        if (!productTermSigns.contains(factors(0))) productTermSigns += (factors(0) -> Map())
        productTermSigns(factors(0)) += (factors(1) -> productTerm.cstFactor.sign)

        if (!productTermSigns.contains(factors(1))) productTermSigns += (factors(1) -> Map())
        productTermSigns(factors(1)) += (factors(0) -> productTerm.cstFactor.sign)
      })

      def inferSigns(squaredSumTermsToInfer: List[ArithExpr],
                     inferredSigns: Map[ArithExpr, Sign.Sign]): Option[Map[ArithExpr, Sign.Sign]] = {
        squaredSumTermsToInfer match {
          case Nil => // All terms have been inferred. Return result
            Some(inferredSigns)

          case squaredSumTerm :: remainingTerms =>
            var updatedSigns: Map[ArithExpr, Sign.Sign] = inferredSigns

          // Infer new signs based on previously inferred signs and product term signs
          productTermSigns(squaredSumTerm).foreach {
            case (secondFactor: ArithExpr, productTermSign: Sign.Sign) =>
              val inferredSecondFactorSign =
                if (inferredSigns(squaredSumTerm) == productTermSign) Sign.Positive
                else Sign.Negative

                updatedSigns =
                  if (updatedSigns.contains(secondFactor)) {
                    if (updatedSigns(secondFactor) != inferredSecondFactorSign)
                    // If we have already inferred the sign for the second factor and it is different, the very first sign
                    // we informed in this combination is incorrect
                      return None
                    else updatedSigns // We've already inferred the sign for the second factor and it's the same
                  } else (updatedSigns + (secondFactor -> inferredSecondFactorSign))
            }

          // Infer signs of the remaining squared sum terms
          inferSigns(remainingTerms, updatedSigns)
        }
      }

      // Try to infer signs with the assumption that the sign of the first squared sum term is positive.
      // If that succeeds, we found one of potentially two valid combinations ((a+b)^2 == (-a-b)^2); here we just return
      // the first one.
      // If we fail to infer a valid combination of signs, it means the the assumption is incorrect;
      // try inferring again with the new assumption that the first sign is negative.
      // If that succeeds, we got our combination.
      // If that fails, this expression is not a square of the sum.
      val signs: Option[Map[ArithExpr, Sign.Sign]] =
      inferSigns(squaredSumTerms, Map[ArithExpr, Sign.Sign](squaredSumTerms.head -> Sign.Positive)) match {
        case Some(signCombination) => Some(signCombination)
        case None =>
          inferSigns(squaredSumTerms, Map[ArithExpr, Sign.Sign](squaredSumTerms.head -> Sign.Negative))
      }
      signs match {
        case Some(signCombination) =>
          Some(SimplifyPow(
            base = squaredSumTerms.map(term => signCombination(term) match {
              case Sign.Positive => term
              case Sign.Negative => SimplifyProd(List(Cst(-1), term)) // TODO check if we want to use SimplifyProd here
              case _ => throw new IllegalArgumentException("The sign cannot be unknown at this point")
            }).reduce(_ + _),
            exp = 2))
        case None => None
      }
    }
  }

  /* Get non-constant and constant common factors from factors of two simplified Prods */
  def getCommonFactors(factors1: List[ArithExpr with SimplifiedExpr], factors2: List[ArithExpr with SimplifiedExpr]):
  (Cst, List[ArithExpr]) = {
    val (cstFactor1, nonCstFactors1) = Prod.partitionFactorsOnCst(factors1, simplified = true)

    getCommonFactors(cstFactor1, nonCstFactors1, factors2)
  }

  def getCommonFactors(cstFactor1: Cst, nonCstFactors1: List[ArithExpr with SimplifiedExpr],
                       factors2: List[ArithExpr with SimplifiedExpr]):
  (Cst, List[ArithExpr]) = {
    val (cstFactor2, nonCstFactors2) = Prod.partitionFactorsOnCst(factors2, simplified = true)

    val cstFactors: List[Long] = List(cstFactor1.c, cstFactor2.c)

    val cstCommonFactor = ComputeGCD.gcdLong(cstFactors)

    (Cst(cstCommonFactor), nonCstFactors1.intersect(nonCstFactors2))
  }


    /**
      * Try to promote the sum into another expression, then try to combine terms. If all fails the expression is simplified.
      *
      * @param lhs The left-hand side.
      * @param rhs The right-hand side.
      * @return A promoted expression or a simplified sum object.
      */
    def apply(lhs: ArithExpr with SimplifiedExpr, rhs: ArithExpr with SimplifiedExpr): ArithExpr with SimplifiedExpr = {
      if (PerformSimplification())
        ((lhs, rhs) match {
          case (s1: Sum, s2: Sum) => s2.terms.foldLeft[ArithExpr](s1)(_ + _)
          case (s1: Sum, s2@Sum(_)) => s1.terms.foldLeft[ArithExpr](s2)(_ + _)
          case (s1@Sum(_), s2: Sum) => rhs + lhs

          case (s@Sum(lhsTerms), Sum(rhsTerms)) =>
            lhsTerms.tail.foldLeft[ArithExpr](addTerm(rhsTerms, lhsTerms.head)) {
              case (acc: ArithExpr, lhsTerm) => addTerm(List(acc), lhsTerm)
            }

          case (Sum(lhsTerms), _) => addTerm(lhsTerms, rhs)
          case (_, Sum(rhsTerms)) => addTerm(rhsTerms, lhs)
          case _ =>                  addTerm(List(lhs), rhs)
        }) match {
        // Simplify by looking at all the resulting terms / factors
        // example: a^2 + 2ab + b^2 => (a + b)^2
        case s@Sum(terms) =>
          toPowOfSum(terms) match {
            case Some(x) => x
            case _ => s
          }

        case x => x
      }
      else
        new Sum(List(lhs, rhs).sortWith(ArithExpr.sort)) with SimplifiedExpr
    }

  /**
    * TODO: documentation
    */
  def apply(terms: List[ArithExpr with SimplifiedExpr]): ArithExpr with SimplifiedExpr = {
//    assume(terms.length > 1)
    if (terms.length > 1) terms.reduce(_ + _)
    else terms.head
  }
}
