package lift
package arithmetic
package simplifier

import scala.collection.mutable

object SimplifySum {

  /**
    * Tries to simplify two expressions where one is a Sum by adding the new term to
    * the list of terms of the existing sum.
    * First, it tries to merge the new term from rhs with one of the lhs terms
    * from the list. If that fails, the lhs is reconstructed as a single expression; it then tries to
    * simplify reconstructed lhs with the new term from rhs using combineTerms.
    * The difference between addTerm and combineTerms is that addTerm handles cases with Sum as lhs,
    * and combineTerm doesn't.
    *
    * @param terms            A list of left hand-side (lhs) terms
    * @param term             A new term from right hand-side expression
    * @param termsComeFromSum A flag indicating whether lhs is originally a Sum and not another arithmetic
    *                         expression temporarily represented as a sum using Sum extractors
    * @return                 A simplified expression as Right if simplification was successful; a Sum object where
    *                         the new term is appended to the unchanged list of old terms as Left otherwise
    */
  def addTerm(terms: List[ArithExpr with SimplifiedExpr], term: ArithExpr with SimplifiedExpr,
              termsComeFromSum: Boolean = false):
  Either[ArithExpr with SimplifiedExpr, ArithExpr with SimplifiedExpr] = {
    terms.zipWithIndex.foreach {
      case (x, i) =>
        val newterm = combineTerms(term, x)
        if (newterm.isDefined) return Right(replaceAt(i, newterm.get, terms).reduce(_ + _))
      }

    // We didn't manage to combine the new term with any of the old terms.
    val simplifiedOriginalSum: ArithExpr with SimplifiedExpr =
      if (terms.length > 1) {
        if (termsComeFromSum) new Sum(terms) with SimplifiedExpr
        else {
          // TODO: investigate whether we can reconstruct the first expression without
          //  simplification even if it is not a Sum
          SimplifySum(terms)
        }
      } else terms.head
    // Try to combine `term` with sum of `terms`
    combineTerms(simplifiedOriginalSum, term) match {
      case Some(simplifiedResult) => Right(simplifiedResult)
      // If simplified combination is not possible, it is safe to just prepend the term to `terms`
      // for a simplified sum
      case None =>
        Left(new Sum((term +: terms).sortWith(ArithExpr.isCanonicallySorted)) with SimplifiedExpr)
    }
  }

  /**
    * Try to combine a pair of terms.
    * If one or both of the terms are Sums, no Sum-specific simplifications are applied;
    * addTerms takes care of that. If one or both of the terms are Sums that can be represented
    * as something else using extractors, then simplification is possible.
    *
    * @param lhs The first term
    * @param rhs The second term
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
      case (commonCstFactor, commonNonCstFactors) =>

        // Split common factors
        val (commonCstFractionFactor, commonNonCstFractionFactors) = Prod.partitionFactorsOnCstFraction(commonNonCstFactors)

        // Returns the term without common factors and its constant fractional part without common factors
        def removeCommonFactors(termFactors: List[ArithExpr with SimplifiedExpr]): (ArithExpr with SimplifiedExpr, ArithExpr) = {

          val (termCstFactor, termCstFracFactor, termNonCstFactors) = Prod.partitionFactorsOnCst(termFactors) match {
            case (cstFactor, nonCstFactors) if commonCstFractionFactor.isEmpty =>
              (cstFactor, Cst(1), nonCstFactors)

            case (cstFactor, nonCstFactorsWithCstFractions) =>
              val (cstFracFactor, nonCstFactors) = Prod.partitionFactorsOnCstFraction(nonCstFactorsWithCstFractions)
              (cstFactor, cstFracFactor.getOrElse(Cst(1)), nonCstFactors)
          }

          val termCstFracFactorWithoutCommonFactors =
            (commonCstFractionFactor match {
              case None => termCstFracFactor
              case Some(commonFrac) => termCstFracFactor /^ commonFrac
            }) match {
            case Cst(c) if c == 1 => new Pow(1, -1) with SimplifiedExpr
            case other => other
          }

          (SimplifyProd(
              List(Cst(termCstFactor.c / commonCstFactor.c)) ++
                Prod.removeFactors(termNonCstFactors, commonNonCstFractionFactors)),
            termCstFracFactorWithoutCommonFactors)
        }

        val (term1WithoutCommonFactorsWithoutCstFracFactor, term1CstFracFactorWithDistinctDenom) = removeCommonFactors(term1factors)
        val (term2WithoutCommonFactorsWithoutCstFracFactor, term2CstFracFactorWithDistinctDenom) = removeCommonFactors(term2factors)

        val (term1WithoutCommonFactors, term2WithoutCommonFactors) =
          (term1CstFracFactorWithDistinctDenom, term2CstFracFactorWithDistinctDenom) match {
            case (p1: Pow, p2: Pow) if !(p1.b == 1 && p2.b == 1) =>
              assert(p1.b.isInstanceOf[Cst] && p2.b.isInstanceOf[Cst])
              assert(p1.e == Cst(-1) && p2.e == Cst(-1))

              // Now that we have constant fraction common factor removed from the two terms, merge the two
              // terms (both have fractions) and try to simplify the result.
              // (a * (1/b), c * (1/d)) -> (a * (d/(b*d)), c * (b/(b*d))

              // The reason we are simplifying fractions here and not in simplify is that we want the fractions to be
              // factorized before merging to avoid large denominators

              (term1WithoutCommonFactorsWithoutCstFracFactor * p2.b,
                term2WithoutCommonFactorsWithoutCstFracFactor * p1.b)

            case _ =>
              (term1WithoutCommonFactorsWithoutCstFracFactor * term1CstFracFactorWithDistinctDenom,
                term2WithoutCommonFactorsWithoutCstFracFactor * term2CstFracFactorWithDistinctDenom)
          }

        val commonCstFractionFactorWithMergedDenominators = commonCstFractionFactor match {
          case Some(frac) => Some(frac * term1CstFracFactorWithDistinctDenom * term2CstFracFactorWithDistinctDenom)
          case None => None
          }

        val commonFactors =
          (if (commonCstFactor != Cst(1)) List(commonCstFactor) else List()) ++
            (if (commonCstFractionFactorWithMergedDenominators.isDefined)
              List(commonCstFractionFactorWithMergedDenominators.get)
            else List()) ++
            commonNonCstFractionFactors

        // Here even if we fail to simplify, we might convert into normal form using asPowOfSum inside simplify
        simplify(term1WithoutCommonFactors, term2WithoutCommonFactors) match {

          case Right(simplifiedSumWithoutCommonFactors) =>
            // Remaining sum has been collapsed (simplified)
            Some(simplifiedSumWithoutCommonFactors * SimplifyProd(commonFactors))

          case Left(nonSimplifiedSumWithoutCommonFactors) =>
            // No simplification of remaining sum is possible, but we might have converted into normal form
            // (e.g. using asPowOfSum)
            // Check if it can be simplified by multiplying it by each common factor
            // We prevent infinite loop here using a flag preventing us from distributing that will lead us back here
            var simplificationAchieved: Boolean = false

            val possiblySimplifiedCommonFactors = commonFactors.map(commonFactor =>
              if (!simplificationAchieved) {
                SimplifyProd.combineFactors(nonSimplifiedSumWithoutCommonFactors, commonFactor,
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


  /**
    * toPowOfSum converts a sum to power if possible as it is our chosen normal form.
    * Example: (a^2 + b^2 + c^2) + (2ab + 2ac + 2bc) == (a + b + c)^2
    * Most of the effort is devoted to inferring the signs of the components of the sum
    * in the base of the power.
    *
    * toPowOfSum currently only supports power of 2
    */
  def toPowOfSum(terms: List[ArithExpr with SimplifiedExpr]): Option[ArithExpr with SimplifiedExpr] = {
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
      /* Try to infer the signs of the components of the sum in the base of the power */

      // Populate the matrix where for each pair of productTerms, their corresponding sign is saved
      var productTermSigns: mutable.Map[ArithExpr, Map[ArithExpr, Sign.Sign]] = mutable.Map()
      productTerms.foreach(productTerm => {
        val factors = productTerm.factors.filter(factor => !(factor == Cst(2)) && !(factor == Cst(-2)))

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

  /**
    * Get non-constant and constant common factors from factors of two simplified Prods
    * @param factors1 First product.
    * @param factors2 Second product
    * @return A tuple of constant and non-constant common factors
    */
  def getCommonFactors(factors1: List[ArithExpr with SimplifiedExpr], factors2: List[ArithExpr with SimplifiedExpr]):
  (Cst, List[ArithExpr]) = {
    val (cstFactor1, nonCstFactors1) = Prod.partitionFactorsOnCst(factors1)

    getCommonFactors(cstFactor1, nonCstFactors1, factors2)
  }

  /**
    * Get non-constant and constant common factors from factors of two simplified Prods where the first
    * product is already factorised into constant and non-constant factors.
    * This version of getCommonFactors was added for performance, to avoid factorising the first product for
    * the second time.
    *
    * @param cstFactor1 Constant factor of the first product.
    * @param nonCstFactors1 Non-constant factors of the first product. NB: constant fractions are currently treated as non-constant factors
    * @param factors2 Second product
    * @return A tuple of constant and non-constant common factors
    */
  def getCommonFactors(cstFactor1: Cst, nonCstFactors1: List[ArithExpr with SimplifiedExpr],
                       factors2: List[ArithExpr with SimplifiedExpr]):
  (Cst, List[ArithExpr]) = {
    val (cstFactor2, nonCstFactors2) = Prod.partitionFactorsOnCst(factors2)
    val (cstFractionFactor1, nonCstFracFactors1) = Prod.partitionFactorsOnCstFraction(nonCstFactors1)
    val (cstFractionFactor2, nonCstFracFactors2) = Prod.partitionFactorsOnCstFraction(nonCstFactors2)

    val cstFactors: List[Long] = List(cstFactor1.c, cstFactor2.c)

    val cstCommonFactor = ComputeGCD.gcdLong(cstFactors)

    // TODO: apply this logic to non-cst fractions when extending ComputeGCD.apply
    val cstFractionCommonFactor = (cstFractionFactor1, cstFractionFactor2) match {

      case (Some(Pow(b1: Cst, e1: Cst)), Some(Pow(b2: Cst, e2: Cst))) =>

        assert(e1 == Cst(-1) && e2 == Cst(-1))

        val gcd = ComputeGCD.gcdLong(b1.c, b2.c)

        if (gcd == 1) List()
        else List(new Pow(gcd, -1) with SimplifiedExpr)

      case _ => List()
    }

    (Cst(cstCommonFactor), cstFractionCommonFactor ++ nonCstFracFactors1.intersect(nonCstFracFactors2))
  }


  /**
    * Try to simplify a sum of two terms. Indicate whether simplification was achieved by returning
    * either Left or Right.
    * For usages where we have to obtain the result of summing two expressions and know whether
    * the result was simplified or two expressions were just packaged into a Sum.
    *
    * @param lhs First term.
    * @param rhs Second term.
    * @return An arithmetic expression as Right if simplification was achieved; a Sum instance with
    *         lhs and rhs as terms as Left otherwise.
    */
  def simplify(lhs: ArithExpr with SimplifiedExpr, rhs: ArithExpr with SimplifiedExpr):
  Either[ArithExpr with SimplifiedExpr, ArithExpr with SimplifiedExpr] = {
    var simplified: Boolean = false


    /**
      * Unwrap the result of simplification attempt from Either into ArithExpr and
      * update the `simplified` flag if the result was Right
      */
    def updateStatus(simplificationResult: Either[ArithExpr with SimplifiedExpr, ArithExpr with SimplifiedExpr]):
    ArithExpr with SimplifiedExpr = simplificationResult match {
      case Right(simplifiedExpr) =>
        simplified = true
        simplifiedExpr
      case Left(nonSimplifiedExpr) => nonSimplifiedExpr
    }

    // Try to simplify if one or both expressions are sums or can be represented as such.
    val termWiseSimplifiedExpr: ArithExpr with SimplifiedExpr = (lhs, rhs) match {
      case (s1: Sum, s2: Sum) => s2.terms.foldLeft[ArithExpr with SimplifiedExpr](s1)(
        (acc, s2term) =>            updateStatus(simplify(acc, s2term)))
      case (s1: Sum, s2@Sum(_)) => s1.terms.foldLeft[ArithExpr with SimplifiedExpr](s2)(
        (acc, s1term) =>            updateStatus(simplify(acc, s1term)))
      case (s1@Sum(_), s2: Sum) =>  updateStatus(simplify(rhs, lhs))

      case (s@Sum(lhsTerms), Sum(rhsTerms)) =>
        lhsTerms.tail.foldLeft[ArithExpr with SimplifiedExpr](updateStatus(
          addTerm(rhsTerms, lhsTerms.head, termsComeFromSum = lhs.isInstanceOf[Sum])))(
          (acc, lhsTerm) =>         updateStatus(addTerm(List(acc), lhsTerm, termsComeFromSum = true)))

      case (Sum(lhsTerms), _) =>    updateStatus(addTerm(lhsTerms, rhs, termsComeFromSum = lhs.isInstanceOf[Sum]))
      case (_, Sum(rhsTerms)) =>    updateStatus(addTerm(rhsTerms, lhs, termsComeFromSum = rhs.isInstanceOf[Sum]))
      case _ =>                     updateStatus(addTerm(List(lhs), rhs, termsComeFromSum = false))
    }

    // Irrespectively of whether we simplified the expression or not, consider the result as a whole and try to
    // simplify as such.
    // Here we make sure that the expression is in the normal form
    val normalisedExpr = termWiseSimplifiedExpr match {
      case sum@Sum(terms) => toPowOfSum(terms) match {
        case Some(powOfSum) =>
          simplified = true
          powOfSum
        case _ => sum
      }
      case nonSumExpr => nonSumExpr
    }

    if (simplified) Right(normalisedExpr)
    else Left(normalisedExpr)
  }


  /**
    * Try to simplify the sum into another expression if simplification is enabled
    *
    * @param lhs The left-hand side.
    * @param rhs The right-hand side.
    * @return A promoted expression or a simplified sum object.
    */
    def apply(lhs: ArithExpr with SimplifiedExpr, rhs: ArithExpr with SimplifiedExpr): ArithExpr with SimplifiedExpr = {
      if (PerformSimplification())
        simplify(lhs, rhs) match {
          case Right(simplifiedExpr) => simplifiedExpr
          case Left(nonSimplifiedExpr) => nonSimplifiedExpr
      }
      else
        new Sum(List(lhs, rhs).sortWith(ArithExpr.isCanonicallySorted)) with SimplifiedExpr
    }

  /**
    * Try to simplify the sum into another expression.
    *
    * @param terms The terms of the sum to simplify.
    * @return A promoted expression or a simplified sum object.
    */
  def apply(terms: List[ArithExpr with SimplifiedExpr]): ArithExpr with SimplifiedExpr = {
    if (terms.length > 1) terms.reduce(_ + _)
    else terms.head
  }
}
