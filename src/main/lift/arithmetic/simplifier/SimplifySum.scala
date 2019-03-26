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
  def addTerm(terms: List[ArithExpr], term: ArithExpr): ArithExpr = {
    terms.zipWithIndex.foreach{
      case (x, i) => {
        val newterm = combineTerms(term, x)
        if (newterm.isDefined) return replaceAt(i, newterm.get, terms).reduce(_ + _)
      }}
    new Sum((term +: terms).sortWith(ArithExpr.sort)) with SimplifiedExpr
  }

  /**
   * TODO: update documentation
   * Try to combine a pair of terms.
    *
    * @param lhs The first term.
   * @param rhs The second term.
   * @return An option containing an expression if the terms can be combined, None otherwise
   */
  def combineTerms(lhs: ArithExpr, rhs: ArithExpr): Option[ArithExpr] = {
    var factorisedExpr: Option[ArithExpr] = None

    // Try to factorise a sum of products in hope that the sum without common factors can be simplified
    def simplifiableByFactorisation(factors1: List[ArithExpr], factors2: List[ArithExpr]): Boolean = {
      getCommonFactors(factors1, factors2) match {
        case Nil => false
        case commonFactors =>
          (Prod.removeFactors(commonFactors, factors1) ++
            Prod.removeFactors(commonFactors, factors2)).reduce(_ + _) match {
            // If the the sum of two factor lists without common factors is still a sum, it is not simplifiable
            case _: Sum => false // Doesn't use the extractor; only matches actual sums
            case other =>
              factorisedExpr = Some(other * new Prod(commonFactors) with SimplifiedExpr)
              true
          }
      }

    }

    (lhs, rhs) match {

      case (lift.arithmetic.?, _) | (_, lift.arithmetic.?) => Some(lift.arithmetic.?)

      case (PosInf, NegInf) | (NegInf, PosInf) => Some(?)
      case (PosInf, _) | (_, PosInf) => Some(PosInf)
      case (NegInf, _) | (_, NegInf) => Some(NegInf)

      case (Cst(x), Cst(y)) => Some(Cst(x + y))
      case (Cst(0), _) => Some(rhs)
      case (_, Cst(0)) => Some(lhs)

      // Simplify terms
      // Expressions should be simplified at this point, so we shouldn't need this
      case (x, y) if !x.simplified => Some(ExprSimplifier(x) + y)
      case (x, y) if !y.simplified => Some(x + ExprSimplifier(y))

      // Prune zeroed vars (a Var with a range that can only be 0 should have been simplified!)
      case (x, v: Var) if v.range.min == v.range.max && v.range.min != ? => Some(x + v.range.min)
      case (v: Var, y) if v.range.min == v.range.max && v.range.min != ? => Some(y + v.range.min)

      // Modulo Identity: a = a / b * b + a % b
      case (Prod(factors), m@Mod(a, b)) if factors.reduce(_*_) == (a / b) * b => Some(a)
      case (m@Mod(a, b), Prod(factors)) if factors.reduce(_*_) == (a / b) * b => Some(a)

      // Avoid duplicates in the term list
      case (x, y) if x == y => Some(2 * x)

      // Try to factorise in hope that the factorised sum will be simplier
      case (Prod(factors1), Prod(factors2)) if simplifiableByFactorisation(factors1, factors2) =>
        assume(factorisedExpr.isDefined); factorisedExpr

      // Merge products if they only differ by a constant factor
//      case (x, p: Prod) if p.withoutFactor(p.cstFactor) == x => Some(x * (p.cstFactor + 1))
      case (x, Prod(factors2)) if simplifiableByFactorisation(List(x), factors2) =>
        assume(factorisedExpr.isDefined); factorisedExpr

//      case (p: Prod, x) if p.withoutFactor(p.cstFactor) == x => Some(x * (p.cstFactor + 1))
      case (Prod(factors1), x) if simplifiableByFactorisation(factors1, List(x)) =>
        assume(factorisedExpr.isDefined); factorisedExpr

      case _ => None
    }
  }

  // toPowOfSum is specific to the power of 2, but is generic to any length of the sum
  def toPowOfSum(terms: List[ArithExpr]): Option[Pow] = {
    // (a^2 + b^2 + c^2) + (2ab + 2ac + 2bc) == (a + b + c)^2
    // powerTerms + productTerms == squaredSumTerms^2
    val powerTerms: List[Pow] = terms.flatMap {
      case p: Pow => Some(Pow(p.b, p.e))
      case _ => None
    }
    val productTerms: List[Prod] = terms.flatMap {
      // The conditional prevents us from matching powers as products
      case p: Prod/* if !p.isInstanceOf[Pow]*/ => Some(Prod(p.factors))
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
          Some(Pow(
            b = squaredSumTerms.map(term => signCombination(term) match {
              case Sign.Positive => term
              case Sign.Negative => Prod(List(Cst(-1), term))
              case _ => throw new IllegalArgumentException("The sign cannot be unknown at this point")
            }).reduce(_ + _),
            e = 2))
        case None => None
      }
    }
  }

  /* Get common factors from factors of two simplified Prods */
  def getCommonFactors(factors1: List[ArithExpr], factors2: List[ArithExpr]): List[ArithExpr] =
    factors1.intersect(factors2)


    /**
      * Try to promote the sum into another expression, then try to combine terms. If all fails the expression is simplified.
      *
      * @param lhs The left-hand side.
      * @param rhs The right-hand side.
      * @return A promoted expression or a simplified sum object.
      */
    def apply(lhs: ArithExpr, rhs: ArithExpr): ArithExpr = {
      if (PerformSimplification())
        ((lhs, rhs) match {
          case (Sum(lhsTerms), Sum(rhsTerms)) =>
            addTerm(lhsTerms, rhsTerms.head) + (
              if (rhsTerms.tail.length == 1)
                rhsTerms.tail.head
              else
                new Sum(rhsTerms.tail) with SimplifiedExpr)
          case (Sum(lhsTerms), _) => addTerm(lhsTerms, rhs)
          case (_, Sum(rhsTerms)) => addTerm(rhsTerms, lhs)
          case _ =>                  addTerm(List(lhs), rhs)
        }) match {

        // example: a^2 + 2ab + b^2 => (a + b)^2
        case s@Sum(terms) =>
          toPowOfSum(terms) match {
            case Some(p: Pow) => p
            case _ => s
          }

        // example: x * (a^2 + 2ab + b^2) => x * (a + b)^2
        case Prod(factors) =>
            new Sum(factors.map {
              case s@Sum(terms) =>
                toPowOfSum(terms) match {
                  case Some(p: Pow) => p
                  case _ => s
                }
              case x => x
            }) with SimplifiedExpr

        case x => x
      }
      else
        new Sum(List(lhs, rhs).sortWith(ArithExpr.sort)) with SimplifiedExpr
    }
}
