package lift.arithmetic.simplifier

import ir.arithexpr_extension.PrecomputedFunctionCall
import lift.arithmetic.Predicate.Operator
import lift.arithmetic._

object SimplifyBigSum {
  private def boundsOverlap(bigSum: BigSum) = {
      bigSum.stop.isEvaluable && bigSum.start.isEvaluable && ArithExpr.isSmaller(bigSum.stop.max,bigSum.start.min).contains(true)
  }

  def apply(bigSum: BigSum):ArithExpr = {
    val result = if (ArithExpr.visitUntil(bigSum.stop, {
      case _:PrecomputedFunctionCall => true
      case _ => false
    })) {
      bigSum
    }
    //preemptively attempt to lift out expression if not contained
    else if(boundsOverlap(bigSum)) {
      Cst(0)
    }
    else
      splitTerms(bigSum)
    result
  }

  private def splitTerms(bigSum: BigSum):ArithExpr = {
    bigSum.body match {
      case Sum(terms) =>
        //Split each term in it's own sum, then simplify it
        terms.map(term =>
          SimplifyBigSum(bigSum.copy(body = term)
        )).reduce(_ + _)

      case _ => simplifyFactors(bigSum)
    }
  }

  private def makeProd(exprs:List[ArithExpr]):ArithExpr = exprs match {
    case List(justThis) => justThis
    case other => other.reduce(_ * _)
  }

  private def simplifyFactors(bigSum: BigSum):ArithExpr = {
    bigSum.body match {
      case Prod(factors) =>
        val (stayingIn, liftedOut) = factors.partition(expr => expr.contains(bigSum.iterationVariable))
        //If we lifted out all of the constant factors, then we should leave a Cst(1) behind...
        val newBody = stayingIn match {
          case Nil => Cst(1)
          case other => makeProd(other)
        }

        val prod = makeProd(liftedOut)
        val newSum = SimplifyBigSum(bigSum.copy(body = newBody))
        val result = Prod(List(prod, newSum))
        result
      case _ => finalPhase(bigSum)
    }
  }

  private def finalPhase(bigSum: BigSum):ArithExpr = {
    bigSum.body match {
      case _: IfThenElse =>
        ifElimination(bigSum)
      case _ =>
        //EULER FORMULA
        if (bigSum.body == bigSum.iterationVariable && bigSum.start == Cst(0)) {
          (bigSum.stop * (bigSum.stop + 1)) / 2
        } //Sum of powers of two
        else if(bigSum.body == Pow(Cst(2), bigSum.iterationVariable) && bigSum.start == Cst(0)) {
          Pow(Cst(2), bigSum.stop + 1) - 1
        } else {
          //CONSTANT
          intoProduct(bigSum).getOrElse(bigSum)
        }
    }
  }


  //if the iteration variable never appears in the body, then it's just a straightforward product
  private def intoProduct(bigSum: BigSum):Option[ArithExpr] = {
    if(!bigSum.body.contains(bigSum.iterationVariable)) {
      val stop = bigSum.stop
      val start = bigSum.start
      val coeff = stop - start + 1
      Some(coeff  * bigSum.body)
    } else {
      None
    }
  }

  private def ifElimination(bigSum: BigSum):ArithExpr = {
    val ifBody = bigSum.body.asInstanceOf[IfThenElse]
    //Does the bottom of the range match the if condition?
    ifBody.test match {
      case Predicate(lhs, rhs, Predicate.Operator.==)
        if lhs == bigSum.iterationVariable && rhs == bigSum.start ||
           lhs == bigSum.start && rhs == bigSum.iterationVariable =>
        //Split up the sum!

        //We need to guard the lifted-out piece by another condition, that is that the bounds
        //of the sum are actually non-overlapping.
        val liftedOutPredicate = SimplifyIfThenElse(Predicate(bigSum.stop, bigSum.start, Operator.>=), ifBody.t, 0)
        liftedOutPredicate + SimplifyBigSum(BigSum(bigSum.iterationVariable, bigSum.start + 1, bigSum.stop, ifBody.e))

      case Predicate(lhs, rhs, Predicate.Operator.<)
        if lhs == bigSum.iterationVariable =>

        val liftedOut = SimplifyBigSum(BigSum(bigSum.iterationVariable, bigSum.start, rhs -1, ifBody.t))
        val remainingBit = SimplifyBigSum(BigSum(bigSum.iterationVariable, rhs, bigSum.stop, ifBody.e))
        liftedOut + remainingBit

      case Predicate(lhs, rhs, Predicate.Operator.>)
        if lhs == bigSum.iterationVariable =>

        val liftedOut = SimplifyBigSum(BigSum(bigSum.iterationVariable, bigSum.start, rhs -1, ifBody.t))
        val remainingBit = SimplifyBigSum(BigSum(bigSum.iterationVariable, rhs, bigSum.stop, ifBody.e))
        liftedOut + remainingBit

      case Predicate(_, _, other) =>
        println(s"WARNING: Can't simplify BigSum with operator $other")
        bigSum
    }
  }
}
