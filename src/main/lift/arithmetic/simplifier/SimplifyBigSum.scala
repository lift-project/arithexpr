package lift.arithmetic.simplifier

import lift.arithmetic._

object SimplifyBigSum {
  def apply(bigSum: BigSum):ArithExpr = {
    if(ArithExpr.isSmaller(bigSum.stop.max, bigSum.start.min).contains(true)) {
      Cst(0)
    } else
      splitTerms(bigSum)
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

        val result = makeProd(liftedOut) * SimplifyBigSum(bigSum.copy(body = newBody))
        result
      case _ => finalPhase(bigSum)
    }
  }

  private def finalPhase(bigSum: BigSum):ArithExpr = {
    bigSum.body match {
      case _: IfThenElse =>
        ifElimination(bigSum)
      case _ => if (bigSum.body == bigSum.iterationVariable && bigSum.start == Cst(0)) {
        (bigSum.stop * (bigSum.stop + 1)) / 2
      } else {
        intoProduct(bigSum)
      }
    }
  }


  //if the iteration variable never appears in the body, then it's just a straightforward product
  private def intoProduct(bigSum: BigSum) = {
    if(!bigSum.body.contains(bigSum.iterationVariable)) {
      val stop = bigSum.stop
      val start = bigSum.start
      val coeff = stop - start + 1
      coeff  * bigSum.body
    } else {
      bigSum
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
        ifBody.t + SimplifyBigSum(BigSum(bigSum.iterationVariable, bigSum.start + 1, bigSum.stop, ifBody.e))
      case _ => bigSum
    }
  }


  def main(args:Array[String]) = {
    val v = Var("x")
    val bigSum = SimplifyBigSum(BigSum(v, 0 , 10, v))

    println(bigSum)
    println(bigSum.evalDouble)

    val bigSum2 = SimplifyBigSum(BigSum(v, 5, 10, 1))

    println(bigSum2)
    println(bigSum2.evalDouble)
  }
}
