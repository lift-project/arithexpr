package lift.arithmetic.simplifier

import lift.arithmetic._

object SimplifyBigSum {
  def apply(bigSum: BigSum):ArithExpr = {
    splitTerms(bigSum)
  }

  private def splitTerms(bigSum: BigSum):ArithExpr = {
    bigSum.body match {
      case Sum(terms) =>
        //Split each term in it's own sum, then simplify it
        Sum(terms.map(term =>
          SimplifyBigSum(bigSum.copy(body = term)
        )))

      case _ => liftOutConstantFactors(bigSum)
    }
  }

  private def makeProd(exprs:List[ArithExpr]):ArithExpr = exprs match {
    case List(justThis) => justThis
    case other => Prod(other)
  }

  private def liftOutConstantFactors(bigSum: BigSum):ArithExpr = {
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
    if(bigSum.body == bigSum.iterationVariable && bigSum.start == Cst(0)) {
      (bigSum.stop*(bigSum.stop + 1))/2
    } else {
      intoProduct(bigSum)
    }
  }

  /*
  //If the sum does not being from zero, then we can split it in two zero-based sums
  private def splitSums(bigSum: BigSum):ArithExpr = {
    //TODO:Sound in principle, but stackoveflows!
      if(bigSum.range.min != Cst(0)) {
        val upperSum = BigSum(bigSum.iterationVariable, ContinuousRange(0, bigSum.range.max), bigSum.body)
        val lowerSum = BigSum(bigSum.iterationVariable, ContinuousRange(0, bigSum.range.min), bigSum.body)
        upperSum - lowerSum
      } else bigSum
  }*/

  //If the iteration variable never appears in the body, then it's just a straightforward product
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
