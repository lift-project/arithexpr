package lift.arithmetic.simplifier

import lift.arithmetic._

object SimplifyBigSum {
  def apply(bigSum: BigSum):ArithExpr = {
    intoProduct(bigSum)
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
      val coeff = stop - start
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
