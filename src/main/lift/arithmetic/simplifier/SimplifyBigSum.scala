package lift.arithmetic.simplifier

import lift.arithmetic._

object SimplifyBigSum {

  private def done(bigSum: BigSum):ArithExpr = new BigSum(bigSum.variable, bigSum.body) with SimplifiedExpr

  def apply(bigSum:BigSum):ArithExpr with SimplifiedExpr = {
      bigSum.body match {
          //Constant case
        case anything if !ArithExpr.freeVariables(anything).contains(bigSum.variable) =>
          ((bigSum.upTo + 1) - bigSum.from)*bigSum.body
          //Split the sum along +
        case Sum(terms) if terms.nonEmpty =>


          val sumTerms = terms.map(term => bigSum.modify(newBody = term))
          (sumTerms).reduceOption(_ + _).getOrElse(Cst(0))
          //Take out constant products
        case Prod(factors) if factors.nonEmpty =>
          val (keepIn, takeOut) = factors.partition(factor => ArithExpr.freeVariables(factor).contains(bigSum.variable))
          takeOut match {
            case Nil => done(bigSum)
            case _ =>
              val takeOutExpr = takeOut.reduce(_ * _)
              val newBody = keepIn match {
                case Nil => Cst(1)
                case _ => keepIn.reduce(_ * _)
              }
              val newSum = bigSum.modify(newBody = newBody)
              takeOutExpr*newSum
          }
          //Euler's formula
        case v:InclusiveIndexVar if v == bigSum.variable =>
          val N = bigSum.upTo
          N * (N + 1) / 2


          //If we find a stepwise function over the sum variable, and the sum starts at 0...
        case SteppedCase(v, cases) if v == bigSum.variable && bigSum.from == Cst(0) =>
          //For each case, we can generate a term
          val terms = cases.zipWithIndex.map{
            case (caseExpr, index) =>
              val subbed = ArithExpr.substitute(caseExpr, Map(v -> Cst(index)))
              ArithExpr.ifThenElse(BoolExpr.arithPredicate(bigSum.upTo, Cst(index), BoolExpr.ArithPredicate.Operator.>=), subbed, Cst(0))
              .asInstanceOf[ArithExpr]
          }

          terms.reduceOption(_ + _).getOrElse(Cst(0))
        case _ => done(bigSum)
      }
  }
}
