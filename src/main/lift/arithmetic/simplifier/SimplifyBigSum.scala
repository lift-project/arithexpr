package lift.arithmetic.simplifier

import lift.arithmetic._
import lift.util.{ListMatch, Matching}

object SimplifyBigSum {

  private def done(bigSum: BigSum):ArithExpr = new BigSum(bigSum.variable, bigSum.body) with SimplifiedExpr

  def apply(bigSum:BigSum):ArithExpr with SimplifiedExpr = {
    bigSum.body match {
      //Constant case
      case anything if !ArithExpr.freeVariables(anything).contains(bigSum.variable) =>
        ((bigSum.upTo + 1) - bigSum.from)*bigSum.body
      //Split the sum along +
      case Sum(terms) if terms.nonEmpty =>
        bigSumofTerms(bigSum, terms)

      //Take out constant products

      case Prod(factors) if factors.nonEmpty => bigSumOfProduct(bigSum, factors)
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

  private def bigSumofTerms(bigSum: BigSum, terms:List[ArithExpr with SimplifiedExpr]):ArithExpr with SimplifiedExpr = {
    Sum(terms).asProd match {
      case Some(Prod(xs)) =>
        bigSumOfProduct(bigSum, xs)
      case None =>
        val products = terms.map({
          case x:Prod => x.factors
          case other => List(other, Cst(1))
        })

        val matchFx = Matching.just[ArithExpr with SimplifiedExpr] {
          case fCall: ArithExprFunctionCall if fCall.exposedArgs == Seq(bigSum.variable) => true
          case _ => false
        }

        val matchFxPlusOne = Matching.just[ArithExpr with SimplifiedExpr] {
          case fCall: ArithExprFunctionCall if fCall.exposedArgs == Seq(bigSum.variable + 1) => true
          case _ => false
        }

        val matchConstant = Matching.just[ArithExpr with SimplifiedExpr] {
          exp => !ArithExpr.freeVariables(exp).contains(bigSum.variable)
        }

        val matchMinusOne = Matching.just[ArithExpr with SimplifiedExpr](_ == Cst(-1))

        val matchFirstPart = ListMatch(matchFxPlusOne, matchConstant)
        val matchSecondPart =  ListMatch(matchFx, matchMinusOne, matchConstant)

        val (found, lefovers) = Matching.matchMany(
          products, Iterable(matchFirstPart, matchSecondPart)
        )

        val simplified = if(lefovers.isEmpty) {
          val firstMap = found(matchFirstPart)
          val secondMap = found(matchSecondPart)

          def elideZero(ae:ArithExpr with SimplifiedExpr):Option[ArithExpr with SimplifiedExpr] = {
            ae match {
              case Cst(1) => None
              case _ => Some(ae)
            }
          }

          if(firstMap.get(matchConstant).flatMap(elideZero) == secondMap.get(matchConstant).flatMap(elideZero)) {
            val constantFactor = firstMap(matchConstant)

            val functionBase = secondMap(matchFx).asInstanceOf[ArithExprFunctionCall]

            val f1 = functionBase.substituteExposedArgs(Map(bigSum.variable -> (bigSum.upTo + 1)))
            val f2 = functionBase.substituteExposedArgs(Map(bigSum.variable -> Cst(0)))

            val newExpr = constantFactor * (f1 - f2)
            Some(newExpr)
          } else None
        } else None

        simplified match {
          case None =>
            val sumTerms = terms.map(term => bigSum.modify(newBody = term))
            sumTerms.reduceOption(_ + _).getOrElse(Cst(0))
          case Some(x) => x
        }
    }
  }

  private def bigSumOfProduct(bigSum: BigSum, factors:Seq[ArithExpr]):ArithExpr with SimplifiedExpr = {
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
  }
}
