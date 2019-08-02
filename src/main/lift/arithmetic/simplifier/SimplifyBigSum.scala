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

          val SumTermSimplificationResult(processedTerms, toTakeOut) = simplifySumTerms(bigSum.variable, bigSum.upTo, terms)

          val sumTerms = processedTerms.map(term => bigSum.modify(newBody = term))
          (sumTerms ++ toTakeOut).reduceOption(_ + _).getOrElse(Cst(0))
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

  private case class SumTermSimplificationResult(keepInTheSum:Seq[ArithExpr with SimplifiedExpr], takeOutOfSum:Seq[ArithExpr with SimplifiedExpr])

  private def simplifySumTerms(iterVar:Var,
                               sumUpperBound:ArithExpr,
                               exprs: List[ArithExpr with SimplifiedExpr]):SumTermSimplificationResult = {
    val (functions, notFunctions) = exprs.partition(_.isInstanceOf[ArithExprFunctionCall])
    val (relevantFunctions, irrelevantFunctions) = functions
      .map(_.asInstanceOf[ArithExprFunctionCall])
      .map(functionWithRespectToVar(_, iterVar))
      .partition(_.isDefined)

    val SumTermSimplificationResult(keepInSum, takeOutOfSum) = findPlusOnePairs(sumUpperBound, relevantFunctions.map(_.get), Seq(), Seq())

    SumTermSimplificationResult(
      keepInSum ++ notFunctions ++ irrelevantFunctions.map(_.get.originalFunction),
      takeOutOfSum
    )
  }

  private def findPlusOnePairs(sumUpperBound:ArithExpr,
                               funs:List[FunctionWithRespectToSingleVar],
                               seen:Seq[FunctionWithRespectToSingleVar],
                               takenOut:Seq[ArithExpr with SimplifiedExpr]):
  SumTermSimplificationResult = {
    funs match {
      case Nil => SumTermSimplificationResult(seen.map(_.originalFunction), takenOut)
      case fun::rest =>
        val sibling = if(fun.arg == fun.v + 1) {
          seen.find(x => x.arg == fun.v)
        } else if(fun.arg == fun.v) {
          seen.find(x => x.arg == 0 - fun.v)
        } else None

        sibling match {
          case None => findPlusOnePairs(sumUpperBound, rest, seen :+ fun, takenOut)
          case Some(matching) =>
            val newEntries = Seq(fun.replaceArg(sumUpperBound), 0 - fun.replaceArg(0))
            findPlusOnePairs(sumUpperBound,  rest, seen.filter(_ != matching), takenOut ++ newEntries)
        }
    }
  }

  private def functionWithRespectToVar(fun:ArithExprFunctionCall, v:Var):Option[FunctionWithRespectToSingleVar] = {
    fun.exposedArgs.filter(ArithExpr.freeVariables(_).contains(v)).toList match {
      case x::Nil => Some(FunctionWithRespectToSingleVar(fun, v, x))
      case _ => None
    }
  }

  private case class FunctionWithRespectToSingleVar(originalFunction:ArithExprFunctionCall, v:Var, val arg:ArithExpr) {
    def replaceArg(ae:SimplifiedExpr):ArithExprFunctionCall = {
      originalFunction.substituteExposedArgs(Map(arg -> ae))
    }
  }


}
