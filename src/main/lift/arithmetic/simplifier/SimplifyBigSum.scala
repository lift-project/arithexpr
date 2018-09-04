package lift.arithmetic.simplifier

import lift.arithmetic.Predicate.Operator
import lift.arithmetic._

object SimplifyBigSum {
  def apply(bigSum: BigSum):ArithExpr = {
    val result:ArithExpr =
    //If bounds are known, unroll
    if(bigSum.start.isInstanceOf[Cst] && bigSum.stop.isInstanceOf[Cst]) {
      unrollSum(bigSum)
    } else bigSum.stop match {
        //If we are at 0, then it's fine
        case Sum(terms) if terms.count(_.isInstanceOf[IfThenElse]) == 1 =>
          val (ifThenElse, others) = terms.partition(_.isInstanceOf[IfThenElse])
          val newIfThenElse = pushTermsInIf(ifThenElse.head.asInstanceOf[IfThenElse], others)
          val split = splitUpperIfThenElse(bigSum, newIfThenElse)
          split
        case upperIte:IfThenElse =>
          val thenSum = SimplifyBigSum(bigSum.copy(stop = upperIte.t))
          val elseSum = SimplifyBigSum(bigSum.copy(stop = upperIte.e))

          IfThenElse(upperIte.test, thenSum, elseSum)

        case _ => if (ArithExpr.isSmaller(bigSum.stop.max - bigSum.stop.min, 0).contains(true)) {
          Cst(0)
        }
        else
          splitTerms(bigSum)
    }
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
      val if_statement = IfThenElse(
        Predicate(stop, start, Predicate.Operator.>=), coeff * bigSum.body, 0)

      Some(if_statement)
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

  private def unrollSum(sum:BigSum):ArithExpr = {
    val startInt = sum.start.evalInt
    val endInt = sum.stop.evalInt

    //"to" is scala for inclusive ranges
    val terms = for (i <- startInt to endInt)
      yield ArithExpr.substitute(sum.body, Map[ArithExpr,ArithExpr](sum.iterationVariable -> Cst(i)))
    terms.foldLeft[ArithExpr](Cst(0))(_ + _)
  }


  private def pushTermsInIf(ifThenElse: IfThenElse, others:Iterable[ArithExpr]):IfThenElse = {
    val newTerm = others.foldLeft[ArithExpr](0)(_ + _)
    IfThenElse(ifThenElse.test, ifThenElse.t + newTerm, ifThenElse.e + newTerm)
  }

  private def splitUpperIfThenElse(bigSum: BigSum, upperIte:IfThenElse) = {
    val thenSum = SimplifyBigSum(bigSum.copy(stop = upperIte.t))
    val elseSum = SimplifyBigSum(bigSum.copy(stop = upperIte.e))

    IfThenElse(upperIte.test, thenSum, elseSum)
  }

  //Try to get the IfThenElse in a state where the conditional is always of the form
  //if x == something, that is take x + 2 = 3 => x = 1
  private def regularise(ifThenElse: IfThenElse, variableOfInterest:Var):IfThenElse = {
    ifThenElse match {
      case IfThenElse(Predicate(lhs, rhs, op), t, e) =>
        lhs match {
          case Sum(terms) if terms.contains(variableOfInterest) =>
            val(myVar, others) = terms.partition(_.contains(variableOfInterest))
            val newLhs = myVar.foldLeft[ArithExpr](0)(_ + _)
            val newRhs = rhs - others.foldLeft[ArithExpr](0)(_ + _)
            IfThenElse(Predicate(newLhs, newRhs, op), t, e)
          case _ => ifThenElse
        }
      case _ => ifThenElse
    }
  }
}
