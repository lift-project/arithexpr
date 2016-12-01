package lift
package arithmetic

import sun.reflect.generics.reflectiveObjects.NotImplementedException

object Sign extends Enumeration {
  type Sign = Value
  val Positive, Negative, Unknown = Value

  def reverse(s: Sign): Sign = {
    s match {
      case Sign.Positive => Sign.Negative
      case Sign.Negative => Sign.Positive
      case Sign.Unknown => Sign.Unknown
    }
  }

  private[arithmetic] def apply(ae: ArithExpr): Value = {
    ae match {
      case CeilingFunction(e) => e.sign
      case FloorFunction(e) => e.sign
      case AbsFunction(_) => Sign.Positive
      case Cst(c) if c >= 0 => Sign.Positive
      case Cst(c) if c < 0 => Sign.Negative
      case Prod(factors) => signProd(factors)
      case Sum(terms) => signSum(terms)
      case IntDiv(numer, denom) => signIntDiv(numer, denom)
      case ite: IfThenElse => signIfThenElse(ite)
      case Log(b, x) => signLog(b, x)
      case Mod(dividend, _) => dividend.sign
      case Pow(b, e) => b.sign
      case Var(_, range) => signVar(range)
      case ? => Sign.Unknown
      case _: ArithExprFunction => Sign.Unknown
    }
  }

  private def signProd(factors: List[ArithExpr]): Sign.Value = {
    factors.foldLeft(Sign.Positive)((s: Sign.Value, factor) =>
      s match {
        case Sign.Positive => factor.sign
        case Sign.Negative => Sign.reverse(factor.sign)
        case Sign.Unknown => return Sign.Unknown
      })
  }

  private def signSum(terms: List[ArithExpr]): Sign.Value = {
    val unknownSignTerms = terms.filter(_.sign == Sign.Unknown)
    if (unknownSignTerms.nonEmpty)
      Sign.Unknown
    else {
      val posTerms = terms.filter(_.sign == Sign.Positive)
      val negTerms = terms.filter(_.sign == Sign.Negative)
      if (posTerms.isEmpty) {
        assert(negTerms.nonEmpty)
        Sign.Negative
      }
      else if (negTerms.isEmpty) {
        assert(posTerms.nonEmpty)
        Sign.Positive
      }
      else {
        val absSumNegTerms = abs(negTerms.fold(Cst(0))(_ + _))
        val sumPosTerms = posTerms.fold(Cst(0))(_ + _)
        val lhsSmaller = ArithExpr.isSmaller(absSumNegTerms, sumPosTerms)
        val rhsSmaller = ArithExpr.isSmaller(sumPosTerms, absSumNegTerms)
        if (lhsSmaller.isEmpty || rhsSmaller.isEmpty)
          Sign.Unknown
        else if (lhsSmaller.get && !rhsSmaller.get)
          Sign.Positive
        else if (!lhsSmaller.get && rhsSmaller.get)
          Sign.Negative
        else Sign.Unknown
      }
    }
  }

  private def signIntDiv(numer: ArithExpr, denom: ArithExpr): Sign.Value = {
    (numer.sign, denom.sign) match {
      case (Sign.Positive, Sign.Positive) | (Sign.Negative, Sign.Negative) => Sign.Positive
      case (Sign.Positive, Sign.Negative) | (Sign.Negative, Sign.Positive) => Sign.Negative
      case _ => Sign.Unknown
    }
  }

  private def signIfThenElse(ite: IfThenElse): Sign.Value = {
    if (ite.t.sign == ite.e.sign)
      ite.t.sign
    else
      Sign.Unknown
  }

  private def signLog(b: ArithExpr, x: ArithExpr): Sign.Value = {
    x.sign match {
      case Sign.Positive =>
        (x - 1).sign match {
          case Sign.Positive => Sign.Positive
          case Sign.Negative => Sign.Negative
          case Sign.Unknown => Sign.Unknown
        }
      case Sign.Negative => throw new NotImplementedException
      case Sign.Unknown => throw new NotImplementedException
    }
  }

  private def signVar(range: Range): Sign.Value = {
    if (range.min.sign == Sign.Positive)
      Sign.Positive
    else if (range.max.sign == Sign.Negative)
      Sign.Negative
    else
      Sign.Unknown
  }
}
