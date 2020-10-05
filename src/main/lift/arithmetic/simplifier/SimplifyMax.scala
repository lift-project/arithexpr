package lift.arithmetic.simplifier

import lift.arithmetic.{ArithExpr, Max, PerformSimplification, SimplifiedExpr}

object SimplifyMax {
  def simplify(a: ArithExpr with SimplifiedExpr, b: ArithExpr with SimplifiedExpr):
  Option[ArithExpr with SimplifiedExpr] =
    (a, b) match {
      case (a, b) if a == b => Some(a)
      case (a, b) if ArithExpr.isSmaller(a, b).contains(true) => Some(b)
      case (a, b) if ArithExpr.isSmaller(b, a).contains(true) => Some(a)
      case _ => None
    }

  def apply(a: ArithExpr with SimplifiedExpr, b: ArithExpr with SimplifiedExpr): ArithExpr with SimplifiedExpr = {
    (if (PerformSimplification()) simplify(a, b)
    else None) match {
        case Some(simplifiedExpr) => simplifiedExpr
        case None => new Max(a, b) with SimplifiedExpr
      }
  }
}
