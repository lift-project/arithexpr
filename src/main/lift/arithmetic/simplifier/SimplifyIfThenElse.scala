package lift
package arithmetic
package simplifier

import lift.arithmetic.Predicate.Operator

object SimplifyIfThenElse {

  def simplify(test: Predicate, t : ArithExpr, e : ArithExpr): Option[ArithExpr] = {
    // If both branches are the same, it doesn't matter which one we take

    if (e == t) return Some(t)

    // otherwise try to evaluate the predicate
    val lmin = test.lhs.min
    val lmax = test.lhs.max
    val rmin = test.rhs.min
    val rmax = test.rhs.max

    if(test.op == Operator.<) test.lhs match {
      case v: Var if ArithExpr.isSmaller(v.range.max, test.rhs).getOrElse(false) => return Some(t)
      case Sum(Cst(c) :: (v:Var) :: Nil) if(
        c < 0 && ArithExpr.isSmaller(v.range.max, test.rhs).getOrElse(false)) => return Some(t)
      case _ =>
    }

    // >= => min of lhs needs to be always bigger or equals to the max of rhs
    if(test.op == Operator.>= && (ArithExpr.isSmaller(rmax, lmin).getOrElse(false) || rmax == lmin))
      return Some(t)

    if(test.op == Operator.<= && (ArithExpr.isSmaller(lmax, rmin).getOrElse(false) || rmin == lmax))
      return Some(t)

    if(test.op == Operator.> && ArithExpr.isSmaller(rmax, lmin).getOrElse(false))
      return Some(t)

    if(test.op == Operator.< && ArithExpr.isSmaller(lmax, rmin).getOrElse(false))
      return Some(t)

    else {
      val p = ExprSimplifier(test.lhs - test.rhs)
      p match {
        case Cst(v) =>
          val op = test.op
          // true predicate
          if ((v > 0 && (op == Operator.> || op == Operator.>=)) ||
            (v < 0 && (op == Operator.< || op == Operator.<=)) ||
            (v == 0 && (op == Operator.== || op == Operator.<= || op == Operator.>=)) ||
            (v != 0 && op == Operator.!=)) Some(t)
          else Some(e)
        case _ => None
      }
    }
  }

  def apply(test: Predicate, t : ArithExpr, e : ArithExpr): ArithExpr = {
    val simplificationResult = if (PerformSimplification()) simplify(test, t, e) else None
    simplificationResult match {
      case Some(toReturn) => toReturn
      case None => new IfThenElse(Predicate(ExprSimplifier(test.lhs), ExprSimplifier(test.rhs), test.op), ExprSimplifier(t), ExprSimplifier(e)) with SimplifiedExpr
    }
  }
}
