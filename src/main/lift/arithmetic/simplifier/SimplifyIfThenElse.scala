package lift
package arithmetic
package simplifier

object SimplifyIfThenElse {

  def simplify(test: BoolExpr, t : ArithExpr with SimplifiedExpr, e : ArithExpr with SimplifiedExpr): Option[ArithExpr with SimplifiedExpr] = {
    test match {
      case BoolExpr.True => Some(t)
      case BoolExpr.False => Some(e)
      case test: BoolExpr.ArithPredicate =>
        // If both branches are the same, it doesn't matter which one we take
        if (e == t) Some(t)
        // otherwise try to evaluate the predicate
        else {
          ExprSimplifier(test.lhs - test.rhs) match {
            case Cst(v) =>
              val op = test.op
              import BoolExpr.ArithPredicate.Operator
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
  }

  def apply(test: BoolExpr, t : ArithExpr with SimplifiedExpr, e : ArithExpr with SimplifiedExpr): ArithExpr with SimplifiedExpr = {
    val simplificationResult = if (PerformSimplification()) simplify(test, t, e) else None
    simplificationResult match {
      case Some(toReturn) => toReturn
      case None =>
        new IfThenElse(test.simplifyInnerArithExpr, ExprSimplifier(t), ExprSimplifier(e)) with SimplifiedExpr
    }
  }
}
