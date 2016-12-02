package lift
package arithmetic
package simplifier

object SimplifyIfThenElse {

  def simplify(test: Predicate, t : ArithExpr, e : ArithExpr): Option[ArithExpr] = {
    // If both branches are the same, it doesn't matter which one we take
    if (e == t) Some(t)
    // otherwise try to evaluate the predicate
    else {
      ExprSimplifier(test.lhs - test.rhs) match {
        case Cst(v) =>
          val op = test.op
          import lift.arithmetic.Predicate.Operator
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
