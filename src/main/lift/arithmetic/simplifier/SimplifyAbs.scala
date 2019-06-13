package lift
package arithmetic
package simplifier

object SimplifyAbs {

  def apply(ae: ArithExpr with SimplifiedExpr): ArithExpr with SimplifiedExpr = {
    if (PerformSimplification())
      ae.sign match {
        case Sign.Positive => ae
        case Sign.Negative => -1 * ae
        case Sign.Unknown => new AbsFunction(ae) with SimplifiedExpr
      }
    else
      new AbsFunction(ae) with SimplifiedExpr
  }

}
