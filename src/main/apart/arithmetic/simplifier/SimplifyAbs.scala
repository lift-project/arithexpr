package apart
package arithmetic
package simplifier

object SimplifyAbs {

  def apply(ae: ArithExpr): ArithExpr = {
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
