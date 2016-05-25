package apart
package arithmetic
package simplifier

object SimplifyAbs {

  def apply(ae: ArithExpr): ArithExpr = {
    ae.sign match {
      case Sign.Positive => ae
      case Sign.Negative => -1 * ae
      case Sign.Unknown => new Abs(ae) with SimplifiedExpr
    }
  }

}
