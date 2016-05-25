package apart
package arithmetic
package simplifier


object SimplifyDivision {

  def apply(numer: ArithExpr, denom: ArithExpr): ArithExpr = {
    (numer, denom) match {
      case (x, Cst(1)) => x
      case (Cst(x), Cst(y)) if x % y == 0 => Cst(x / y)
      case (x, y) if x == y => Cst(1)
      case (x, y) if x == (y * Cst(-1)) => Cst(-1)
      case (x, y) => x * (y pow -1)
    }
  }

}
