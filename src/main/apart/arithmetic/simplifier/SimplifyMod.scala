package apart
package arithmetic
package simplifier

object SimplifyMod {

  def simplify(dividend: ArithExpr, divisor: ArithExpr): Option[ArithExpr] = (dividend, divisor) match {

    // Simplify operands
    case (x, y) if !x.simplified => Some(ExprSimplifier(x) % y)
    case (x, y) if !y.simplified => Some(x % ExprSimplifier(y))

    // Modulo 1
    case (_, Cst(1)) => Some(Cst(0))

    // 0 or 1 modulo anything
    case (Cst(x), _) if x == 0 || x == 1 => Some(dividend)

    // Constant modulo
    case (Cst(x), Cst(y)) => Some(Cst(x % y))

    // If there exists a common denominator, simplify
    case (x, y) if ArithExpr.gcd(x,y) != Cst(1) => {
      val fac = ArithExpr.gcd(x,y)
      Some((x/^fac) % (y/^fac))
    }

    case (x, y) if ArithExpr.multipleOf(x, y) => Some(Cst(0))
    case (m: Mod, divisor) if m.divisor == divisor => Some(m)
    case (x, y) if ArithExpr.isSmaller(x, y) => Some(x)
    case (Sum(terms), d) =>
      // (A + B) mod C = (A mod C + B mod C) mod C
      // try to distribute the mod. If this results in a simpler sum (by the number of terms) then keep it
      terms.map(_ % d).reduce(_ + _) match {
        case Sum(newTerms) =>
          // If the new sum is simpler, re-factorize the mod with the new expression
          if (newTerms.length < terms.length) {
            Some(newTerms.map({
              case Mod(_dividend, _divisor) if _divisor == d => _dividend
              case t => t
            }).reduce(_ + _) % d)
          } else None
        case x => Some(x % d)
      }
    case _ => None
  }

  def apply(dividend: ArithExpr, divisor: ArithExpr): ArithExpr = simplify(dividend, divisor) match {
    case Some(toReturn) => toReturn
    case None => new Mod(dividend, divisor) with SimplifiedExpr
  }
}
