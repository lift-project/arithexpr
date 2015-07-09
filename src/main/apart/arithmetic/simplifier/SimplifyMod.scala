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

    case (x, y) if ArithExpr.multipleOf(x, y) => Some(Cst(0))
    case (m: Mod, divisor) if m.divisor == divisor => Some(m)
    case (x, y) if ArithExpr.isSmaller(x, y) => Some(x)

    // If the divident is a product, try to find the divisor. Finding the GCD below should make this redundant, but the
    // GCD method does not return fractions, but the divisor could be one.
    case (Prod(factors), div) if factors.contains(div) => Some(Cst(0))

    // If there exists a common denominator, simplify
    case (x, y) if ArithExpr.gcd(x,y) == y => Some(Cst(0))

    // Isolate the terms which are multiple of the mod and eliminate
    case (s@Sum(terms), d) =>
      val (multiple, notmultiple) = terms.partition(x => ArithExpr.gcd(x, d) == d)
      if (multiple.nonEmpty) Some(s.withoutTerm(multiple) % d)
      else None

    case _ => None
  }

  def apply(dividend: ArithExpr, divisor: ArithExpr): ArithExpr = simplify(dividend, divisor) match {
    case Some(toReturn) => toReturn
    case None => new Mod(dividend, divisor) with SimplifiedExpr
  }
}
