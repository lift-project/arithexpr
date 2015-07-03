package apart
package arithmetic
package simplifier

object SimplifyPow {

  /**
   * Try to promote a Pow to a different expression.
   * @param base The base.
   * @param exp The exponent.
   * @return An option containing a promoted expression if the expression can be re-written, None otherwise.
   */
  def simplify(base: ArithExpr, exp: ArithExpr): Option[ArithExpr] = (base, exp) match {

    // Power of zero
    case (base, Cst(0)) => Some(Cst(1))

    // Power of one
    case (base, Cst(1)) => Some(base)

    // 0 or 1 to any power
    case (Cst(x), _) if x == 0 || x == 1 => Some(base)

    // Distribute product: x^(m+n) => x^m * x^n
    case (base, Sum(terms)) => Some(terms.map(base pow _).reduce(_*_))

    // Power of a product: (x*y)^(n) => x^n * y^n
    case (Prod(terms), exp) => Some(terms.map(_ pow exp).reduce(_*_))

    // Constant positive exponent
    case (Cst(b), Cst(e)) if e > 1 => Some(Cst(scala.math.pow(b,e).toInt))

    // Constant negative exponents: pow(x,-y) = pow(pow(x,y), -1)
    case (Cst(b), Cst(e)) if e < -1 => Some(Cst(scala.math.pow(b, -e).toInt) pow Cst(-1))

    // Simplify Operands
    case (x, y) if !x.simplified => Some(ExprSimplifier(x) pow y)
    case (x, y) if !y.simplified => Some(x pow ExprSimplifier(y))

    // Power of power: (x^e1)^e2 => x^(e1*e2)
    case (Pow(b, e1), e2) => Some(b pow (e1 * e2))

    // x^(a*log(x,b)*c) => b^(a*b)
    case (x,p@Prod(factors)) =>
      val log = factors.find{
        case Log(x1,_) if x1 == x => true
        case _ => false
      }
      if (log.nonEmpty) Some(log.get.asInstanceOf[Log].x pow p.withoutFactors(List(log.get)))
      else None

    // x^log(x,b) => b
    case (x1,Log(x2,b)) if x1 == x2 => Some(b)

    case _ => None
  }

  def apply(base: ArithExpr, exp: ArithExpr) = simplify(base, exp) match {
    case Some(toReturn) => toReturn
    case None => new Pow(base, exp) with SimplifiedExpr
  }
}
