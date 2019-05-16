package lift
package arithmetic
package simplifier

import scala.language.postfixOps

object SimplifyPow {

  /**
   * Try to promote a Pow to a different expression.
   * @param base The base.
   * @param exp The exponent.
   * @return An option containing a promoted expression if the expression can be re-written, None otherwise.
   */
  def simplify(base: ArithExpr, exp: ArithExpr): Option[ArithExpr] = (base, exp) match {

    // Power of zero
    case (_, Cst(0)) => Some(Cst(1))

    // Power of one
    case (b, Cst(1)) => Some(b)

    // Negative base with the power of minus one
      // (-b)^-1 => -1 * b^-1
    case (Cst(b), Cst(-1)) if b < 0 => Some(SimplifyProd(List(Cst(-1), SimplifyPow(Cst(-b), Cst(-1)))))

    // 0 or 1 to any power
    case (Cst(x), _) if x == 0 || x == 1 => Some(base)

    case (Cst(b), Cst(e)) if e >= 0 => Some(Cst(Math.pow(b, e).toInt))

    // Constant positive exponent
    case (Cst(b), Cst(e)) if e > 1 => Some(Cst(scala.math.pow(b,e).toInt))

    // Constant negative exponents: pow(x,-y) = pow(pow(x,y), -1)  (closed form)
    case (Cst(b), Cst(e)) if e < -1 => Some(Cst(scala.math.pow(b, -e).toInt) pow Cst(-1))

    // Distribute product: x^(m+n) => x^m * x^n
    // This is not a closed form -- hence, this is now a "temporary view" for simplification
    // implemented in Prod.unapply()
//    case (b, Sum(terms)) => Some(terms.map(b pow).reduce(_*_))

    // Simplify Operands
    case (x, y) if !x.simplified => Some(ExprSimplifier(x) pow y)
    case (x, y) if !y.simplified => Some(x pow ExprSimplifier(y))

    // Power of power: (x^e1)^e2 => x^(e1*e2)
    case (Pow(b, e1), e2) if (e1 match {
      case Cst(1) => false
      case _ => true
    })  => Some(b pow (e1 * e2))

    // x^(a*log(x,b)*c) => b^(a*b)
    case (x, Prod(factors)) =>
      val log = factors.find{
        case Log(x1,_) if x1 == x => true
        case _ => false
      }
      if (log.nonEmpty) Some(log.get.asInstanceOf[Log].x pow SimplifyProd(Prod.removeFactors(factors, List(log.get))))
      else None

    // x^log(x,b) => b
    case (x1,Log(x2,b)) if x1 == x2 => Some(b)

    case (v: Var, e) if v.range.min == v.range.max && v.range.min != ? => Some(v.range.min pow e)
    case (x, v: Var) if v.range.min == v.range.max && v.range.min != ? => Some(x pow v.range.min)

    case _ => None
  }

  def apply(base: ArithExpr, exp: ArithExpr) = {
    val simplificationResult = if (PerformSimplification()) simplify(base, exp) else None
    simplificationResult match {
      case Some(toReturn) => toReturn
      case None => new Pow(base, exp) with SimplifiedExpr
    }
  }
}
