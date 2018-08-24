package lift
package arithmetic
package simplifier

/**
 * Product simplifier
 */
object SimplifyProd {

  /**
   * Add a factor to a an existing product.
   * @param factor The factor to add.
   * @param prod An existing Prod object.
   * @return A re-written expression if the factor can be optimized with another from the list, a Prod otherwise.
   */
  def addFactor(factor: ArithExpr, prod: Prod): ArithExpr = {
    prod.factors.foreach(x => {
      val newfac = combineFactors(factor, x)
      if (newfac.isDefined) return prod.withoutFactor(x) * newfac.get
    })

    new Prod((factor :: prod.factors).sortWith(ArithExpr.sort)) with SimplifiedExpr
  }

  def isPowerVar(a:ArithExpr): Boolean = {
    def unsimplifiable(e:ArithExpr) = e.isInstanceOf[Var] || e.isInstanceOf[ArithExprFunction]
    a match {
      case Pow(_, e) => unsimplifiable(e)
      case _  => false
    }
  }

  /**
   * Try to combine a pair of factors.
   * @param lhs The first factor.
   * @param rhs The second factor.
   * @return An option containing an expression if the factors can be combined, None otherwise
   */
  def combineFactors(lhs: ArithExpr, rhs: ArithExpr): Option[ArithExpr] = {
    if (isPowerVar(lhs) || isPowerVar(rhs)) {
      None
    } else {
      (lhs, rhs) match {
        case (Cst(x), Cst(y)) => Some(Cst(x * y))

        case (x, y) if x == y => Some(x pow 2)

        case (Pow(b1, e1), Pow(b2, e2)) if b1 == b2 =>
          Some(b1 pow (e1 + e2))
        // Not efficient: two calls to `simplify`
        case (Pow(b1, e1), Pow(b2, e2)) if e1 == e2 && simplify(b1, b2).isDefined => Some((b1 * b2) pow e1)
        case (base, Pow(b, e)) if base == Cst(1) => Some(base /^ b * (b pow (e + 1)))
        case (Pow(b, e), base) if base == Cst(1) => Some(base /^ b * (b pow (e + 1)))
        case (base, Pow(b, e)) if ArithExpr.gcd(base, b) == b => Some(base /^ b * (b pow (e + 1)))
        case (Pow(b, e), base) if ArithExpr.gcd(base, b) == b => Some(base /^ b * (b pow (e + 1)))
        case (base, Pow(b, e)) if ArithExpr.gcd(base, b) != Cst(1) && e == Cst(-1) =>
          val gcd = ArithExpr.gcd(base, b)
          Some(base /^ gcd * ((b /^ gcd) pow e))
        case (Pow(b, e), base) if ArithExpr.gcd(base, b) != Cst(1) && e == Cst(-1) =>
          val gcd = ArithExpr.gcd(base, b)
          Some(base /^ gcd * ((b /^ gcd) pow e))
        case (x, y) => None
      }
    }
  }

    /**
      * Promote the product to another operation.
      *
      * @param lhs The left-hand side.
      * @param rhs The right-hand side.
      * @return An option containing a different operation if the product can be re-written, None otherwise
      */
    def simplify(lhs: ArithExpr, rhs: ArithExpr): Option[ArithExpr] = (lhs, rhs) match {

      case (lift.arithmetic.?, _) | (_, lift.arithmetic.?) => Some(lift.arithmetic.?)

      case (PosInf, NegInf) | (NegInf, PosInf) => Some(NegInf)
      case (PosInf, PosInf) | (NegInf, NegInf) => Some(PosInf)
      case (PosInf, y) => y.sign match {
        case Sign.Unknown => Some(?)
        case Sign.Positive => Some(PosInf)
        case Sign.Negative => Some(NegInf)
      }
      case (x, PosInf) => x.sign match {
        case Sign.Unknown => Some(?)
        case Sign.Positive => Some(PosInf)
        case Sign.Negative => Some(NegInf)
      }
      case (NegInf, y) => y.sign match {
        case Sign.Unknown => Some(?)
        case Sign.Positive => Some(NegInf)
        case Sign.Negative => Some(PosInf)
      }
      case (x, NegInf) => x.sign match {
        case Sign.Unknown => Some(?)
        case Sign.Positive => Some(NegInf)
        case Sign.Negative => Some(PosInf)
      }


      // Factor simplification
      case (x, y) if !x.simplified => Some(ExprSimplifier(x) * y)
      case (x, y) if !y.simplified => Some(x * ExprSimplifier(y))

      // Constant product
      case (Cst(x), Cst(y)) => Some(Cst(x * y))

      // Multiplication by zero
      case (Cst(0), _) | (_, Cst(0)) => Some(Cst(0))

      // TODO enable this when min and max are tested
      // The the evaluation yields 0, return 0
      //case (x, y) if x.max == 0 => Some(Cst(0))
      //case (x, y) if y.max == 0 => Some(Cst(0))

      // Multiplication by one
      case (Cst(1), _) => Some(rhs)
      case (_, Cst(1)) => Some(lhs)

      // Distribute sums
      case (x, s: Sum) => Some(s.terms.map(_ * x).reduce(_ + _))
      case (s: Sum, x) => Some(s.terms.map(_ * x).reduce(_ + _))

      // Combine products
      case (p1: Prod, p2: Prod) if p1.factors.length >= p2.factors.length => Some(addFactor(p2.factors.head, p1) * p2.withoutFactor(p2.factors.head))
      case (p1: Prod, p2: Prod) => Some(p2 * p1)
      case (p: Prod, x) => Some(addFactor(x, p))
      case (x, p: Prod) => Some(addFactor(x, p))

      case (v: Var, y) if v.range.min == v.range.max && v.range.min != ? => Some(v.range.min * y)
      case (x, v: Var) if v.range.min == v.range.max && v.range.min != ? => Some(x * v.range.min)

      // Actual product
      case (x, y) => None
    }
  /**
   * Try to promote the product into another expression, then try to combine factors. If all fails the expression is simplified.
   * @param lhs The left-hand side.
   * @param rhs The right-hand side.
   * @return A promoted expression or a simplified Prod object.
   */
  def apply(lhs: ArithExpr, rhs: ArithExpr): ArithExpr = {
    //println("Simplifying product")
    val simplificationResult = if (PerformSimplification()) simplify(lhs, rhs) else None
    simplificationResult match {
      case Some(toReturn) => toReturn
      case None =>
        val combineResult = if (PerformSimplification()) combineFactors(lhs,rhs) else None
        combineResult match {
          case Some(toReturn) => toReturn
          case None =>
            val result = new Prod(List(lhs, rhs).sortWith(ArithExpr.sort)) with SimplifiedExpr
            result
        }
    }
  }

}
