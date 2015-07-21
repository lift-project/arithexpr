package apart
package arithmetic
package simplifier

/**
 * Simplify binary addition.
 */
object SimplifySum {

  /**
   * Add a term to a an existing sum.
   * @param term The term to add.
   * @param sum An existing Sum object.
   * @return A re-written expression if the term can be optimized with another from the list, a Sum otherwise.
   */
  def addTerm(term: ArithExpr, sum: Sum): ArithExpr = {
    // Try to combine the new term to each existing terms in the sum, substibute if there is a match
    sum.terms.foreach(x => combineTerms(term,x) match {
      case Some(newterm) => return sum.withoutTerm(List(x)) + newterm
      case _ =>
    })
    // If we couldn't simplify the expression, create a simplified Sum object
    new Sum((term :: sum.terms).sortWith(ArithExpr.sort)) with SimplifiedExpr
  }

  /**
   * Try to combine a pair of terms.
   * @param lhs The first term.
   * @param rhs The second term.
   * @return An option containing an expression if the terms can be combined, None otherwise
   */
  def combineTerms(lhs: ArithExpr, rhs: ArithExpr): Option[ArithExpr] = (lhs, rhs) match {
    // Modulo Identity: a = a / b * b + a % b
    case (p: Prod, m@Mod(a, b)) if p == (a / b) * b => Some(a)
    case (m@Mod(a, b), p: Prod) if p == (a / b) * b => Some(a)

    // Merge constants
    case (Cst(x), Cst(y)) => Some(Cst(x+y))

    // Avoid duplicates in the term list
    case (x,y) if x == y => Some(2 * x)

    // Prune zeroed vars
    case (x, v:Var) if v.range.max == Cst(1) => Some(x)
    case (v:Var, x) if v.range.max == Cst(1) => Some(x)

    // Merge products if they only differ by a constant factor
    case (p1:Prod, p2:Prod) if p1.withoutFactor(p1.cstFactor) == p2.withoutFactor(p2.cstFactor) =>
      Some(p1.withoutFactor(p1.cstFactor) * (p1.cstFactor + p2.cstFactor))
    case (x, p:Prod) if p.withoutFactor(p.cstFactor) == x => Some(x * (p.cstFactor + 1))
    case (p:Prod, x) if p.withoutFactor(p.cstFactor) == x => Some(x * (p.cstFactor + 1))

    // Try to factorize terms and see if they simplify
    case (x, y) if ArithExpr.gcd(x, y) != Cst(1) =>
      val gcd = ArithExpr.gcd(x, y)
      val slhs = x /^ gcd
      val srhs = y /^ gcd
      slhs + srhs match {
        case s@Sum(sterms) if sterms.contains(slhs) && sterms.contains(srhs) => None
        case other => Some(other * gcd)
      }

    case x => None
  }

  /**
   * Promote the sum to another operation.
   * @param lhs The left-hand side.
   * @param rhs The right-hand side.
   * @return An option containing a different operation if the sum can be re-written, None otherwise
   */
  def simplify(lhs: ArithExpr, rhs: ArithExpr): Option[ArithExpr] = (lhs, rhs) match {
    // Not a sum
    case (Cst(x), Cst(y)) => Some(Cst(x+y))
    case (Cst(0), _) => Some(rhs)
    case (_, Cst(0)) => Some(lhs)

    // Simplify terms
    case (x, y) if !x.simplified => Some(ExprSimplifier(x) + y)
    case (x, y) if !y.simplified => Some(x + ExprSimplifier(y))

    // Prune zeroed vars
    case (x, v:Var) if v.range.max == Cst(1) => Some(x)
    case (v:Var, x) if v.range.max == Cst(1) => Some(x)

    // Combine Sums: if there are two sums, let the largest absorb the terms of the other one
    case (s1: Sum, s2: Sum) if s1.terms.length >= s2.terms.length => Some(addTerm(s2.terms.head, s1) + s2.withoutTerm(List(s2.terms.head)))
    case (s1: Sum, s2: Sum) => Some(s2 + s1)

    // Otherwise if one is a sum, add the new term
    case (s: Sum, x) => Some(addTerm(x, s))
    case (x, s: Sum) => Some(addTerm(x, s))

    case (x, y) => None
  }

  /**
   * Try to promote the sum into another expression, then try to combine terms. If all fails the expression is simplified.
   * @param lhs The left-hand side.
   * @param rhs The right-hand side.
   * @return A promoted expression or a simplified sum object.
   */
  def apply(lhs: ArithExpr, rhs: ArithExpr): ArithExpr = simplify(lhs, rhs) match {
    case Some(toReturn) => toReturn
    case None => combineTerms(rhs, lhs) match {
      case Some(toReturn) => toReturn
      case None => new Sum(List(lhs, rhs).sortWith(ArithExpr.sort)) with SimplifiedExpr
    }
  }
}
