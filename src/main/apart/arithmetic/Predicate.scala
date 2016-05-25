package apart
package arithmetic

import apart.arithmetic.simplifier.SimplifyIfThenElse

/**
  * Predicate object. Stores two arithmetic expressions and an operator
  */
case class Predicate(lhs: ArithExpr, rhs: ArithExpr, op: Predicate.Operator.Operator) {

  override lazy val toString: String = s"($lhs $op $rhs)"

  def ??(thenblock: ArithExpr) = {
    val predicate = this
    new {
      def !!(els: ArithExpr) = SimplifyIfThenElse(predicate, thenblock, els)
    }
  }

  val digest: Int = 0x7c6736c0 ^ lhs.digest() ^ rhs.digest() ^ op.hashCode()
}

object Predicate {

  /**
    * List of comparison operators
    */
  object Operator extends Enumeration {
    type Operator = Value
    val < = Value("<")
    val > = Value(">")
    val <= = Value("<=")
    val >= = Value(">=")
    val != = Value("!=")
    val == = Value("==")
  }

}
