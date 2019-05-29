package lift
package arithmetic

import lift.arithmetic.Predicate.Operator.Operator
import lift.arithmetic.simplifier.SimplifyIfThenElse

/**
  * Predicate object. Stores two arithmetic expressions and an operator
  */
case class Predicate(lhs: ArithExpr with SimplifiedExpr,
                     rhs: ArithExpr with SimplifiedExpr,
                     op: Predicate.Operator.Operator) {

  override lazy val toString: String = s"($lhs $op $rhs)"

  sealed class IfWithoutElse(predicate: Predicate, thenBlock: ArithExpr) {
    def !!(elseBlock: ArithExpr) = SimplifyIfThenElse(predicate, thenBlock, elseBlock)
  }

  def ??(thenBlock: ArithExpr) = new IfWithoutElse(this, thenBlock)

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

  /**
    * Converts a Predicate to a Scala notation String which can be evaluated into a valid Predicate
    */
  def printToScalaString(p: Predicate, printNonFixedVarIds: Boolean): String =
    s"Predicate(${ArithExpr.printToScalaString(p.lhs, printNonFixedVarIds)}," +
      s"${ArithExpr.printToScalaString(p.rhs, printNonFixedVarIds)}, ${p.op})"

}
