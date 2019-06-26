package lift
package arithmetic
package simplifier

import scala.language.implicitConversions

/**
 * Generic expression simplifier.
 */
object ExprSimplifier {

  /**
   * Simplify an expression.
   * @param expr The expression to simplify.
   * @return A simplified expression equivalent to expr or expr itself if it is already simplified.
   */
  def apply(expr: ArithExpr): ArithExpr with SimplifiedExpr = expr match {
    case e: SimplifiedExpr => e
    case v: Var => SimplifyVar(v)
    case Pow(x, y) => SimplifyPow(x, y)
    case Prod(factors) => factors.reduce(_*_)
    case s: Sum => s.terms.reduce(_+_)
    case Mod(a, b) => SimplifyMod(a, b)
    case IntDiv(a, b) => SimplifyIntDiv(a, b)
    case IfThenElse(test, t, el) => SimplifyIfThenElse(test, t, el)
    case AbsFunction(ae) => SimplifyAbs(ae)
    case FloorFunction(ae) => SimplifyFloor(ae)
    case CeilingFunction(ae) => SimplifyCeiling(ae)
    case bs:BigSum => SimplifyBigSum(bs)
  }

  def apply(aes: Seq[ArithExpr]): Seq[ArithExpr with SimplifiedExpr] = aes.map(apply)
  def apply(aes: List[ArithExpr]): List[ArithExpr with SimplifiedExpr] = aes.map(apply)
}
