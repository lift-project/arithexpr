package lift
package arithmetic

object PerformSimplification {
  var simplify = System.getenv("LIFT_NO_ARITH_SIMPL") == null
  def apply() = simplify
}
