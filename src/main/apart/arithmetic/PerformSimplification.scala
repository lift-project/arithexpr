package apart
package arithmetic

object PerformSimplification {
  val simplify = System.getenv("APART_NO_ARITH_SIMPL") == null
  def apply() = simplify
}
