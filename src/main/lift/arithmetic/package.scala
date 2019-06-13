package lift

package object arithmetic {

  object PerformSimplification {
    var simplify: Boolean = System.getenv("LIFT_NO_ARITH_SIMPL") == null
    def apply(): Boolean = simplify
  }

  object NewFactorizationOfSum {
    var enabled: Boolean = System.getenv("LIFT_ARITH_FACTORIZE_SMART") != null
    def apply(): Boolean = enabled
  }

  def removeAt[T](i: Int, from: List[T]): List[T] = from.take(i) ++ from.drop(i + 1)
  def replaceAt[T](i: Int, replacement: T, from: List[T]): List[T] = from.zipWithIndex.map(element =>
    if (element._2 == i) replacement else element._1)
}
