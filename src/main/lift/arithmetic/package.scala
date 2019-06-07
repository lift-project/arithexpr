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
}
