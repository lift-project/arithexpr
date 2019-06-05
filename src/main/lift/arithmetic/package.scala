package lift

import org.junit.Assume

package object arithmetic {

  object PerformSimplification {
    var simplify = System.getenv("LIFT_NO_ARITH_SIMPL") == null
    def apply() = simplify
  }

  /**
    * Simplification level allows to specify how advanced should simplification be.
    * Higher level simplify more expressions, but slower.
    * Default level: O0
    * O1: enables detection of temporary representations of Sum as a Prod (see Sum.asProd)
    */
  object SimplificationLevel extends Enumeration {
    type SimplificationLevel = Value
    val O0, O1 = Value

    private val level: SimplificationLevel.Value = System.getenv("LIFT_ARITH_SIMPL_LEVEL") match {
      case "O1" | "o1" => O1
      case _ => O0
    }

    def apply(): SimplificationLevel = level

    val o0: Boolean = level == O0
    val o1: Boolean = level == O1

    def assumeLevelNoLessThan(minLevel: SimplificationLevel): Unit = {
      Assume.assumeTrue(f"Simplification level must be $minLevel or higher. Got $level.", level >= minLevel)
    }
  }
}
