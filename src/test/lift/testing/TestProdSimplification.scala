package lift.testing

import lift.arithmetic.{Cst, RangeAdd, Var}
import org.junit.Assert.assertEquals
import org.junit.Test

class TestProdSimplification {
  @Test
  def trivialRange(): Unit = {
    val v = Var("v", range = RangeAdd(0, 1, 1))
    assertEquals(Cst(0), v * Cst(16))
  }
}