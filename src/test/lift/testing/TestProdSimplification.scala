package lift.testing

import lift.arithmetic.ArithExpr.intToCst
import lift.arithmetic.{Cst, RangeAdd, Var}
import org.junit.Assert.assertEquals
import org.junit.Test

class TestProdSimplification {
  @Test
  def trivialRange(): Unit = {
    val v = Var("v", range = RangeAdd(0, 1, 1))
    assertEquals(Cst(0), v * Cst(16))
  }

  @Test
  def prodOfFractions(): Unit = {
    val v = Var("v")
    assertEquals(v /^ 8, (v /^ 2) /^ 4)
    assertEquals(v /^ 8, (v /^ 2) * (Cst(1) /^ 4))
  }

  @Test
  def prodOfMultipleFractions(): Unit = {
    val a = Var("a")
    val b = Var("b")
    val c = Var("c")
    val e1 = a * (1/^(b*c))
    val e2 = b * c
    assertEquals(a, e1 * e2)
  }
}