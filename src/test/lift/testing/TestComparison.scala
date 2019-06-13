package lift.testing

import lift.arithmetic._
import lift.arithmetic.simplifier.SimplifyProd
import org.junit.Assert.assertEquals
import org.junit.Test

class TestComparison {
  /**
   * The simplification
   *
   * ```
   * lhs < x1 * x2 * … xn * 1/y1 * 1/y2 * … 1/ym
   * -> sign(Π yi) * (Π yi) * lhs < sign(Π yi) * Π xi
   * ```
   *
   * can lead to an empty product on the right hand side of `<`. It must be
   * replaced by `Cst(1)` since `Prod(Nil)` is not valid.
   */
  @Test
  def testInversion(): Unit = {
    val a = Var("a", range = StartFromRange(1))
    val b = Var("b", range = StartFromRange(1))
    val rhs = SimplifyProd(List(Cst(1) /^ a, Cst(1) /^ b))
    assertEquals(Some(false), ArithExpr.isSmaller(1, rhs))
  }

  /** Used to lead to a stack overflow */
  @Test
  def smallerOpaqueVar(): Unit = {
    val v = new OpaqueVar(Var("v"))
    assertEquals(None, ArithExpr.isSmaller(v/2, 1))
  }
}
