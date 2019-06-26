package lift.testing

import lift.arithmetic._
import org.junit.Test
import org.junit.Assert.assertEquals

class TestDivisionSimplification {
  val a = Var("a")
  val b = Var("b")
  val c = Var("c")

  @Test
  def simpleFactorization(): Unit = {
    assertEquals(b, (Cst(42) * b + a * b) /^ (Cst(42) + a))
    assertEquals(a, (Cst(42) * a + b * a) /^ (Cst(42) + b))
  }
  
  @Test
  def factorizationInAffineExpr(): Unit = {
    assertEquals(
      c + a /^ (Cst(42) + b),
      (a + Cst(42) * c + b * c) /^ (Cst(42) + b)
    )
  }

  @Test def issueNumber4(): Unit = {
    val v_O = Var("v_O", StartFromRange(1))
    val gl_id = Var("gl_id", ContinuousRange(0, Var("gl_size", ContinuousRange(1, PosInf))))
    val inSize  = Cst(3)
    val i = (4 + (2 * v_O)) / (2 + v_O) + (3 * gl_id)

    assertEquals(gl_id, i/inSize)
  }

  @Test
  def noSimplification(): Unit = {
    val w = Var("w", RangeAdd(3, PosInf, 1))
    val x = Var("x", RangeAdd(0, w, 1))
    val expr = (Cst(1) + x + w) / (Cst(2) + w)
    assertEquals((Cst(1) + x + w) / (Cst(2) + w), expr)
  }
}