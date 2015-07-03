package apart.testing

import apart.arithmetic._
import org.junit.Test
import org.junit.Assert._

class TestSumSimplification {
  val a = Var("a")
  val b = Var("b")
  val c = Var("c")
  val d = Var("d")

  @Test
  def addZero() = {
    assertEquals(a, a + 0)
  }

  @Test
  def cancellingTerms() = {
    assertEquals(a, b + a - b)
  }

  @Test
  def constfolding() = {
    assertEquals(Cst(10), Cst(8) + Cst(2))
  }
}
