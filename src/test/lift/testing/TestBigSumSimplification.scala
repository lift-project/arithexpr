package lift.testing

import lift.arithmetic.BoolExpr.ArithPredicate
import lift.arithmetic._
import org.junit.Assert.assertEquals
import org.junit.Test

class TestBigSumSimplification {

  @Test
  def inclusivity = assertEquals(BigSum(from = 0, upTo = 0, _ => 1), Cst(1))

  @Test
  def constant = assertEquals(BigSum(from = 0, upTo = 10 - 1, _ => 1), Cst(10))

  @Test
  def splitSum = {
    val x = Var("x")
    val y = Var("y")
    val bs = BigSum(from = 0, upTo = 10 - 1, _ => x + y)
    assertEquals(bs, (10*x) + (10*y))
  }

  @Test
  def euler = assertEquals(BigSum(from = 0, upTo = 10 - 1, x => x), Cst(45))

  @Test
  def takeOutFactorAndThenEuler =assertEquals(BigSum(from = 0, upTo = 10 - 1, x => 2 * x), Cst(90))
}
