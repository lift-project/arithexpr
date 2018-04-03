package lift.testing

import lift.arithmetic._
import org.junit.Test
import org.junit.Assert._

class TestIfThenElseSimplification {

  @Test
  def ifThenElseWithVars(): Unit = {
    val t = Var("T")
    val f = Var("F")
    val expr1 = (SizeVar("N") ge Cst(0)) ?? t !! f
    val expr2 = (1 + SizeVar("N") ge Cst(0)) ?? t !! f

    assertEquals(expr1, t)
    assertEquals(expr2, t)
  }

  @Test
  def ifThenElseUseRangeInformation(): Unit = {
    val t = Var("T")
    val f = Var("F")
    val N = SizeVar("N")
    val range = RangeAdd(1, N, 1)
    val M = Var("M", range)

    val expr1 = (M lt N) ?? t !! f
    val expr2 = (M gt 0) ?? t !! f
    assertEquals(expr1, t)
    assertEquals(expr2, t)
  }

}