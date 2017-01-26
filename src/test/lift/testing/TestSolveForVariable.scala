package lift.testing

import lift.arithmetic._
import lift.arithmetic.NotSolvableException
import org.junit.Assert._
import org.junit.Test

/**
  * Test class for the Solve For Variable functionality
  */
class TestSolveForVariable {

  @Test
  def TestMult(): Unit = {
    val v = Var("X")
    val lhs = Prod(Cst(5) :: v :: Nil)
    val rhs = Prod(Cst(50) :: Nil)
    println(s"lhs: ${lhs}")
    println(s"rhs: ${rhs}")

    val nrhs = SolveForVariable(lhs, rhs)

    println(s"NewRHS: ${nrhs}")
    println(s"Expected: ${Cst(10)}")

    assertEquals(nrhs, Cst(10))
  }

  @Test
  def TestDiv(): Unit  = {
    val v = Var("X")
    val lhs = IntDiv(v, Cst(10))
    val rhs = Cst(10)
    println(s"lhs: ${lhs}")
    println(s"rhs: ${rhs}")

    val nrhs = SolveForVariable(lhs, rhs)

    println(s"NewRHS: ${nrhs}")
    println(s"Expected: ${Cst(10)}")

    assertEquals(nrhs, Cst(100))
  }

  @Test(expected=classOf[NotSolvableException])
  def TooManyVariables(): Unit = {
    val x = Var("X")
    val y = Var("Y")
    val lhs = Prod(x :: y :: Cst(5) :: Nil)
    val rhs = Prod(Cst(50) :: Nil)
    println(s"lhs: ${lhs}")
    println(s"rhs: ${rhs}")

    val nrhs = SolveForVariable(lhs, rhs)
  }

  @Test(expected=classOf[NotSolvableException])
  def NonLinearEquation (): Unit = {
    val x = Var("X")
    val lhs = Prod(x :: x :: Cst(5) :: Nil)
    val rhs = Prod(Cst(50) :: Nil)
    println(s"lhs: ${lhs}")
    println(s"rhs: ${rhs}")

    val nrhs = SolveForVariable(lhs, rhs)
  }

}
