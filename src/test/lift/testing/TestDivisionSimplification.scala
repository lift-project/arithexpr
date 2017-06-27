package lift.testing

import lift.arithmetic._
import opencl.generator.OclFunction
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
    val v_O_0 = Var("v_O_0",StartFromRange(1))
    val v_gl_id_13 =   OclFunction("get_global_id", 0, ContinuousRange(0, OclFunction("get_global_size", 0, ContinuousRange(1,PosInf))))
    val inSize  = Cst(3)
    val i = (((4+(2*v_O_0))) / ((2+v_O_0))+(3*v_gl_id_13))

    i/inSize
    println("made it !")
  }
}