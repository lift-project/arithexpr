package apart.testing

import apart.arithmetic._
import org.junit.Test
import org.junit.Assert._

/**
 * Associativity and commutativity tests
 */
class TestAssocAndComm {
  val a = Var("a")
  val b = Var("b")
  val c = Var("c")
  val d = Var("d")

  @Test
  def testAddition(): Unit = {
    assertEquals(a + b, b + a)
    assertEquals(a + b + c, c + b + a)

    assertEquals(a + (b + c), (a + b) + c)
  }

  @Test
  def testMultiplication(): Unit = {
    assertEquals(a * b, b * a)
    assertEquals(a * b * c, c * b * a)

    assertEquals(a * (b * c), (a * b) * c)
  }

  @Test
  def testDivision(): Unit = {
    assertNotEquals(a / b, b / a)
    assertNotEquals(a / b / c, c / b / a)

    assertNotEquals(a / (b / c), (a / b) / c)
  }

  @Test
  def testMod(): Unit = {
    assertNotEquals(a % b, b % a)
    assertNotEquals(a % b % c, c % b % a)

    assertNotEquals(a % (b % c), (a % b) % c)
  }

  @Test
  def EquivalentExpr(): Unit = {
    assertEquals(a + a + b + c + a + b, 2 * a + a + 2 * b + c)
  }
}
