package lift.testing

import java.io.File

import lift.arithmetic.{Cst, Var, ArithExpr}
import org.junit.Test
import scala.language.postfixOps

/**
 * Generate C Unit test cases to cross validate the expression simplifier and the actual C behavior
 */
class generateCUnits {
  // var pool
  val pool = List(Var("a"), Var("b"), Var("c"), Var("d"))
  val value_map = Map[ArithExpr, ArithExpr](
    (pool.head, Cst(12)),
    (pool(1), Cst(57)),
    (pool(2), Cst(2)),
    (pool(3), Cst(4))
  )

  val rd = new scala.util.Random(1)

  def out(x: String, sb: StringBuilder): Unit = {
    sb ++= s"$x;\n"
  }

  def newTerm(): ArithExpr = {
    val c = rd.nextInt(3)
    if(c == 0)
      pool(rd.nextInt(pool.length))
    else
    Cst(rd.nextInt(20)+1)
  }

  def addTerm(a: ArithExpr, sb: StringBuilder): ArithExpr = {
    val seed = rd.nextInt(9)
    val other = newTerm()
    sb ++= "  res "
    if (seed == 0) {
      out(s"%= $other",sb)
      a % other
    }
    else if (seed < 3) {
      out(s"-= $other",sb)
      a - other
    }
    else if (seed < 4) {
      out(s"/= $other",sb)
      a / other
    }
    else if (seed < 6) {
      out(s"*= $other",sb)
      a * other
    }
    else if (seed == 6) {
      out(s" = pow(res,($other % 3))",sb)
      a pow (other % 3)
    }
    else {
      out(s"+= $other",sb)
      a + other
    }
  }

  @Test
  def generateRandomTests(){

    var sb = new StringBuilder

    for( i <- 1 to 100) {
      System.out.println(s"Generating test $i out of 100")
      var a = newTerm()
      sb ++= s"TEST(ArithExpr, Test$i) {\n  int res = ${a.toString};\n"
      for (i <- 0 to 5) { a = addTerm(a, sb)}
      val sub = ArithExpr.substitute(a, value_map)
      sb ++=
        s"""
          |  // Partially evaluated expression:
          |  EXPECT_EQ(res, $a) << "Partially evaluated expression does not match";
          |
          |  // After substitution:
          |  EXPECT_EQ(res, $sub) << "Wrong result after substitution";
          |}
          |
          |""".stripMargin
    }

    val f = new File("gtest.cpp")
    val p = new java.io.PrintWriter(f)
    try { p.write(
      s"""
        |#include "gtest/gtest.h"
        |#include <cmath>
        |
        |int pow(int a, int b) {
        |  return std::pow(a,b);
        |}
        |
        |${(value_map map {case (a,b) => s"int $a = $b;\n" } toList).reduce(_+_)}
        |
        |$sb
        |
        |int main(int argc, char **argv) {
        |  ::testing::InitGoogleTest(&argc, argv);
        |  return RUN_ALL_TESTS();
        |}
      """.stripMargin) } finally { p.close() }
  }
}
