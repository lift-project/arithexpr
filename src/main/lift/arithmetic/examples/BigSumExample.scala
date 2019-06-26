package lift.arithmetic.examples

import lift.arithmetic.{BigSum, Var}

object BigSumExample {

  private def inclusivity = BigSum(from = 0, upTo = 0, _ => 1)

  private def constant = BigSum(from = 0, upTo = 10 - 1, _ => 1)

  private def splitSum = BigSum(from = 0, upTo = 10 - 1, _ => Var("x") + Var("y"))

  private def euler = BigSum(from = 0, upTo = 10 - 1, x => x)

  private def takeOutFactor = BigSum(from = 0, upTo = 10 - 1, x => 2 * x)


  def main(args: Array[String]): Unit = {
    println(s"Inclusivity:$inclusivity")
    println(s"Constant: $constant")
    println(s"Spliting the sum:$splitSum")
    println(s"Euler simplification:$euler")
    println(s"Take out factor:$takeOutFactor")
  }
}
