package lift
package arithmetic
package simplifier

object SimplifyCeiling {

  def apply(ae: ArithExpr with SimplifiedExpr): ArithExpr with SimplifiedExpr = {
    ae match {
      case c: Cst => c
      case i: IntDiv => i
      case NegInf => NegInf
      case PosInf => PosInf
      case _ =>
        try {
          val d = CeilingFunction(ae).evalDouble
          assert(d.isValidInt)
         Cst(d.toInt)
        } catch {
          case NotEvaluableException() =>
            // ok let's try to evaluate ceiling of min and max
            try {
              val min = CeilingFunction(ae.min).evalDouble
              val max = CeilingFunction(ae.max).evalDouble
              if (min == max) {
                assert(min.isValidInt)
                return Cst(min.toInt)
              }
            } catch {
              case NotEvaluableException() => new CeilingFunction(ae) with SimplifiedExpr
              case e: Throwable => throw e
            }
            new CeilingFunction(ae) with SimplifiedExpr
          case e: Throwable => throw e
        }
    }
  }

}
