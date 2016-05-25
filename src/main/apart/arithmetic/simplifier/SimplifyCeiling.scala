package apart
package arithmetic
package simplifier

object SimplifyCeiling {

  def apply(ae: ArithExpr): ArithExpr = {
    ae match {
      case c: Cst => c
      case _ =>
        try {
          val d = new Ceiling(ae).evalDbl
          assert(d.isValidInt)
          new Cst(d.toInt)
        } catch {
          case _: NotEvaluableException =>
            // ok let's try to evaluate ceiling of min and max
            try {
              val min = new Ceiling(ae.min).evalDbl
              val max = new Ceiling(ae.max).evalDbl
              if (min == max) {
                assert(min.isValidInt)
                return new Cst(min.toInt)
              }
            } catch {
              case _: NotEvaluableException => new Ceiling(ae) with SimplifiedExpr
              case e: Throwable => throw e
            }
            new Ceiling(ae) with SimplifiedExpr
          case e: Throwable => throw e
        }
    }
  }

}
