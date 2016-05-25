package apart
package arithmetic
package simplifier

object SimplifyFloor {

  def apply(ae: ArithExpr): ArithExpr = {
    ae match {
      case c: Cst => c
      case _ =>
        try {
          val d = new Floor(ae).evalDbl
          assert(d.isValidInt)
          new Cst(d.toInt)
        } catch {
          case _: NotEvaluableException =>
            // ok let's try to evaluate floor of min and max
            try {
              val min = new Floor(ae.min).evalDbl
              val max = new Floor(ae.max).evalDbl
              if (min == max) {
                assert(min.isValidInt)
                return new Cst(min.toInt)
              }
            } catch {
              case _: NotEvaluableException => new Floor(ae) with SimplifiedExpr
              case e: Throwable => throw e
            }
            new Floor(ae) with SimplifiedExpr
          case e: Throwable => throw e
        }
    }
  }

}
