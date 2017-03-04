package lift
package arithmetic
package simplifier

object SimplifyFloor {

  def apply(ae: ArithExpr): ArithExpr = {
    ae match {
      case c: Cst => c
      case _ =>
        try {
          val d = new FloorFunction(ae).evalDouble
          assert(d.isValidInt)
          new Cst(d.toInt)
        } catch {
          case NotEvaluableException() =>
            // ok let's try to evaluate floor of min and max
            try {
              val min = new FloorFunction(ae.min).evalDouble
              val max = new FloorFunction(ae.max).evalDouble
              if (min == max) {
                assert(min.isValidInt)
                return new Cst(min.toInt)
              }
            } catch {
              case NotEvaluableException() => new FloorFunction(ae) with SimplifiedExpr
              case e: Throwable => throw e
            }
            new FloorFunction(ae) with SimplifiedExpr
          case e: Throwable => throw e
        }
    }
  }

}
