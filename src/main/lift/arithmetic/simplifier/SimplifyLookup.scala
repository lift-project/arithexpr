package lift
package arithmetic
package simplifier

object SimplifyLookup {

  def apply(table: Seq[ArithExpr], index: ArithExpr, id: Int): ArithExpr = {
    index match {
      case c: Cst => table.apply(c.evalToInt)
      case _ => new Lookup(table, index, id)
    }
  }

}
