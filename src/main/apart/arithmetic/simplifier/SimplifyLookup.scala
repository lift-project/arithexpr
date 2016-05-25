package apart
package arithmetic
package simplifier

object SimplifyLookup {

  def apply(table: Seq[ArithExpr], index: ArithExpr, id: Int): ArithExpr = {
    index match {
      case c: Cst => table.apply(c.eval)
      case _ => new Lookup(table, index, id)
    }
  }

}
