package lift
package arithmetic
package simplifier

object SimplifyLookup {

  def apply(table: Seq[ArithExpr with SimplifiedExpr], index: ArithExpr with SimplifiedExpr, id: Int):
  ArithExpr with SimplifiedExpr = {
    index match {
      case c: Cst => table.apply(c.eval)
      case _ => new Lookup(table, index, id)
    }
  }

}
