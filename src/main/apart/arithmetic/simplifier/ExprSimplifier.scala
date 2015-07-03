package apart
package arithmetic
package simplifier

import apart.arithmetic._

object ExprSimplifier {

  def simplify(e: ArithExpr): ArithExpr = {
    if(e.simplified) e
    else  e match {
      case Pow(x,y) =>
        SimplifyPow(x,y)
      case p: Prod =>
        p.factors.reduce(_*_)
      case s: Sum =>
        s.terms.reduce(_+_)
      case Mod(a,b) =>
        SimplifyMod(a,b)
      case IntDiv(a,b) =>
        SimplifyIntDiv(a,b)
      case IfThenElse(test,t,el) =>
        SimplifyIfThenElse(test,t,el)
      case Log(x,y) => e
      case _ => throw new RuntimeException(s"Simplify cannot handle the expression ${e}")
    }
  }

  def apply(expr: ArithExpr): ArithExpr = {
    simplify(expr)
  }

}
