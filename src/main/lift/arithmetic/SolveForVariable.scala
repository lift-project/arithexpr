package lift
package arithmetic
import simplifier._

object SolveForVariable {

  val NotSolvable = new NotSolvableException

  /**
    * Given two arithmetic expressions, a = b, with variable V \in a, solve for V
    *
    * @param a The expression containing V
    * @param b A second expression that equals a
    * @return A (simplified) arithmetic expression that equals V
    */
  def apply(a: ArithExpr, b: ArithExpr): ArithExpr = {
    // simple checks
    if(a.varList.size > 1){
      println(s"Too many variables in expression, expected one variable, got ${a.varList}")
      throw SolveForVariable.NotSolvable
    }
    // ideally we can check by counting the instances, but instead,
    // we'll just have to check all the subterms at every stage
    if(instanceCount(a, a.varList.head) != 1) {
      println(s"Too many instances of variable ${a.varList.head} in expression")
      throw SolveForVariable.NotSolvable
    }
    val v = a.varList.head
    // otherwise, solve, with v - the variable we want to solve for
    solve(a,b,v)
  }

  def solve(a: ArithExpr, b: ArithExpr, v: Var): ArithExpr = {
    (a, b) match {
      // Base case: LHS is a single variable, just return the right hand expression
      case (x: Var, y) => ExprSimplifier(y)

      // Var*Expr = Expr -> Var = Expr/Cst
      case (Prod(factors), y) => {
        val (c: List[ArithExpr], nc: List[ArithExpr]) = factors.partition(e => ArithExpr.contains(e,v))
        if(c.length != 1) {
          throw SolveForVariable.NotSolvable
        }
        solve(c(0), IntDiv(b, Prod(nc)), v)
      }

      // Var/Cst = Expr -> Var = Expr*Cst
      case (IntDiv(x1, x2), y) => {
        (ArithExpr.contains(x1, v), ArithExpr.contains(x2, v)) match {
          case (true, false) => solve(x1, Prod(x2 :: b :: Nil), v)
          case (false, true) => solve(x2, IntDiv(x1, y), v)
          case _ => throw SolveForVariable.NotSolvable
        }
      }

      // otherwise, we don't support it yet...
      case _ => throw SolveForVariable.NotSolvable
    }
  }

  def instanceCount(expr: ArithExpr, elem: ArithExpr): Int = {
    var mc = 0
    ArithExpr.visit(expr, e => if (e == elem) mc = mc+1)
    mc
  }



}
