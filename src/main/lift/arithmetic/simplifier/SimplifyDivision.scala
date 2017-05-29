package lift
package arithmetic
package simplifier


object SimplifyDivision {

  def apply(numer: ArithExpr, denom: ArithExpr): ArithExpr = {
    (numer, denom) match {
      case (x, Cst(1)) => x
      case (Cst(x), Cst(y)) if x % y == 0 => Cst(x / y)
      case (x, y) if x == y => Cst(1)
      case (x, y) if x == (y * Cst(-1)) => Cst(-1)
      
      // SPECIAL CASES
      // cn + mn /^ c+m == n(c+m) /^ c+m => n
      case (
        Sum(
          Prod(Cst(c1) :: (n2: Var) :: Nil) ::
          Prod((m1: Var) :: (n1: Var) :: Nil) ::  Nil),
        Sum(Cst(c2) :: (m2: Var) :: Nil)
        ) if c1 == c2 && ((m1 == m2 && n1 == n2) || (m1 == n2 && m2 == n1)) => n2

      // i + ca + ma /^ c+m => a + (i /^ c+m)
      case (
        Sum(
          (i: Var) :: Prod(Cst(c1) :: (a2: ArithExpr) :: Nil) ::
          Prod((m1: Var) :: (a1: ArithExpr) :: Nil) :: Nil),
        Sum(Cst(c2) :: (m2: Var) :: Nil)
        ) if c1 == c2 && m1 == m2 && a1 == a2 => a1 + (i /^ (c1 + m1))
        
      case (x, y) => x * (y pow -1)
    }
  }

}
