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

      // A * x1 * x2 * … xn /^ a == x1 * x2 * … * xn
      case (Prod(terms), r) if terms.contains(r) =>
        val idx = terms.indexOf(r)
        val remaining = terms.slice(0, idx) ++ terms.slice(idx + 1, terms.length)
        if (remaining.length == 1) remaining.head
        else Prod(remaining)

      // Σ a * xi /^ Σ xi == a
      case (Sum(lTerms), Sum(rTerms)) if
          lTerms.length == rTerms.length &&
          (lTerms zip rTerms).map(p => p._1 /^ p._2).distinct.length == 1 &&
          // This last condition is not necessary but it should prevent infinite simplifications
          (lTerms.head /^ rTerms.head) != Prod(List(lTerms.head, Pow(rTerms.head, Cst(-1)))) =>
        lTerms.head /^ rTerms.head

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
