import Mathlib

/-!
# A255746: Squarefree semiprimes n such that n+4 is also a squarefree semiprime.

Source: https://oeis.org/A255746
Credit: @LAPRAI

Formalizes the OEIS comment: Conjecturally, the sequence is infinite.

Conventions: a squarefree semiprime is a squarefree number with exactly two prime factors counted with multiplicity (`ArithmeticFunction.cardFactors n = 2`).
-/

namespace OMA.S_oeis_a255746

/-- `n` is a squarefree semiprime. -/
def IsSqfSemiprime (n : ℕ) : Prop := Squarefree n ∧ ArithmeticFunction.cardFactors n = 2

/-- There are infinitely many `n` with `n` and `n + 4` squarefree semiprimes. -/
theorem main : {n : ℕ | IsSqfSemiprime n ∧ IsSqfSemiprime (n + 4)}.Infinite := by
  sorry

end OMA.S_oeis_a255746
