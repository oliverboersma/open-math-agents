import Mathlib

/-!
# A182457: a(0)=0, a(1)=1, a(n) = (a(n-2)*a(n-1)+1) mod n.

Source: https://oeis.org/A182457
Credit: @LAPRAI

Formalizes the OEIS comment: Conjecture: a(n) contains infinitely many zeros.

Conventions: offset 0; `mod` is natural `%`.
-/

namespace OMA.S_oeis_a182457

/-- `a(0) = 0`, `a(1) = 1`, `a(n) = (a(n-2)*a(n-1) + 1) mod n`. -/
def a : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 => (a n * a (n + 1) + 1) % (n + 2)

/-- `a(n) = 0` for infinitely many `n`. -/
theorem main : {n : ℕ | a n = 0}.Infinite := by
  sorry

end OMA.S_oeis_a182457
