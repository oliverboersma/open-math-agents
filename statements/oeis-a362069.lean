import Mathlib

/-!
# OEIS A362069

Alexandru Petrescu conjectured that infinitely many pairs of consecutive
integers belong to A362069. An integer `k` belongs to A362069 if adding
the sum of the decimal digits of its square to `k` gives a square.

Source: https://oeis.org/A362069
-/

namespace OMA.S_oeis_a362069

def term (k : ℕ) : Prop := ∃ r : ℕ, k + (Nat.digits 10 (k^2)).sum = r^2

theorem main : {k : ℕ | term k ∧ term (k+1)}.Infinite := by
  sorry

end OMA.S_oeis_a362069
