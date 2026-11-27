import Mathlib

/-!
# OEIS A226224

In a base b ≥ 2, consider the positive integers whose digit sum is their
square root. A226224 takes the largest such integer and A226087 counts
them. Since 1 always qualifies, a largest value of 1 is equivalent to
there being exactly one positive solution. The conjecture states that
this happens precisely in base 2.

Sources: https://oeis.org/A226224 and https://oeis.org/A226087
-/

namespace OMA.S_oeis_a226224

def solutions (b : ℕ) : Set ℕ := {k | 0 < k ∧ ∃ r : ℕ, r^2=k ∧ (Nat.digits b k).sum=r}

theorem main : ∀ b : ℕ, 2 ≤ b → (IsGreatest (solutions b) 1 ↔ b = 2) := by
  sorry

end OMA.S_oeis_a226224
