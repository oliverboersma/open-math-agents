import Mathlib

/-!
# Perfect powers among derangement numbers

Zhi-Wei Sun's conjecture from 9 January 2025, recorded at https://oeis.org/A000166.
Lean statement by @dk8827.
-/

namespace OMA.S_oeis_a000166

/-- Among the derangement numbers indexed by `n > 2`, the only perfect power is
the fourth term, which is `3 ^ 2`. -/
theorem main :
    numDerangements 4 = 3 ^ 2 ∧
      ∀ n : ℕ, 2 < n →
        (∃ a k : ℕ, 1 < a ∧ 1 < k ∧ numDerangements n = a ^ k) → n = 4 := by
  sorry

end OMA.S_oeis_a000166
