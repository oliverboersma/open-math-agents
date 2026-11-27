import Mathlib

/-!
# The harmonic threshold in OEIS A002387

Benoit Cloitre's October 23, 2002 conjecture gives the first harmonic number
strictly above each integer n > 1 by rounding exp(n − γ) to the nearest integer
via the specified floor formula.

Source: OEIS A002387, https://oeis.org/A002387.
-/

namespace OMA.S_oeis_a002387

theorem main : ∀ n : ℕ, 1 < n →
    IsLeast {k : ℕ | (n : ℚ) < harmonic k}
      ⌊Real.exp ((n : ℝ) - Real.eulerMascheroniConstant) + 1 / 2⌋₊ := by
  sorry

end OMA.S_oeis_a002387
