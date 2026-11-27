import Mathlib

/-!
# A265739: Numbers k such that [pi*k - 1/k, pi*k + 1/k] contains an integer

Source: https://oeis.org/A265739
Credit: @AkiRA-COM-FP

Formalizes the OEIS A265739 conjecture (offset 1): there are infinitely many positive
integers `k` such that `[pi * k - 1 / k, pi * k + 1 / k]` contains an integer.
-/

namespace OMA.S_oeis_a265739

/-- Infinitely many positive integers `k` admit an integer within `1 / k` of `pi * k`. -/
theorem main :
    Set.Infinite {k : ℕ | 1 ≤ k ∧
      ∃ m : ℤ, |Real.pi * (k : ℝ) - (m : ℝ)| ≤ 1 / (k : ℝ)} := by
  sorry

end OMA.S_oeis_a265739
