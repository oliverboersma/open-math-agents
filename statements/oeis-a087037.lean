import Mathlib

/-!
# A087037: Smallest integer x > 0 such that x^x + n is prime, or 0 if no such x exists

Source: https://oeis.org/A087037
Credit: @AkiRA-COM-FP

Formalizes the OEIS A087037 conjecture: for every integer `n >= 1`, there exists
an integer `x > 0` such that `x^x + n` is prime.
(Disproved by Firoozbakht and Hasler: fails for `n = (6*k - 1)^3`, e.g. `n = 125`.)
-/

namespace OMA.S_oeis_a087037

/-- Conjecture: for every `n >= 1`, there exists `x > 0` with `x^x + n` prime. -/
theorem main :
    ∀ n : ℕ, 1 ≤ n → ∃ x : ℕ, 0 < x ∧ (x ^ x + n).Prime := by
  sorry

end OMA.S_oeis_a087037
