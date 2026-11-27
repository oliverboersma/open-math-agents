import Mathlib

/-!
# A056084: Numbers k such that k^8 == 1 (mod 9^3)

Source: https://oeis.org/A056084
Credit: @AkiRA-COM-FP

Formalizes Philipp Emanuel Weidmann's OEIS A056084 conjecture (offset 1):
for every `n >= 1`, `a(n) = (1458*n - 729 + (-1)^n * 725) / 4`.
-/

namespace OMA.S_oeis_a056084

/-- The `n`-th (1-indexed) natural number `k` satisfying `k^8 % 9^3 = 1`. -/
noncomputable def a (n : ℕ) : ℕ :=
  Nat.nth (fun k : ℕ => k ^ 8 % 9 ^ 3 = 1) (n - 1)

/-- For every `n >= 1`, `a(n) = (1458*n - 729 + (-1)^n * 725) / 4`. -/
theorem main :
    ∀ n : ℕ, 1 ≤ n →
      (a n : ℚ) = (1458 * (n : ℚ) - 729 + (-1 : ℚ) ^ n * 725) / 4 := by
  sorry

end OMA.S_oeis_a056084
