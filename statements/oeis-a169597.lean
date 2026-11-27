import Mathlib

/-!
# A169597: Numbers congruent to 2 or 15 mod 19

Source: https://oeis.org/A169597
Credit: @AkiRA-COM-FP

Formalizes the OEIS A169597 conjecture: for no term `n > 2` congruent to `2` or `15` mod `19`
is `36*n^2 + 72*n + 35` equal to `p * (p + 2)` where `p` and `p + 2` are twin primes.
-/

namespace OMA.S_oeis_a169597

/-- For every `n > 2` with `n % 19 = 2` or `n % 19 = 15`, `36*n^2 + 72*n + 35`
is not equal to `p * (p + 2)` for twin primes `p, p + 2`. -/
theorem main :
    ∀ n : ℕ, 2 < n → (n % 19 = 2 ∨ n % 19 = 15) →
      ∀ p : ℕ, Nat.Prime p → Nat.Prime (p + 2) →
        36 * n ^ 2 + 72 * n + 35 ≠ p * (p + 2) := by
  sorry

end OMA.S_oeis_a169597
