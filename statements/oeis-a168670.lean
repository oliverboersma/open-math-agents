import Mathlib

/-!
# A168670: Numbers congruent to 1 or 8 mod 11

Source: https://oeis.org/A168670
Credit: @AkiRA-COM-FP

Formalizes the OEIS A168670 conjecture: for no term `n > 1` congruent to `1` or `8` mod `11`
is `36*n^2 + 72*n + 35` equal to `p * (p + 2)` where `p` and `p + 2` are twin primes.
-/

namespace OMA.S_oeis_a168670

/-- For every `n > 1` with `n % 11 = 1` or `n % 11 = 8`, `36*n^2 + 72*n + 35`
is not equal to `p * (p + 2)` for twin primes `p, p + 2`. -/
theorem main :
    ∀ n : ℕ, 1 < n → (n % 11 = 1 ∨ n % 11 = 8) →
      ∀ p : ℕ, Nat.Prime p → Nat.Prime (p + 2) →
        36 * n ^ 2 + 72 * n + 35 ≠ p * (p + 2) := by
  sorry

end OMA.S_oeis_a168670
