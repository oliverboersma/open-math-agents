import Mathlib

/-!
# A171141: Numbers congruent to 6 or 33 mod 41

Source: https://oeis.org/A171141
Credit: @AkiRA-COM-FP

Formalizes the OEIS A171141 conjecture: for no term `n > 6` congruent to `6` or `33` mod `41`
is `36*n^2 + 72*n + 35` equal to `p * (p + 2)` where `p` and `p + 2` are twin primes.
-/

namespace OMA.S_oeis_a171141

/-- For every `n > 6` with `n % 41 = 6` or `n % 41 = 33`, `36*n^2 + 72*n + 35`
is not equal to `p * (p + 2)` for twin primes `p, p + 2`. -/
theorem main :
    ∀ n : ℕ, 6 < n → (n % 41 = 6 ∨ n % 41 = 33) →
      ∀ p : ℕ, Nat.Prime p → Nat.Prime (p + 2) →
        36 * n ^ 2 + 72 * n + 35 ≠ p * (p + 2) := by
  sorry

end OMA.S_oeis_a171141
