import Mathlib

/-!
# A169599: Numbers congruent to 4 or 23 mod 29

Source: https://oeis.org/A169599
Credit: @AkiRA-COM-FP

Formalizes the OEIS A169599 conjecture: for no term `n > 4` congruent to `4` or `23` mod `29`
is `36*n^2 + 72*n + 35` equal to `p * (p + 2)` where `p` and `p + 2` are twin primes.
-/

namespace OMA.S_oeis_a169599

/-- For every `n > 4` with `n % 29 = 4` or `n % 29 = 23`, `36*n^2 + 72*n + 35`
is not equal to `p * (p + 2)` for twin primes `p, p + 2`. -/
theorem main :
    ∀ n : ℕ, 4 < n → (n % 29 = 4 ∨ n % 29 = 23) →
      ∀ p : ℕ, Nat.Prime p → Nat.Prime (p + 2) →
        36 * n ^ 2 + 72 * n + 35 ≠ p * (p + 2) := by
  sorry

end OMA.S_oeis_a169599
