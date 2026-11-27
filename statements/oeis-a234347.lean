import Mathlib

/-!
# A234347: a(n) = |{0 < k < n: 3^k + 3^{phi(n-k)/2} - 1 is prime}|, where phi(.) is Euler's totient function.

Source: https://oeis.org/A234347
Credit: @LAPRAI

Formalizes the OEIS comment: Conjecture: a(n) > 0 for all n > 3.

Conventions: `phi` is `Nat.totient` and `phi(n-k)/2` is natural division (`phi(m)` is even for `m > 2`).
-/

namespace OMA.S_oeis_a234347

/-- For every `n > 3` some `0 < k < n` makes `3^k + 3^(phi(n-k)/2) - 1` prime. -/
theorem main : ∀ n : ℕ, 3 < n →
    ∃ k : ℕ, 0 < k ∧ k < n ∧ (3 ^ k + 3 ^ (Nat.totient (n - k) / 2) - 1).Prime := by
  sorry

end OMA.S_oeis_a234347
