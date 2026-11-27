import Mathlib

/-!
# A214074: Least m>0 such that 2^n-m and 3^n-m are relatively prime

Source: https://oeis.org/A214074
Credit: @niclorusso

Conjecture (in the comments of A214074): a(n) = 3 if and only if n = 330*k-209 for some k>=1.

Conventions:
* The sequence has offset 1. 2^n - m and 3^n - m are integers (they can be negative or zero), and
  "relatively prime" means their gcd is 1 (`Int.gcd`, the gcd of the absolute values).
* a(n) = 3 means that 3 is the least m > 0 with gcd(2^n - m, 3^n - m) = 1 (`IsLeast`). Such an m
  always exists (m = 2^n - 1 gives gcd 1).
-/

namespace OMA.S_oeis_a214074

/-- The conjecture on A214074: for `n >= 1`, the least `m > 0` with `gcd(2^n - m, 3^n - m) = 1`
is `3` if and only if `n = 330k - 209` for some `k >= 1`. -/
theorem main : ∀ n : ℕ, 1 ≤ n →
    (IsLeast {m : ℕ | 0 < m ∧ Int.gcd ((2 : ℤ) ^ n - m) ((3 : ℤ) ^ n - m) = 1} 3 ↔
      ∃ k : ℕ, 1 ≤ k ∧ n = 330 * k - 209) := by
  sorry

end OMA.S_oeis_a214074
