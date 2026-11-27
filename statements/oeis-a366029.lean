import Mathlib

/-!
# A366029: Numbers k > 1 such that (k-1)^(2^k-2) == 1 (mod (2^k-1)*k^2).

Source: https://oeis.org/A366029
Credit: @mbilenko03

Conjecture (from the entry): for `k > 1`, `(2^k-1)*k^2` divides `(k-1)^(2^k-2) - 1` if and only if
`2^k - 1` is a (Mersenne) prime or `k = 2^(2^m) + 1` (is a Fermat number).

(The entry's next comment, about which primes in the sequence are not Mersenne exponents, is a
consequence of this conjecture and is not stated separately.)

Conventions:
- Natural-number arithmetic; for `k > 1` we have `k - 1 ≥ 1`, so `(k-1)^(2^k-2) - 1` is the true
  difference (no truncation).
- A Fermat number is `2^(2^m) + 1` for some `m ≥ 0`, prime or not.
-/

namespace OMA.S_oeis_a366029

theorem main :
    ∀ k : ℕ, 1 < k →
      ((2 ^ k - 1) * k ^ 2 ∣ (k - 1) ^ (2 ^ k - 2) - 1 ↔
        (2 ^ k - 1).Prime ∨ ∃ m : ℕ, k = 2 ^ (2 ^ m) + 1) := by
  sorry

end OMA.S_oeis_a366029
