import Mathlib

/-!
# Mersenne exponents and a Fermat-type congruence

Conjectures recorded at https://oeis.org/A000043: for an integer `k > 1`, the number `2 ^ k - 1` is
prime or `k` is a Fermat number `2 ^ (2 ^ m) + 1` if and only if
`(k - 1) ^ (2 ^ k - 2) ≡ 1 (mod (2 ^ k - 1) * k ^ 2)`; and, for `p` prime, the same
equivalence holds modulo `2 ^ p - 1`. The third conjecture on that page, about least prime
factors of `2 ^ k - 1`, is not stated here.
-/

namespace OMA.S_oeis_a000043

/-- For `k > 1`: `2 ^ k - 1` is prime, or `k` is a Fermat number `2 ^ (2 ^ m) + 1`, if and only if
`(k - 1) ^ (2 ^ k - 2) ≡ 1 (mod (2 ^ k - 1) * k ^ 2)`; and for `p` prime the analogous statement
holds modulo `2 ^ p - 1`. -/
theorem main :
    (∀ k : ℕ, 1 < k →
      (((2 ^ k - 1).Prime ∨ ∃ m : ℕ, k = 2 ^ (2 ^ m) + 1) ↔
        (k - 1) ^ (2 ^ k - 2) ≡ 1 [MOD (2 ^ k - 1) * k ^ 2])) ∧
    (∀ p : ℕ, p.Prime →
      (((2 ^ p - 1).Prime ∨ ∃ m : ℕ, p = 2 ^ (2 ^ m) + 1) ↔
        (p - 1) ^ (2 ^ p - 2) ≡ 1 [MOD 2 ^ p - 1])) := by
  sorry

end OMA.S_oeis_a000043
