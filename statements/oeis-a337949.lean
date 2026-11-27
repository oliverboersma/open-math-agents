import Mathlib

/-!
# A337949: a(n) = 2^(n*(n-1)/2) + 2^(n*(n+1)/2) for n > 0, with a(0) = 1

Source: https://oeis.org/A337949
Credit: @xor2k

Formalizes the OEIS A337949 conjecture (offset 0):
a(2*n+1) = 0 (mod 3), a(4*n+2) = 1 (mod 3), a(4*n+4) = 2 (mod 3), for n >= 0.

Conventions: the sequence is indexed by `n : ℕ` starting at `0`, with `a 0 = 1` as in OEIS.
For `n > 0` the exponents `n*(n-1)/2` and `n*(n+1)/2` are exact natural numbers
(a product of consecutive integers is even), so natural subtraction and floor division
agree with the OEIS formula. The three congruences are stated as `% 3` equalities and
asserted jointly for every `n : ℕ`.
-/

namespace OMA.S_oeis_a337949

/-- `a(0) = 1` and `a(n) = 2^(n*(n-1)/2) + 2^(n*(n+1)/2)` for `n > 0`. -/
def a (n : ℕ) : ℕ :=
  if n = 0 then 1 else 2 ^ (n * (n - 1) / 2) + 2 ^ (n * (n + 1) / 2)

/-- For every `n ≥ 0`: `a(2n+1) ≡ 0`, `a(4n+2) ≡ 1` and `a(4n+4) ≡ 2 (mod 3)`. -/
theorem main :
    ∀ n : ℕ, a (2 * n + 1) % 3 = 0 ∧ a (4 * n + 2) % 3 = 1 ∧ a (4 * n + 4) % 3 = 2 := by
  sorry

end OMA.S_oeis_a337949
