import Mathlib

/-!
# A337951: a(n) = 4^(n*(n-1)/2) + 4^(n*(n+1)/2) for n > 0, with a(0) = 1

Source: https://oeis.org/A337951
Credit: @xor2k

Formalizes the OEIS A337951 conjecture (offset 0):
a(2*n+1) = 0 (mod 5), a(4*n+2) = 3 (mod 5), a(4*n+4) = 2 (mod 5), for n >= 0.

Conventions: the sequence is indexed from `0` as in OEIS, with the special value `a 0 = 1`
(the closed formula would give `2` at `n = 0`). The exponents `n*(n-1)/2` and `n*(n+1)/2` are
triangular numbers, so the floor division `/` on `ℕ` is exact; for `n > 0` the truncated
subtraction `n - 1` is the usual one. Congruences mod 5 are written with `Nat.ModEq`.
All three congruences are stated, as a conjunction, for every `n : ℕ`.
-/

namespace OMA.S_oeis_a337951

/-- `a(n) = 4^(n*(n-1)/2) + 4^(n*(n+1)/2)` for `n > 0`, with `a(0) = 1`. -/
def a (n : ℕ) : ℕ :=
  if n = 0 then 1 else 4 ^ (n * (n - 1) / 2) + 4 ^ (n * (n + 1) / 2)

/-- For every `n ≥ 0`: `a(2n+1) ≡ 0`, `a(4n+2) ≡ 3` and `a(4n+4) ≡ 2 (mod 5)`. -/
theorem main :
    ∀ n : ℕ, a (2 * n + 1) ≡ 0 [MOD 5] ∧ a (4 * n + 2) ≡ 3 [MOD 5] ∧
      a (4 * n + 4) ≡ 2 [MOD 5] := by
  sorry

end OMA.S_oeis_a337951
