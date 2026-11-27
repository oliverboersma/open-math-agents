import Mathlib

/-!
# OEIS A092765: stronger Gauss congruences for next-nearest-neighbour walks returning to 0

Source: https://oeis.org/A092765
Credit: @sntntHb

A092765: consider the 1-D random walk with jumps to next-nearest neighbors; `a(n)` is the number
of paths of length `n` ending at the origin.

Conjecture (Peter Bala): the stronger congruences `a(n*p^k) == a(n*p^(k-1)) ( mod p^(2*k) )` hold
for any prime `p`, except `p = 3`, and positive integers `n` and `k`.

Formalized: the steps are `-2, -1, +1, +2`, so `a(n)` is the constant term of
`(x^-2 + x^-1 + x + x^2)^n`, i.e. the coefficient of `x^(2n)` in `(1 + x + x^3 + x^4)^n`; this is
the definition used. `main` states the congruence modulo `p^(2*k)` for every prime `p /= 3` and
all `n, k >= 1`.
-/

namespace OMA.S_oeis_a092765

open Polynomial

/-- Number of walks of length `n` with steps in `{-2,-1,1,2}` from `0` back to `0`. -/
noncomputable def a (n : ℕ) : ℕ := ((1 + X + X ^ 3 + X ^ 4 : ℕ[X]) ^ n).coeff (2 * n)

theorem main :
    ∀ p n k : ℕ, p.Prime → p ≠ 3 → 0 < n → 0 < k →
      a (n * p ^ k) ≡ a (n * p ^ (k - 1)) [MOD p ^ (2 * k)] := by
  sorry

end OMA.S_oeis_a092765
