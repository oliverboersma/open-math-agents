import Mathlib

/-!
# OEIS A035378: congruences mod 5 for the expansion of Sum_k Product_{j<=k} (1-x^j) at x = -1

Source: https://oeis.org/A035378
Credit: @sntntHb

A035378: coefficients in the expansion of `Sum_{k>=0} Product_{j=1..k} (1-x^j)` about `x = -1`.

Conjectures (Peter Bala, Jun 19 2023): `a(5*n+3) == 0 (mod 5)`, `a(5*n+4) == 0 (mod 5)` and
`a(5*n+2) - 2*a(5*n+1) == 0 (mod 5)`.

Formalized: write `x = y - 1`, so `a(n)` is the coefficient of `y^n`. The factor `1 - x^j`
vanishes at `x = -1` exactly when `j` is even (a simple zero), so the `k`-th product is divisible
by `y^(k/2)` and only `k <= 2n+1` contribute to the coefficient of `y^n`. Hence `a n` is the
coefficient of `Y^n` in the integer polynomial `Sum_{k=0..2n+1} Product_{j=1..k} (1 - (Y-1)^j)`.
`main` states the three congruences for every `n >= 0`.
-/

namespace OMA.S_oeis_a035378

open Polynomial

/-- `a(n)`: coefficient of `(x+1)^n` in `Sum_{k>=0} Product_{j=1..k} (1-x^j)`. -/
noncomputable def a (n : ℕ) : ℤ :=
  (∑ k ∈ Finset.range (2 * n + 2), ∏ j ∈ Finset.Icc 1 k, (1 - (X - 1) ^ j : ℤ[X])).coeff n

theorem main :
    ∀ n : ℕ, a (5 * n + 3) ≡ 0 [ZMOD 5] ∧ a (5 * n + 4) ≡ 0 [ZMOD 5] ∧
      a (5 * n + 2) - 2 * a (5 * n + 1) ≡ 0 [ZMOD 5] := by
  sorry

end OMA.S_oeis_a035378
