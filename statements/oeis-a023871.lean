import Mathlib

/-!
# OEIS A023871: a supercongruence for [x^n] (Product (1 - x^k)^(-k^2))^n

Source: https://oeis.org/A023871
Credit: @sntntHb

A023871: expansion of `Product_{k>=1} (1 - x^k)^(-k^2)`.

Peter Bala (Feb 02 2025): let `A(x) = Product_{k >= 1} (1 - x^k)^(-k^2)`. The sequence defined by
`u(n) := [x^n] A(x)^n` is conjectured to satisfy the supercongruences
`u(n*p^r) == u(n*p^(r-1)) (mod p^(3*r))` for all primes `p >= 7` and all positive integers `n`
and `r`.

Formalized: factors with `k > n` do not affect the coefficient of `x^n`, so `u n` is the
coefficient of `X^n` in `(Product_{k=1..n} ((1 - X^k)^(-1))^(k^2))^n` in `ℚ[[X]]` (an integer).
The congruence is expressed as `u (n*p^r) - u (n*p^(r-1)) = p^(3*r) * m` for an integer `m`, for
every prime `p >= 7` and all `n, r >= 1`.
-/

namespace OMA.S_oeis_a023871

open PowerSeries

/-- `Product_{k=1..N} (1 - X^k)^(-k^2)`, which agrees with `A(x)` up to degree `N`. -/
noncomputable def A (N : ℕ) : PowerSeries ℚ :=
  ∏ k ∈ Finset.Icc 1 N, ((1 - X ^ k : PowerSeries ℚ)⁻¹) ^ (k ^ 2)

/-- `u(n) = [x^n] A(x)^n`. -/
noncomputable def u (n : ℕ) : ℚ := coeff n (A n ^ n)

theorem main :
    ∀ p n r : ℕ, p.Prime → 7 ≤ p → 0 < n → 0 < r →
      ∃ m : ℤ, u (n * p ^ r) - u (n * p ^ (r - 1)) = (p : ℚ) ^ (3 * r) * m := by
  sorry

end OMA.S_oeis_a023871
