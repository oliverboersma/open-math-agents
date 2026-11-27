import Mathlib

/-!
# OEIS A002742: periodicity congruences for the logarithmic numbers

Source: https://oeis.org/A002742
Credit: @sntntHb

A002742: logarithmic numbers (offset 1), with e.g.f. `(2*x/(1-x^2) + log(1-x^2))*exp(-x)`
(Sean A. Irvine, listed in the entry).

Conjectures (Peter Bala, Sep 06 2022): let `k` be a positive integer.
1) for `n >= 1`, `a(n+2*k) - a(n)` is divisible by `2*k`;
2) for `n >= 1`, `a(n+2*k+1) + a(n)` is divisible by `2*k+1`.

Formalized: `2*x/(1-x^2) = Sum_{n odd} 2*x^n` and `log(1-x^2) = Sum_{n even, n >= 2} (-2/n)*x^n`,
so `G` is the power series with these coefficients over `ℚ`; `egf = G * exp(-x)` and
`a n = n! * [x^n] egf` (an integer). Divisibility of these integers by `d` is expressed as
`value = d * m` for an integer `m`. `main` is the conjunction of the two conjectures, for all
`k >= 1` and `n >= 1`.
-/

namespace OMA.S_oeis_a002742

open PowerSeries

/-- `2*x/(1-x^2) + log(1-x^2)`, coefficientwise. -/
noncomputable def G : PowerSeries ℚ :=
  mk fun n => if n % 2 = 1 then 2 else if n = 0 then 0 else -2 / (n : ℚ)

/-- The e.g.f. `(2*x/(1-x^2) + log(1-x^2)) * exp(-x)`. -/
noncomputable def egf : PowerSeries ℚ := G * mk fun n => (-1) ^ n / (n.factorial : ℚ)

/-- `a(n) = n! * [x^n] egf`. -/
noncomputable def a (n : ℕ) : ℚ := (n.factorial : ℚ) * coeff n egf

theorem main :
    (∀ k n : ℕ, 1 ≤ k → 1 ≤ n → ∃ m : ℤ, a (n + 2 * k) - a n = (2 * k : ℚ) * m) ∧
    (∀ k n : ℕ, 1 ≤ k → 1 ≤ n → ∃ m : ℤ, a (n + 2 * k + 1) + a n = (2 * k + 1 : ℚ) * m) := by
  sorry

end OMA.S_oeis_a002742
