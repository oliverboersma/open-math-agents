import Mathlib

/-!
# A120740: Numbers n such that n = Sum_digits[k*abs(n-k)] for some k>=0.

Source: https://oeis.org/A120740
Credit: @surrenderyourfreedom

Formalizes the conjecture of Colin Barker (Apr 10 2012) recorded in A120740:
`a(n) = (18*n - (-1)^n - 35)/4` for `n > 2`, `a(n) = a(n-1) + a(n-2) - a(n-3)` for `n > 5`, and
the g.f. is `x^2*(4 + x + 4*x^3)/((1 - x)^2*(1 + x))`.

The sequence has offset 1: `a 1 = 0, a 2 = 4, a 3 = 5, a 4 = 9, ...` is the increasing
enumeration of the numbers `n` such that `n` is the sum of the decimal digits of `k * |n - k|`
for some integer `k >= 0`. The value `a 0 = 0` is a placeholder outside the OEIS range; it is also
the constant coefficient required by the g.f. (which is divisible by `x^2`).
-/

namespace OMA.S_oeis_a120740

open PowerSeries

/-- `n` is a term of A120740: `n` equals the sum of the decimal digits of `k * |n - k|` for some
natural number `k`. -/
def IsTerm (n : ℕ) : Prop :=
  ∃ k : ℕ, (Nat.digits 10 (k * Int.natAbs ((n : ℤ) - k))).sum = n

/-- `a n` for `n ≥ 1` is the `n`-th smallest term (offset 1, as in the OEIS); `a 0 = 0`. -/
noncomputable def a (n : ℕ) : ℕ :=
  if n = 0 then 0 else Nat.nth IsTerm (n - 1)

/-- Barker's conjecture: the closed form for `n > 2`, the recurrence for `n > 5`, and the
generating function `x^2*(4 + x + 4*x^3)/((1 - x)^2*(1 + x))`, stated with the denominator
cleared. -/
theorem main :
    (∀ n : ℕ, 2 < n → (a n : ℤ) = (18 * n - (-1) ^ n - 35) / 4) ∧
    (∀ n : ℕ, 5 < n → (a n : ℤ) = a (n - 1) + a (n - 2) - a (n - 3)) ∧
    PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - X) ^ 2 * (1 + X)) =
      X ^ 2 * (4 + X + 4 * X ^ 3) := by
  sorry

end OMA.S_oeis_a120740
