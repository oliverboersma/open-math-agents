import Mathlib

/-!
# A274010: Boris Stechkin function: a(n) is the number of m with 2 <= m <= n and floor(n(m-1)/m) divisible by m-1.

Source: https://oeis.org/A274010
Credit: @rorcores

The entry (offset 0, data 0, 0, 1, 2, 3, 3, 4, 4, 4, 5, 5, 4, 6, 6, 4, 6, 7, 5, 6, 6, ...) records
in its FORMULA section:

  Conjecture: a(n) = tau(n) + tau(n-1) - 2, for n>=2. - Ridouane Oudra, Feb 28 2020

Conventions:
* `a(n)` counts the integers `m` with `2 ≤ m ≤ n` such that `m - 1` divides `floor(n (m - 1) / m)`
  (natural-number division `/` is the floor).
* `tau(k)` is the number of positive divisors of `k` (A000005), `k.divisors.card`.
* The identity is stated in `ℤ`, so the subtraction of `2` is not truncated.
-/

namespace OMA.S_oeis_a274010

/-- The Boris Stechkin function: the number of `m` with `2 ≤ m ≤ n` such that `floor(n (m-1) / m)`
is divisible by `m - 1`. -/
def a (n : ℕ) : ℕ := ((Finset.Icc 2 n).filter fun m => (m - 1) ∣ n * (m - 1) / m).card

/-- Oudra's conjecture: `a(n) = tau(n) + tau(n-1) - 2` for `n ≥ 2`. -/
theorem main : ∀ n : ℕ, 2 ≤ n →
    (a n : ℤ) = (n.divisors.card : ℤ) + ((n - 1).divisors.card : ℤ) - 2 := by
  sorry

end OMA.S_oeis_a274010
