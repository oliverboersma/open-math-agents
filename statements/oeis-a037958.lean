import Mathlib

/-!
# A037958: a(n) = binomial(n, floor((n-8)/2)).

Source: https://oeis.org/A037958 (OEIS Foundation, CC BY-SA 4.0)
Credit: @OrangeHeadz

The OEIS entry has offset 0 and begins 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 10, 11, 66, 78, 364, ...
Its formula section contains the conjecture of R. J. Mathar (Jul 26 2015), marked there as
verified by Robert Israel (Jun 28 2018):

  -(n+9)*(n-8)*a(n) + 2*n*a(n-1) + 4*n*(n-1)*a(n-2) = 0.

Conventions.
* For `n < 8` the lower index `floor((n-8)/2)` is negative and the binomial coefficient is 0,
  as in the OEIS data. For `n ≥ 8` the lower index is the natural number `(n - 8) / 2`.
* The recurrence is stated for every `n ≥ 2`, the indices for which `a(n-1)` and `a(n-2)` are
  terms of the sequence, and as an equation in the integers.
-/

namespace OMA.S_oeis_a037958

/-- A037958 with offset 0: `a n = binomial(n, floor((n-8)/2))`, which is `0` for `n < 8`. -/
def a (n : ℕ) : ℤ := if n < 8 then 0 else (Nat.choose n ((n - 8) / 2) : ℤ)

/-- Mathar's three-term recurrence for A037958. -/
theorem main : ∀ n : ℕ, 2 ≤ n →
    -((n : ℤ) + 9) * ((n : ℤ) - 8) * a n + 2 * (n : ℤ) * a (n - 1) +
      4 * (n : ℤ) * ((n : ℤ) - 1) * a (n - 2) = 0 := by
  sorry

end OMA.S_oeis_a037958
