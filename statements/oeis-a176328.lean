import Mathlib

/-!
# Odd-index numerators in OEIS A176328

Source: https://oeis.org/A176328
Source text: https://github.com/oeis/oeisdata/blob/main/seq/A176/A176328.seq
Credit: @Heart-galaxy

The source conjectures that a(2*n+1) = -2*n-1 for every nonnegative integer n.
Here a is defined by Peter Luschny's exact formula from June 17, 2012:
a(n) = numerator((-1)^n * (B_n(1) + B_n(2)) / 2), where B_n is the
Bernoulli polynomial. The numerator is that of the reduced rational number.

Sela Fried reports the conjecture proved on December 21, 2025:
https://oeis.org/A176328/a176328.pdf
This formalization states that known result and does not claim a new
resolution of an open problem.
-/

namespace OMA.S_oeis_a176328

/-- OEIS A176328, using Luschny's Bernoulli-polynomial formula. -/
noncomputable def a (n : ℕ) : ℤ :=
  (((-1 : ℚ) ^ n *
    ((Polynomial.bernoulli n).eval 1 + (Polynomial.bernoulli n).eval 2) / 2)).num

/-- The numerator at every odd index, including index one. -/
theorem main : ∀ n : ℕ, a (2 * n + 1) = -(2 * n + 1 : ℤ) := by
  sorry

end OMA.S_oeis_a176328
