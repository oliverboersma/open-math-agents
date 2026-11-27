import Mathlib

/-!
# The primality criterion recorded in OEIS A000680

Source: https://oeis.org/A000680
Source text: https://github.com/oeis/oeisdata/blob/main/seq/A000/A000680.seq
Credit: @Heart-galaxy

Werner Schulte asked whether, for every positive integer n, a(n) + 2^n
is divisible by 2*n + 1 exactly when 2*n + 1 is prime, where
a(n) = (2*n)! / 2^n.

The source reports that Sela Fried proved this in 2025:
https://oeis.org/A000680/a000680.pdf
This submission supplies a Lean statement of that result; it does not
claim a new proof or a solution of an open problem.

The quotient is taken in the natural numbers, as is the OEIS sequence.
The strict positivity hypothesis and both directions of the equivalence
are retained from the source.
-/

namespace OMA.S_oeis_a000680

/-- The natural-number sequence A000680, indexed from zero. -/
def a (n : ℕ) : ℕ := Nat.factorial (2 * n) / 2 ^ n

/-- The primality criterion posed by Schulte and proved by Fried. -/
theorem main :
    ∀ n : ℕ, 0 < n → ((2 * n + 1) ∣ (a n + 2 ^ n) ↔ Nat.Prime (2 * n + 1)) := by
  sorry

end OMA.S_oeis_a000680
