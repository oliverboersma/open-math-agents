import Mathlib

/-!
# A233398: n^n mod 3^n.

Source: https://oeis.org/A233398
Credit: @marcelopierry

Conjecture (Harvey P. Dale, Jan 10 2025, in the comments of A233398): a(x) equals zero for every
x that is a multiple of 3.

Conventions:
* The sequence has offset 0: a(n) = n^n mod 3^n, the least nonnegative residue (`%`). In Lean
  `0 ^ 0 = 1` and `1 % 1 = 0`, so a(0) = 0, matching the data 0, 1, 4, 0, 13, 209, 0, ...
* x ranges over all natural numbers (0 is a multiple of 3).
-/

namespace OMA.S_oeis_a233398

/-- A233398(n) = n^n mod 3^n. -/
def a (n : ℕ) : ℕ := n ^ n % 3 ^ n

/-- Dale's conjecture: a(x) = 0 whenever 3 divides x. -/
theorem main : ∀ x : ℕ, 3 ∣ x → a x = 0 := by
  sorry

end OMA.S_oeis_a233398
