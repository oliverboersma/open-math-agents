import Mathlib

/-!
# A016789: a(n) = 3*n + 2.

Source: https://oeis.org/A016789
Credit: @ShoQo

Conjecture (Gary Detlefs, Mar 08 2010): "It appears that a(n) is the set of all nonnegative
integers y such that y^3 = k*n + 2 for some integer k." (Sela Fried, Oct 27 2025: "The above
conjecture is true - immediate with the special case of Fermat's little theorem:
y^3 == y (mod 3).")

Formalization notes:
* The "k*n" in the comment is read as k*3: the proof cited (y^3 ≡ y (mod 3)) is about cubes
  that are 2 mod 3, and with n the sequence index the condition would not describe a set.
  So the claim is: a nonnegative integer y is a term (y = 3n + 2 for some n ≥ 0) if and only if
  y^3 = 3k + 2 for some integer k.
-/

namespace OMA.S_oeis_a016789

/-- a(n) = 3n + 2. -/
def a (n : ℕ) : ℕ := 3 * n + 2

theorem main : ∀ y : ℕ, (∃ n : ℕ, a n = y) ↔ ∃ k : ℤ, (y : ℤ) ^ 3 = 3 * k + 2 := by
  sorry

end OMA.S_oeis_a016789
