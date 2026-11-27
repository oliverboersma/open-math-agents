import Mathlib

/-!
# A401895: Number of distinct decimal digits in the product of n and its digit reversal

Source: https://oeis.org/A401895
Credit: @niclorusso

Conjecture (in the comments of A401895): For 1 <= n < 10^6, a(n) = 1 only for n = 1, 2, 3. It is
conjectured that these are the only such indices.

Conventions:
* The sequence has offset 1. R(n) is the decimal digit reversal of n:
  `Nat.ofDigits 10 (Nat.digits 10 n).reverse` (`Nat.digits 10 n` lists the decimal digits of n,
  least significant first).
* a(n) is the number of distinct decimal digits of n * R(n): `(Nat.digits 10 (n * R n)).toFinset.card`.
* "these are the only such indices" is stated as: for n >= 1, a(n) = 1 if and only if n is 1, 2
  or 3.
-/

namespace OMA.S_oeis_a401895

/-- The decimal digit reversal of `n`. -/
def R (n : ℕ) : ℕ := Nat.ofDigits 10 (Nat.digits 10 n).reverse

/-- A401895: the number of distinct decimal digits of `n * R(n)`. -/
def a (n : ℕ) : ℕ := (Nat.digits 10 (n * R n)).toFinset.card

/-- The conjecture on A401895: for `n >= 1`, `a n = 1` exactly for `n = 1, 2, 3`. -/
theorem main : ∀ n : ℕ, 1 ≤ n → (a n = 1 ↔ n = 1 ∨ n = 2 ∨ n = 3) := by
  sorry

end OMA.S_oeis_a401895
