import Mathlib

/-!
# A257231: a(n) = n^2 mod p where p is the least prime greater than n

Source: https://oeis.org/A257231
Credit: @niclorusso

Conjecture (in the comments of A257231): a(n) is always a positive square, except for the terms
5, 7, 69, 42 and 17 given by n = 7, 23, 113, 114, and 115 respectively.

Conventions:
* The sequence has offset 1: a(n) = n^2 mod p for n >= 1, where p is the least prime greater than n
  and "mod" is the least nonnegative residue (`%`).
* A positive square is a number m > 0 with `IsSquare m`.
* The conjecture is stated as an equivalence: for n >= 1, a(n) is a positive square if and only if
  n is not one of 7, 23, 113, 114, 115 (the five exceptional terms 5, 7, 69, 42, 17 are not squares).
-/

namespace OMA.S_oeis_a257231

/-- The least prime greater than `n`. -/
def nextPrime (n : ℕ) : ℕ := Nat.find (Nat.exists_infinite_primes (n + 1))

/-- A257231: `a n = n^2 mod p` with `p` the least prime greater than `n`. -/
def a (n : ℕ) : ℕ := n ^ 2 % nextPrime n

/-- The conjecture on A257231: for `n >= 1`, `a n` is a positive square unless `n` is one of
`7, 23, 113, 114, 115`. -/
theorem main : ∀ n : ℕ, 1 ≤ n →
    ((0 < a n ∧ IsSquare (a n)) ↔ n ∉ ({7, 23, 113, 114, 115} : Finset ℕ)) := by
  sorry

end OMA.S_oeis_a257231
