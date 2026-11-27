import Mathlib

/-!
# A199331: Number of ordered ways of writing n as the sum of two semiprimes

Source: https://oeis.org/A199331
Credit: @niclorusso

Conjecture (in the comments of A199331): Only the integers 1, 2, 3, 4, 5, 6, 7, 9, 11, 17, 22, 33
(A072966) cannot be partitioned into a set of two semiprimes.

Conventions:
* A semiprime is a product p * q of two primes, not necessarily distinct (A001358: 4, 6, 9, 10, ...).
* "partitioned into two semiprimes" means n = a + b with a and b semiprimes; a = b is allowed
  (for instance 8 = 4 + 4, and 8 is not in the list A072966).
* n ranges over the positive integers (offset 1).
* "Only ... cannot" is stated as an equivalence: a positive integer n is not a sum of two semiprimes
  if and only if n is one of the twelve listed numbers.
-/

namespace OMA.S_oeis_a199331

/-- `n` is a semiprime: the product of two (not necessarily distinct) primes. -/
def IsSemiprime (n : ℕ) : Prop :=
  ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p * q = n

/-- The conjecture on A199331: the positive integers that are not a sum of two semiprimes are
exactly `1, 2, 3, 4, 5, 6, 7, 9, 11, 17, 22, 33`. -/
theorem main : ∀ n : ℕ, 1 ≤ n →
    ((¬ ∃ a b : ℕ, IsSemiprime a ∧ IsSemiprime b ∧ a + b = n) ↔
      n ∈ ({1, 2, 3, 4, 5, 6, 7, 9, 11, 17, 22, 33} : Finset ℕ)) := by
  sorry

end OMA.S_oeis_a199331
