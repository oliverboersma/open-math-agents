import Mathlib

/-!
# A241884: Numbers n such that n - n^2/k^2 is not prime for all k < n.

Source: https://oeis.org/A241884
Credit: @divmxnd0x

Conjecture (Vincenzo Librandi, Jul 16 2016, stated in A241884): the terms are the numbers `n` such
that `n - 1` is not a prime number.

Formalization notes:
* The data and the PARI and Maple programs of A241884 test `n - (n/k)^2` for every divisor `k` of
  `n` (only then is `n^2/k^2` an integer), including `k = n` (which gives `n - 1`); the sequence is
  defined here accordingly: `n` is a term iff `n - t^2` is not prime for every divisor `t` of `n`
  (`t = n/k` runs over the divisors of `n` as `k` does).
* `n - t^2` is taken in `ℤ` (it is negative when `t^2 > n`, and then not prime).
* The terms are positive integers, so the conjecture is stated for `n ≥ 1`.
* With this definition the terms up to 50 are 1, 2, 5, 7, 9, 10, 11, 13, 15, 16, 17, 19, 21, 22, 23,
  25, 26, 27, 28, 29, 31, 33, 34, 35, 36, 37, 39, 40, 41, 43, 45, 46, 47, 49, 50, matching the data of
  A241884.
-/

namespace OMA.S_oeis_a241884

/-- `n` is a term of A241884: `n - t^2` is not prime for any divisor `t` of `n`. -/
def IsTerm (n : ℕ) : Prop :=
  ∀ t ∈ n.divisors, ¬ ∃ p : ℕ, p.Prime ∧ (n : ℤ) - (t : ℤ) ^ 2 = p

/-- Librandi's conjecture: for `n ≥ 1`, `n` is a term iff `n - 1` is not prime. -/
theorem main : ∀ n : ℕ, 1 ≤ n → (IsTerm n ↔ ¬ (n - 1).Prime) := by
  sorry

end OMA.S_oeis_a241884
