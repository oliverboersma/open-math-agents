import Mathlib

/-!
# A236102: Numbers whose divisors are partition numbers

Source: https://oeis.org/A236102
Credit: @niclorusso

Conjecture (in the comments of A236102): the only composite numbers in this sequence are 15, 22,
and 77.

Conventions:
* The partition numbers are p(m) = the number of partitions of m (A000041: 1, 1, 2, 3, 5, 7, 11,
  15, 22, ...), here `Fintype.card (Nat.Partition m)`.
* n is a term when every positive divisor of n (`Nat.divisors n`) is a partition number.
* A composite number is a natural number n > 1 that is not prime.
* "the only composite numbers" is stated as a set equality.
-/

namespace OMA.S_oeis_a236102

/-- `x` is a partition number: `x = p(m)` for some `m`. -/
def IsPartitionNumber (x : ℕ) : Prop :=
  ∃ m : ℕ, Fintype.card (Nat.Partition m) = x

/-- `n` is a term of A236102: all divisors of `n` are partition numbers. -/
def IsTerm (n : ℕ) : Prop :=
  ∀ d ∈ n.divisors, IsPartitionNumber d

/-- The conjecture on A236102: the composite terms are exactly `15`, `22` and `77`. -/
theorem main : {n : ℕ | 1 < n ∧ ¬ n.Prime ∧ IsTerm n} = {15, 22, 77} := by
  sorry

end OMA.S_oeis_a236102
