import Mathlib

/-!
# A004432: Numbers that are the sum of 3 distinct nonzero squares.

Source: https://oeis.org/A004432
Credit: @ShoQo

Conjecture (Jeffrey Shallit, Jan 15 2017): a number n is a sum of 3 squares, but not a sum of
3 distinct nonzero squares, if and only if it is of the form 4^j*s, where j >= 0 and s in
{1, 2, 3, 5, 6, 9, 10, 11, 13, 17, 18, 19, 22, 25, 27, 33, 34, 37, 43, 51, 57, 58, 67, 73, 82,
85, 97, 99, 102, 123, 130, 163, 177, 187, 193, 267, 627, 697}.

Formalization notes:
* "Sum of 3 squares" allows zero squares (A000378); "sum of 3 distinct nonzero squares" is
  membership in this sequence, A004432.
* The source's parenthetical "(i.e., is in A004432 but not A000408)" does not match its own
  sentence (A000408 is the sums of 3 nonzero squares), so we follow the sentence itself, which
  is the version that agrees with the data: checked for all 1 <= n <= 200000.
* `n` ranges over positive integers: `n = 0` is a sum of three squares but not of the form
  `4^j * s` with `s` in the list, so the sentence is about positive numbers.
-/

namespace OMA.S_oeis_a004432

/-- `n` is a sum of three squares of natural numbers (zeros allowed). -/
def IsSumOfThreeSquares (n : ℕ) : Prop :=
  ∃ a b c : ℕ, n = a ^ 2 + b ^ 2 + c ^ 2

/-- `n` is a sum of three distinct nonzero squares (membership in A004432). -/
def IsSumOfThreeDistinctNonzeroSquares (n : ℕ) : Prop :=
  ∃ a b c : ℕ, 0 < a ∧ a < b ∧ b < c ∧ n = a ^ 2 + b ^ 2 + c ^ 2

/-- Shallit's finite list of exceptional cores. -/
def exceptions : Finset ℕ :=
  {1, 2, 3, 5, 6, 9, 10, 11, 13, 17, 18, 19, 22, 25, 27, 33, 34, 37, 43, 51, 57, 58, 67, 73, 82,
    85, 97, 99, 102, 123, 130, 163, 177, 187, 193, 267, 627, 697}

theorem main :
    ∀ n : ℕ, 0 < n →
      ((IsSumOfThreeSquares n ∧ ¬ IsSumOfThreeDistinctNonzeroSquares n) ↔
        ∃ j s : ℕ, s ∈ exceptions ∧ n = 4 ^ j * s) := by
  sorry

end OMA.S_oeis_a004432
