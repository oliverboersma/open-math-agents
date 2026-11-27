import Mathlib

/-!
# A135499: numbers with equal digit sums at odd and at even positions are multiples of 11

Source: https://oeis.org/A135499
Credit: @ivillar

A135499 (offset 1) lists the positive numbers for which Sum_digits(odd positions) =
Sum_digits(even positions) in base 10: 11, 22, 33, ..., 99, 110, 121, 132, ...
Conjecture (R. J. Mathar, Feb 10 2008): this is a subsequence of A008593, the multiples of 11.
(Later comments note that this follows from the divisibility rule for 11.)

Formalization notes.
* `Nat.digits 10 n` lists the decimal digits of n from the least significant one.
  `digitSums L` is the pair (sum of the entries of L at positions 0, 2, 4, ...,
  sum of the entries at positions 1, 3, 5, ...). Counting positions from the most significant
  digit instead only swaps the two sums, so the defining condition is the same.
* Being a term of A008593 (the numbers 11k) means being divisible by 11.
-/

namespace OMA.S_oeis_a135499

/-- (sum of entries at positions 0, 2, 4, ..., sum of entries at positions 1, 3, 5, ...). -/
def digitSums : List ℕ → ℕ × ℕ
  | [] => (0, 0)
  | d :: l => (d + (digitSums l).2, (digitSums l).1)

/-- n is a term of A135499: n > 0 and its two alternate decimal digit sums are equal. -/
def IsTerm (n : ℕ) : Prop :=
  0 < n ∧ (digitSums (Nat.digits 10 n)).1 = (digitSums (Nat.digits 10 n)).2

/-- Mathar's conjecture: every term of A135499 is a multiple of 11 (a term of A008593). -/
theorem main : ∀ n : ℕ, IsTerm n → 11 ∣ n := by
  sorry

end OMA.S_oeis_a135499
