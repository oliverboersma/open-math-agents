import Mathlib

/-!
# A056828: Numbers that are not the sum of at most three powerful numbers (A001694).

Source: https://oeis.org/A056828
Credit: @divmxnd0x

A powerful number (A001694) is a positive integer `m` such that `p^2 ∣ m` for every prime `p ∣ m`
(so `1` is powerful).

Heath-Brown proved that the sequence is finite. Conjecture (Mollin and Walsh): there are no
further terms, i.e. 7, 15, 23, 87, 111, 119 are the only positive integers that are not the sum of
at most three powerful numbers (no other terms below 4 * 10^7).

Formalization notes:
* "A sum of at most three powerful numbers" is the sum of a list of length at most 3 whose entries
  are powerful; the sequence lists positive integers, so `n ≥ 1`.
* Below 2000 the positive integers that are not such a sum are exactly 7, 15, 23, 87, 111, 119.
-/

namespace OMA.S_oeis_a056828

/-- `m` is powerful: positive, and divisible by `p^2` for each prime `p` dividing it. -/
def IsPowerful (m : ℕ) : Prop :=
  0 < m ∧ ∀ p : ℕ, p.Prime → p ∣ m → p ^ 2 ∣ m

/-- The Mollin–Walsh conjecture: 7, 15, 23, 87, 111, 119 are the only positive integers that are
not a sum of at most three powerful numbers. -/
theorem main :
    {n : ℕ | 1 ≤ n ∧ ¬ ∃ s : List ℕ, s.length ≤ 3 ∧ (∀ x ∈ s, IsPowerful x) ∧ s.sum = n} =
      {7, 15, 23, 87, 111, 119} := by
  sorry

end OMA.S_oeis_a056828
