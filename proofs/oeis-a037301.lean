import OMAStatements.S_oeis_a037301

/-!
The numbers 4k+1 and 4k+2 share their high binary digits and have respective
suffixes 01 and 10. Their binary digit sums agree, whereas their ternary digit
sums have opposite parity. Every interval of five consecutive integers
contains such a pair.
-/

namespace EqualDigitSumRuns

open OMA.S_oeis_a037301

private theorem binary_even (k : ℕ) :
    (Nat.digits 2 (2 * k)).sum = (Nat.digits 2 k).sum := by
  rcases eq_or_ne k 0 with rfl | hk
  · rfl
  · have h := Nat.digits_add 2 (by decide) 0 k (by decide) (Or.inr hk)
    simpa only [zero_add, List.sum_cons] using congrArg List.sum h

private theorem binary_odd (k : ℕ) :
    (Nat.digits 2 (1 + 2 * k)).sum = 1 + (Nat.digits 2 k).sum := by
  rw [Nat.digits_add 2 (by decide) 1 k (by decide) (Or.inl (by decide)), List.sum_cons]

private theorem forbidden_pair (k : ℕ) :
    ¬ (equalDigitSums (4 * k + 1) ∧ equalDigitSums (4 * k + 2)) := by
  rintro ⟨h₁, h₂⟩
  have hb : (Nat.digits 2 (4 * k + 1)).sum = (Nat.digits 2 (4 * k + 2)).sum := by
    rw [show 4 * k + 1 = 1 + 2 * (2 * k) by omega,
        show 4 * k + 2 = 2 * (1 + 2 * k) by omega,
        binary_odd, binary_even, binary_even, binary_odd]
  rw [h₁, h₂] at hb
  have p := Nat.modEq_digits_sum 2 3 (by decide) (4 * k + 1)
  have q := Nat.modEq_digits_sum 2 3 (by decide) (4 * k + 2)
  unfold Nat.ModEq at p q
  omega

theorem no_five (n : ℕ) : ¬ (∀ i : ℕ, i < 5 → equalDigitSums (n + i)) := by
  intro run
  let k := (n + 2) / 4
  have start : n ≤ 4 * k + 1 := by dsimp [k]; omega
  have finish : 4 * k + 2 < n + 5 := by dsimp [k]; omega
  apply forbidden_pair k
  constructor
  · simpa only [Nat.add_sub_of_le start] using run (4 * k + 1 - n) (by omega)
  · have h : n ≤ 4 * k + 2 := by omega
    simpa only [Nat.add_sub_of_le h] using run (4 * k + 2 - n) (by omega)

end EqualDigitSumRuns

theorem OMA.solution : type_of% @OMA.S_oeis_a037301.main := by
  refine ⟨EqualDigitSumRuns.no_five, ?_⟩
  intro i hi
  unfold OMA.S_oeis_a037301.equalDigitSums
  interval_cases i <;> decide
