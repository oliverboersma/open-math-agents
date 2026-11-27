import OMAStatements.S_oeis_a000579

open Finset

namespace OMA.S_oeis_a000579

private theorem sum_shifted_choose (n a b : ℕ) (hab : a ≤ b) :
    ∑ j ∈ range (n + 1), (j + a).choose b = (n + a + 1).choose (b + 1) := by
  induction n with
  | zero =>
    simp [Nat.choose_succ_succ', Nat.choose_eq_zero_of_lt (show a < b + 1 by omega)]
  | succ n ih =>
    rw [sum_range_succ, ih, Nat.succ_add]
    exact (Nat.add_comm _ _).trans (Nat.choose_succ_succ' (n + a + 1) b).symm

/-- Summing with weight x takes two successive partial sums of a binomial coefficient. -/
private theorem weighted_choose (n r : ℕ) :
    ∑ x ∈ range (n + 1), x * (n - x + r).choose (2 * r) =
      (n + r + 1).choose (2 * r + 2) := by
  induction n with
  | zero =>
    simp [Nat.choose_eq_zero_of_lt (show r + 1 < 2 * r + 2 by omega)]
  | succ n ih =>
    rw [sum_range_succ']
    simp only [zero_mul, add_zero, Nat.succ_sub_succ_eq_sub, add_one_mul, sum_add_distrib, ih]
    have h := sum_range_reflect (fun i : ℕ => (i + r).choose (2 * r)) (n + 1)
    simp only [Nat.add_sub_cancel] at h
    rw [h, sum_shifted_choose n r (2 * r) (by omega)]
    rw [Nat.succ_add]
    exact (Nat.add_comm _ _).trans (Nat.choose_succ_succ' (n + r + 1) (2 * r + 1)).symm

/-- Weight of the residual simplex after choosing indices whose sum is s. -/
private def coeff (n s r : ℕ) : ℕ :=
  if s ≤ n then (n - s + r).choose (2 * r) else 0

private theorem sum_coeff (n s r : ℕ) :
    ∑ x ∈ range (n + 1), x * coeff n (s + x) r = coeff n s (r + 1) := by
  by_cases hs : s ≤ n
  · calc
      _ = ∑ x ∈ range (n - s + 1), x * coeff n (s + x) r := by
        symm
        apply sum_subset (range_mono (by omega))
        intro x hx hx'
        simp only [mem_range] at hx hx'
        simp [coeff, show ¬ s + x ≤ n by omega]
      _ = ∑ x ∈ range (n - s + 1), x * (n - s - x + r).choose (2 * r) := by
        apply sum_congr rfl
        intro x hx
        have hx' := mem_range.mp hx
        simp [coeff, show s + x ≤ n by omega, Nat.sub_sub]
      _ = _ := by
        rw [weighted_choose]
        simp [coeff, hs, Nat.mul_add, Nat.add_assoc]
  · rw [sum_eq_zero]
    · simp [coeff, hs]
    · intro x hx
      simp [coeff, show ¬ s + x ≤ n by omega]

private theorem sum_last (n k l : ℕ) :
    (∑ m ∈ range (n + 1), if k + l + m ≤ n then k * l * m else 0) =
      k * l * coeff n (k + l) 1 := by
  rw [← sum_coeff n (k + l) 0, mul_sum]
  apply sum_congr rfl
  intro m hm
  by_cases h : k + l + m ≤ n <;> simp [coeff, h]

end OMA.S_oeis_a000579

open OMA.S_oeis_a000579

theorem OMA.solution : type_of% @OMA.S_oeis_a000579.main := by
  intro n
  unfold weightedTripleSimplexSum
  simp_rw [sum_last, mul_assoc, ← mul_sum, sum_coeff]
  simpa [coeff] using (sum_coeff n 0 2).symm
