import OMAReductions.R_Erdos10_erdos_10_variants_gallagher_R1_H2_R1
import Mathlib

/-! Expand the square. Diagonal terms are at most M^2 each. For an off-diagonal pair with
shifts a <= b, the terms with j >= b are v(i + (b - a)) v(i) for i = j - b < N - b, which is a
part of the nonnegative sum over i < N. -/

open Finset Filter Real
open scoped Classical

theorem OMA.solution : OMA.R_Erdos10_erdos_10_variants_gallagher_R1_H2_R1.H2 := by
  intro v s N Q M hv hM hvM
  have key : ∀ a b : ℕ, a ≤ b →
      ∑ j ∈ range N, (if a ≤ j then v (j - a) else 0) * (if b ≤ j then v (j - b) else 0)
        ≤ ∑ j ∈ range N, v j * v (j + (b - a)) := by
    intro a b hab
    have h1 : ∀ j ∈ range N,
        (if a ≤ j then v (j - a) else 0) * (if b ≤ j then v (j - b) else 0)
          = if b ≤ j then v (j - b) * v (j - b + (b - a)) else 0 := by
      intro j _
      by_cases hb : b ≤ j
      · rw [if_pos (le_trans hab hb), if_pos hb, if_pos hb]
        have : j - a = j - b + (b - a) := by omega
        rw [this, mul_comm]
      · rw [if_neg hb, if_neg hb, mul_zero]
    rw [Finset.sum_congr rfl h1, ← Finset.sum_filter]
    calc ∑ j ∈ (range N).filter (fun j => b ≤ j), v (j - b) * v (j - b + (b - a))
        = ∑ i ∈ range (N - b), v i * v (i + (b - a)) := by
          apply Finset.sum_nbij' (fun j => j - b) (fun i => i + b)
          · intro j hj
            simp only [Finset.mem_filter, Finset.mem_range] at hj ⊢
            omega
          · intro i hi
            simp only [Finset.mem_filter, Finset.mem_range] at hi ⊢
            omega
          · intro j hj
            simp only [Finset.mem_filter, Finset.mem_range] at hj
            omega
          · intro i _
            simp
          · intro j _
            rfl
      _ ≤ ∑ i ∈ range N, v i * v (i + (b - a)) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · exact Finset.range_mono (Nat.sub_le N b)
          · intro i _ _
            exact mul_nonneg (hv _) (hv _)
  have pair : ∀ a b : ℕ,
      ∑ j ∈ range N, (if a ≤ j then v (j - a) else 0) * (if b ≤ j then v (j - b) else 0)
        ≤ ∑ j ∈ range N, v j * v (j + Nat.dist a b) := by
    intro a b
    rcases le_total a b with hab | hab
    · have : Nat.dist a b = b - a := by unfold Nat.dist; omega
      rw [this]
      exact key a b hab
    · have : Nat.dist a b = a - b := by unfold Nat.dist; omega
      rw [this]
      calc _ = ∑ j ∈ range N,
            (if b ≤ j then v (j - b) else 0) * (if a ≤ j then v (j - a) else 0) :=
            Finset.sum_congr rfl fun j _ => mul_comm _ _
        _ ≤ _ := key b a hab
  have hsq : ∀ j, (∑ t ∈ Q, (if s t ≤ j then v (j - s t) else 0)) ^ 2
      = ∑ t ∈ Q, (if s t ≤ j then v (j - s t) else 0) ^ 2 +
        ∑ t ∈ Q, ∑ u ∈ Q.erase t,
          (if s t ≤ j then v (j - s t) else 0) * (if s u ≤ j then v (j - s u) else 0) := by
    intro j
    rw [sq, Finset.sum_mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun t ht => ?_
    rw [← Finset.add_sum_erase Q _ ht, sq]
  have hdiag : ∀ j ∈ range N, ∀ t ∈ Q, (if s t ≤ j then v (j - s t) else 0) ^ 2 ≤ M ^ 2 := by
    intro j hj t _
    rw [Finset.mem_range] at hj
    split_ifs
    · exact pow_le_pow_left₀ (hv _) (hvM _ (by omega)) 2
    · simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
      exact sq_nonneg M
  calc ∑ j ∈ range N, (∑ t ∈ Q, if s t ≤ j then v (j - s t) else 0) ^ 2
      = ∑ j ∈ range N, ∑ t ∈ Q, (if s t ≤ j then v (j - s t) else 0) ^ 2 +
        ∑ t ∈ Q, ∑ u ∈ Q.erase t, ∑ j ∈ range N,
          (if s t ≤ j then v (j - s t) else 0) * (if s u ≤ j then v (j - s u) else 0) := by
        rw [Finset.sum_congr rfl (fun j _ => hsq j), Finset.sum_add_distrib]
        congr 1
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun t _ => ?_
        rw [Finset.sum_comm]
    _ ≤ ∑ j ∈ range N, ∑ t ∈ Q, M ^ 2 +
        ∑ t ∈ Q, ∑ u ∈ Q.erase t, ∑ j ∈ range N, v j * v (j + Nat.dist (s t) (s u)) := by
        apply add_le_add
        · exact Finset.sum_le_sum fun j hj => Finset.sum_le_sum fun t ht => hdiag j hj t ht
        · exact Finset.sum_le_sum fun t _ => Finset.sum_le_sum fun u _ => pair (s t) (s u)
    _ = N * Q.card * M ^ 2 +
        ∑ t ∈ Q, ∑ u ∈ Q.erase t, ∑ j ∈ range N, v j * v (j + Nat.dist (s t) (s u)) := by
        rw [Finset.sum_const, Finset.sum_const, Finset.card_range, nsmul_eq_mul, nsmul_eq_mul]
        ring
