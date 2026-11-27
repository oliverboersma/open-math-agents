import OMAReductions.R_Erdos36_minimum_overlap_variants_lower_white_2022_R1
import Mathlib

/-! Write y = k + t with k the floor of y. A pair with difference d contributes 1 - t when d = k,
t when d = k + 1, and 0 otherwise, so the sum is a convex combination of two overlap counts. -/

theorem OMA.solution : OMA.R_Erdos36_minimum_overlap_variants_lower_white_2022_R1.H2 := by
  intro A B y
  obtain ⟨k, hk⟩ : ∃ k : ℤ, k = ⌊y⌋ := ⟨_, rfl⟩
  have hky : (k : ℝ) ≤ y := hk ▸ Int.floor_le y
  have hyk : y < k + 1 := hk ▸ Int.lt_floor_add_one y
  have key : ∀ d : ℤ, max 0 (1 - |(d : ℝ) - y|) ≤
      (if d = k then 1 - (y - k) else 0) + (if d = k + 1 then y - k else 0) := by
    intro d
    rcases lt_trichotomy d k with h | h | h
    · have h1 : d ≠ k := by omega
      have h2 : d ≠ k + 1 := by omega
      have hd : (d : ℝ) ≤ k - 1 := by
        have : d ≤ k - 1 := by omega
        exact_mod_cast this
      rw [if_neg h1, if_neg h2, add_zero]
      refine max_le le_rfl ?_
      have : 1 ≤ |(d : ℝ) - y| := by
        rw [abs_sub_comm]; exact le_abs.mpr (Or.inl (by linarith))
      linarith
    · subst h
      have h2 : d ≠ d + 1 := by omega
      rw [if_pos rfl, if_neg h2, add_zero, abs_sub_comm, abs_of_nonneg (by linarith)]
      exact max_le (by linarith) le_rfl
    · rcases (show d = k + 1 ∨ k + 2 ≤ d by omega) with h2 | h2
      · subst h2
        have h1 : k + 1 ≠ k := by omega
        rw [if_neg h1, if_pos rfl, zero_add]
        push_cast
        rw [abs_of_nonneg (by linarith)]
        exact max_le (by linarith) (by linarith)
      · have h1 : d ≠ k := by omega
        have h3 : d ≠ k + 1 := by omega
        have hd : (k : ℝ) + 2 ≤ d := by exact_mod_cast h2
        rw [if_neg h1, if_neg h3, add_zero]
        refine max_le le_rfl ?_
        have : 1 ≤ |(d : ℝ) - y| := le_abs.mpr (Or.inl (by linarith))
        linarith
  have hbdd : BddAbove (Set.range (Erdos36.Overlap A B)) := by
    refine ⟨(A ×ˢ B).card, ?_⟩
    rintro _ ⟨j, rfl⟩
    exact Finset.card_filter_le _ _
  have hO : ∀ j, (Erdos36.Overlap A B j : ℝ) ≤ (Erdos36.MaxOverlap A B : ℝ) := fun j => by
    exact_mod_cast le_ciSup hbdd j
  have hcard : ∀ j : ℤ, (((A ×ˢ B).filter (fun p : ℤ × ℤ => p.2 - p.1 = j)).card : ℝ)
      = (Erdos36.Overlap A B (-j) : ℝ) := by
    intro j
    congr 1
    unfold Erdos36.Overlap
    congr 1
    refine Finset.filter_congr ?_
    rintro ⟨a, b⟩ _
    simp only
    omega
  calc ∑ p ∈ A ×ˢ B, max 0 (1 - |((p.2 - p.1 : ℤ) : ℝ) - y|)
      ≤ ∑ p ∈ A ×ˢ B, ((if p.2 - p.1 = k then 1 - (y - k) else 0) +
          (if p.2 - p.1 = k + 1 then y - k else 0)) :=
        Finset.sum_le_sum fun p _ => key (p.2 - p.1)
    _ = (1 - (y - k)) * (((A ×ˢ B).filter (fun p : ℤ × ℤ => p.2 - p.1 = k)).card : ℝ) +
          (y - k) * (((A ×ˢ B).filter (fun p : ℤ × ℤ => p.2 - p.1 = k + 1)).card : ℝ) := by
        rw [Finset.sum_add_distrib, Finset.sum_ite, Finset.sum_ite]
        simp only [Finset.sum_const, nsmul_eq_mul]
        ring
    _ ≤ (1 - (y - k)) * (Erdos36.MaxOverlap A B : ℝ) + (y - k) * (Erdos36.MaxOverlap A B : ℝ) := by
        rw [hcard, hcard]
        have e1 : 0 ≤ 1 - (y - k) := by linarith
        have e2 : 0 ≤ y - k := by linarith
        exact add_le_add (mul_le_mul_of_nonneg_left (hO _) e1) (mul_le_mul_of_nonneg_left (hO _) e2)
    _ = (Erdos36.MaxOverlap A B : ℝ) := by ring
