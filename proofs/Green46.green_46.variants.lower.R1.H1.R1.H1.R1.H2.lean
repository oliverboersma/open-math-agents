import OMAReductions.R_Green46_green_46_variants_lower_R1_H1_R1_H1_R1
import Mathlib

-- Step Green46.green_46.variants.lower.R1.H1.R1.H1.R1.H2: hypothesis H2 of reduction Green46.green_46.variants.lower.R1.H1.R1.H1.R1
-- Credit: @ivillar
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

open Finset Filter Real
open scoped Classical

/-! Each shift t gives the edge of surviving vertices of the form t + h p with h in H; all of
them are congruent to t modulo p and there are at most |H| of them. The weight of an edge is
the total probability of the shifts that produce it, so summing over edges through a vertex
recovers the probability that the vertex is hit. -/

theorem OMA.solution : OMA.R_Green46_green_46_variants_lower_R1_H1_R1_H1_R1.H2 := by
  intro P V H T μ hP hμ
  let edge : ℕ → ℤ → Finset ℕ := fun p t => V.filter (fun q => ∃ h ∈ H, (q : ℤ) = t + (h : ℤ)*p)
  let w : ℕ → Finset ℕ → ℝ := fun p e => ∑ t ∈ (T p).filter (fun t => edge p t = e), μ p t
  have hfib : ∀ p (g : ℤ → ℝ), (∑ e ∈ (T p).image (edge p),
      ∑ t ∈ (T p).filter (fun t => edge p t = e), g t) = ∑ t ∈ T p, g t :=
    fun p g => Finset.sum_fiberwise_of_maps_to (fun t ht => Finset.mem_image_of_mem _ ht) g
  refine ⟨fun p => (T p).image (edge p), w, ?_, ?_, ?_⟩
  · intro p hp e he
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp he
    refine ⟨Finset.filter_subset _ _, ?_, ?_⟩
    · have hsub : edge p t ⊆ H.image (fun h : ℕ => (t + (h:ℤ)*p).toNat) := by
        intro q hq
        obtain ⟨-, h, hh, hq⟩ := Finset.mem_filter.mp hq
        exact Finset.mem_image.mpr ⟨h, hh, by rw [← hq]; simp⟩
      exact (Finset.card_le_card hsub).trans Finset.card_image_le
    · refine ⟨(t % (p:ℤ)).toNat, fun q hq => ?_⟩
      obtain ⟨-, h, hh, hq⟩ := Finset.mem_filter.mp hq
      have hp0 : (0:ℤ) < p := by exact_mod_cast hP p hp
      rw [← Int.natCast_modEq_iff]
      have e1 : (((t % (p:ℤ)).toNat : ℕ) : ℤ) = t % p := Int.toNat_of_nonneg (Int.emod_nonneg _ hp0.ne')
      rw [e1, hq]
      unfold Int.ModEq
      rw [Int.add_mul_emod_self_right, Int.emod_emod]
  · intro p hp
    refine ⟨?_, ?_⟩
    · simp only [w]
      rw [hfib p (μ p)]
      exact (hμ p hp).1
    · intro e he
      exact Finset.sum_nonneg fun t ht => (hμ p hp).2 t (Finset.mem_filter.mp ht).1
  · intro p hp q hq
    calc ∑ e ∈ ((T p).image (edge p)).filter (q ∈ ·), w p e
        = ∑ e ∈ (T p).image (edge p), ∑ t ∈ (T p).filter (fun t => edge p t = e),
            (if q ∈ edge p t then μ p t else 0) := by
          rw [Finset.sum_filter]
          apply Finset.sum_congr rfl
          intro e he
          split_ifs with hqe
          · apply Finset.sum_congr rfl
            intro t ht
            rw [(Finset.mem_filter.mp ht).2, if_pos hqe]
          · symm
            apply Finset.sum_eq_zero
            intro t ht
            rw [(Finset.mem_filter.mp ht).2, if_neg hqe]
      _ = ∑ t ∈ T p, (if q ∈ edge p t then μ p t else 0) := hfib p _
      _ = _ := by
          rw [← Finset.sum_filter]
          apply Finset.sum_congr _ (fun _ _ => rfl)
          apply Finset.filter_congr
          intro t _
          simp [edge, hq]
