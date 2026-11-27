import FormalConjectures.Wikipedia.Kakeya
import Mathlib
-- Cover argument adapted from OpenAI/math 3344da59991ed94f9ba711217b29c1d760badfa6 (Apache-2.0).
open MeasureTheory AffineMap Metric
open scoped ENNReal
namespace OMA.R_Kakeya_kakeya_set_conjecture_R1

def H1 : Prop := ∀ {n : ℕ} {s : ℝ}, 0 < s → ∀ {F : Set (EuclideanSpace ℝ (Fin n))},
    Measure.hausdorffMeasure s F = 0 → ∀ {ε : ℝ≥0∞}, 0 < ε →
    ∃ (x : ℕ → (EuclideanSpace ℝ (Fin n))) (r : ℕ → ℝ) (Z : Set (EuclideanSpace ℝ (Fin n))),
      Z.Countable ∧ F ⊆ Z ∪ ⋃ j, Metric.ball (x j) (r j) ∧
      (∀ j, 0 ≤ r j ∧ r j ≤ 1) ∧
      (∑' j, ENNReal.ofReal (r j) ^ s) ≤ (2 : ℝ≥0∞) ^ s * ε

def H2 : Prop := ∀ {n : ℕ}, 2 ≤ n → ∀ (F : Set (EuclideanSpace ℝ (Fin n))), Kakeya.IsKakeya F → ∀ s : ℝ, 0 < s → s < n → ∃ c : ℝ≥0∞, 0 < c ∧
      ∀ (x : ℕ → (EuclideanSpace ℝ (Fin n))) (r : ℕ → ℝ) (Z : Set (EuclideanSpace ℝ (Fin n))), Z.Countable →
        F ⊆ Z ∪ ⋃ j, Metric.ball (x j) (r j) → (∀ j, 0 ≤ r j ∧ r j ≤ 1) →
        c ≤ ∑' j, ENNReal.ofReal (r j) ^ s

lemma dim_one (S : Set (EuclideanSpace ℝ (Fin 1)))
    (h : ∀ v : EuclideanSpace ℝ (Fin 1), ‖v‖ = 1 → ∃ a, affineSegment ℝ a (a+v) ⊆ S) : dimH S = 1 := by
  let v : EuclideanSpace ℝ (Fin 1) := PiLp.single 2 0 (1 : ℝ)
  have hv : ‖v‖ = 1 := by simp [v, PiLp.norm_single]
  obtain ⟨a, ha⟩ := h v hv
  have hv0 : v ≠ 0 := by intro e; simp [e] at hv
  have hne : a ≠ a + v := by simpa using hv0
  rw [affineSegment_eq_segment] at ha
  apply le_antisymm
  · have hle := dimH_mono (Set.subset_univ S)
    simpa [Real.dimH_univ_eq_finrank] using hle
  · simpa [Real.dimH_segment hne] using dimH_mono ha

theorem main : H1 → H2 → type_of% @Kakeya.kakeya_set_conjecture := by
  intro cheap costly n hn F hF
  by_cases hn2 : 2 ≤ n
  · have bound := costly hn2 F hF
    have hne (s : ℝ) (hs : 0 < s) (hn : s < n) : Measure.hausdorffMeasure s F ≠ 0 := by
      intro hz
      obtain ⟨c, hc, hb⟩ := bound s hs hn
      let A := (2 : ℝ≥0∞) ^ s
      have hAf : A ≠ ∞ := (ENNReal.rpow_lt_top_of_nonneg hs.le (by norm_num)).ne
      have hA : A ≠ 0 := (ENNReal.rpow_pos (by norm_num) (by norm_num)).ne'
      let b := min c 1
      have hbpos : 0 < b := lt_min hc (by norm_num)
      have hbf : b ≠ ∞ := ne_top_of_le_ne_top (by norm_num : (1:ℝ≥0∞) ≠ ∞) (min_le_right _ _)
      have he : 0 < (b / 2) / A := ENNReal.div_pos (ENNReal.div_pos hbpos.ne' (by norm_num)).ne' hAf
      obtain ⟨x,r,Z,hZ,hcov,hr,hcost⟩ := cheap hs hz he
      have hh := (hb x r Z hZ hcov hr).trans hcost
      change c ≤ A * (b / 2 / A) at hh
      rw [mul_comm, ENNReal.div_mul_cancel hA hAf] at hh
      exact (not_lt_of_ge ((min_le_left c 1).trans hh)) (ENNReal.half_lt_self hbpos.ne' hbf)
    apply le_antisymm
    · simpa [Real.dimH_univ_eq_finrank] using dimH_mono (Set.subset_univ F)
    · apply ENNReal.le_of_forall_nnreal_lt
      intro d hd
      by_cases hd0 : d = 0
      · simp [hd0]
      · have hdpos : 0 < (d : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hd0)
        have hdn : (d : ℝ) < n := by exact_mod_cast hd
        exact le_dimH_of_hausdorffMeasure_ne_zero
          (hne _ hdpos hdn)
  · have heq : n = 1 := by omega
    subst n
    simpa using dim_one F hF
end OMA.R_Kakeya_kakeya_set_conjecture_R1
