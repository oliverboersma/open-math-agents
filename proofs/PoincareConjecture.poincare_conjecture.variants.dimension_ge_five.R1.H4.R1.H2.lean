import OMAReductions.R_PoincareConjecture_poincare_conjecture_variants_dimension_ge_five_R1_H4_R1
import Mathlib

-- Step PoincareConjecture.poincare_conjecture.variants.dimension_ge_five.R1.H4.R1.H2: hypothesis H2 of reduction PoincareConjecture.poincare_conjecture.variants.dimension_ge_five.R1.H4.R1
-- Credit: @ivillar
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

open Set Topology

/-! Pull the compact set back to Euclidean space, enclose it in a ball, and push the ball forward. The
closure of the image lies in the compact image of the closed ball, and the ball is homeomorphic to
Euclidean space. -/

theorem OMA.solution : OMA.R_PoincareConjecture_poincare_conjecture_variants_dimension_ge_five_R1_H4_R1.H2 := by
  intro n N _ _ K hK f hf hKf
  have hpre : IsCompact (f ⁻¹' K) := (hf.isInducing.isCompact_preimage_iff hKf).2 hK
  obtain ⟨R, hR, hsub⟩ := hpre.isBounded.subset_ball_lt 0 0
  refine ⟨f '' Metric.ball 0 R, ?_, hf.isOpenMap _ Metric.isOpen_ball, ?_, ?_⟩
  · intro x hx
    obtain ⟨y, rfl⟩ := hKf hx
    exact ⟨y, hsub hx, rfl⟩
  · have hc : IsCompact (f '' Metric.closedBall 0 R) :=
      (isCompact_closedBall 0 R).image hf.continuous
    exact hc.of_isClosed_subset isClosed_closure
      (closure_minimal (image_mono Metric.ball_subset_closedBall) hc.isClosed)
  · let e := OpenPartialHomeomorph.univBall (0 : EuclideanSpace ℝ (Fin n)) R
    exact ⟨(hf.isEmbedding.homeomorphImage (Metric.ball 0 R)).symm.trans
        ((Homeomorph.setCongr (OpenPartialHomeomorph.univBall_target
          (0 : EuclideanSpace ℝ (Fin n)) hR)).symm.trans
          (e.toHomeomorphSourceTarget.symm.trans
            ((Homeomorph.setCongr (OpenPartialHomeomorph.univBall_source
              (0 : EuclideanSpace ℝ (Fin n)) R)).trans (Homeomorph.Set.univ _))))⟩
