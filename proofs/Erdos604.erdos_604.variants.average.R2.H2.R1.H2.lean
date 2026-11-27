import OMAReductions.R_Erdos604_erdos_604_variants_average_R2_H2_R1
import Mathlib.Geometry.Euclidean.Basic

-- Shortens @ivillar's proof using the same two-circle intersection lemma.
open Finset
open scoped EuclideanGeometry

theorem OMA.solution : OMA.R_Erdos604_erdos_604_variants_average_R2_H2_R1.H2 := by
  classical
  intro A u v huv
  apply card_le_mul_card_image
  rintro ⟨s, t⟩ -
  by_contra! h
  obtain ⟨p, q, r, hp, hq, hr, hpq, hpr, hqr⟩ := two_lt_card_iff.mp h
  simp only [mem_filter, Prod.mk.injEq] at hp hq hr
  have hd : Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 2 := by simp
  exact (EuclideanGeometry.eq_of_dist_eq_of_dist_eq_of_finrank_eq_two hd huv hpq
    hp.2.1 hq.2.1 hr.2.1 hp.2.2 hq.2.2 hr.2.2).elim hpr.symm hqr.symm
