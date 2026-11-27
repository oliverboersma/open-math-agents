import OMAReductions.R_PoincareConjecture_poincare_conjecture_variants_dimension_two_R1_H4_R1
import Mathlib

-- Step PoincareConjecture.poincare_conjecture.variants.dimension_two.R1.H4.R1.H3: hypothesis H3 of reduction PoincareConjecture.poincare_conjecture.variants.dimension_two.R1.H4.R1
-- Credit: @ivillar
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

/-!
Send every generator to the nontrivial element of the group of order two. Each letter of the
relator, with either sign, maps to that involution, so the relator of length 2k maps to its
2k-th power, which is trivial. The induced map on the presented group sends a generator to a
nontrivial element, so the presented group is not a subsingleton.
-/

theorem OMA.solution : OMA.R_PoincareConjecture_poincare_conjecture_variants_dimension_two_R1_H4_R1.H3 := by
  intro k w hk hw hs
  let g : Multiplicative (ZMod 2) := Multiplicative.ofAdd 1
  have hg : g⁻¹ = g := by decide
  have hrel : ∀ r ∈ ({FreeGroup.mk w} : Set (FreeGroup (Fin k))),
      FreeGroup.lift (fun _ : Fin k => g) r = 1 := by
    intro r hr
    rw [Set.mem_singleton_iff] at hr
    subst hr
    rw [FreeGroup.lift_mk]
    have hmap : w.map (fun x : Fin k × Bool => cond x.2 g g⁻¹) = List.replicate w.length g := by
      apply List.eq_replicate_iff.mpr
      refine ⟨by simp, ?_⟩
      intro b hb
      obtain ⟨x, -, rfl⟩ := List.mem_map.mp hb
      cases x.2 <;> simp [hg]
    rw [hmap, List.prod_replicate, hw, pow_mul]
    have : g ^ 2 = 1 := by decide
    rw [this, one_pow]
  let φ := PresentedGroup.toGroup hrel
  have h1 : φ (PresentedGroup.of ⟨0, hk⟩) = g := PresentedGroup.toGroup.of hrel
  have h2 : (PresentedGroup.of ⟨0, hk⟩ :
      PresentedGroup ({FreeGroup.mk w} : Set (FreeGroup (Fin k)))) = 1 :=
    Subsingleton.elim _ _
  rw [h2, map_one] at h1
  exact absurd h1 (by decide)
