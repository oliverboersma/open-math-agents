import OMAReductions.R_PoincareConjecture_poincare_conjecture_variants_dimension_ge_five_R1_H4_R1
import Mathlib

-- Step PoincareConjecture.poincare_conjecture.variants.dimension_ge_five.R1.H4.R1.H3: hypothesis H3 of reduction PoincareConjecture.poincare_conjecture.variants.dimension_ge_five.R1.H4.R1
-- Credit: @ivillar
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

open Set Topology

/-! Choose a cell around each compact set. Feed each cell's compact closure, together with the next
set of the compact exhaustion, back into the choice; the resulting cells are nested and cover. -/

theorem OMA.solution : OMA.R_PoincareConjecture_poincare_conjecture_variants_dimension_ge_five_R1_H4_R1.H3 := by
  intro n N _ _ hyp
  choose! V hKV hVo hVc hVe using hyp
  let L : ℕ → Set N := fun j => Nat.rec (compactCovering N 0)
    (fun j W => closure (V W) ∪ compactCovering N (j+1)) j
  have hL0 : L 0 = compactCovering N 0 := rfl
  have hLs : ∀ j, L (j+1) = closure (V (L j)) ∪ compactCovering N (j+1) := fun j => rfl
  have hLc : ∀ j, IsCompact (L j) := by
    intro j
    induction j with
    | zero => rw [hL0]; exact isCompact_compactCovering N 0
    | succ j ih => rw [hLs]; exact (hVc _ ih).union (isCompact_compactCovering N _)
  have hcov : ∀ j, compactCovering N j ⊆ L j := by
    intro j
    cases j with
    | zero => rw [hL0]
    | succ j => rw [hLs]; exact subset_union_right
  refine ⟨fun j => V (L j), fun j => ⟨hVo _ (hLc j), hVe _ (hLc j)⟩, ?_, ?_⟩
  · intro j
    exact (hLs j ▸ subset_union_left).trans (hKV _ (hLc (j+1)))
  · refine eq_univ_of_forall fun x => ?_
    obtain ⟨j, hj⟩ := mem_iUnion.mp ((iUnion_compactCovering N).symm ▸ mem_univ x : x ∈ ⋃ j, compactCovering N j)
    exact mem_iUnion.mpr ⟨j, hKV _ (hLc j) (hcov j hj)⟩
