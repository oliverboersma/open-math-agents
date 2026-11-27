import OMAReductions.R_Arxiv_2001_02665_ringel_conjecture_large_R1
import Mathlib

-- Step Arxiv.2001.02665.ringel_conjecture_large.R1.H2: hypothesis H2 of reduction Arxiv.2001.02665.ringel_conjecture_large.R1
-- Credit: @ivillar
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

/-! The edge set of the mapped graph is the image of the edge set under `Sym2.map g`, which is
injective because `g` is; so the two edge sets have the same cardinality. -/

theorem OMA.solution : OMA.R_Arxiv_2001_02665_ringel_conjecture_large_R1.H2 := by
  intro n V _ T g
  rw [SimpleGraph.edgeSet_map]
  exact Set.ncard_image_of_injective _ (Sym2.map.injective g.injective)
