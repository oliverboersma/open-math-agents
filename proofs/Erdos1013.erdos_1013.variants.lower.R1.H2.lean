import OMAReductions.R_Erdos1013_erdos_1013_variants_lower_R1
import Mathlib

/-!
Step H2 of Erdos1013.erdos_1013.variants.lower.R1: triangle-free graphs of every
chromatic number. For k at least two this is the Mycielski construction from
FormalConjecturesForMathlib (SimpleGraph.exists_cliqueNum_eq_two_chromaticNumber_eq);
for k = 1 the edgeless graph on one vertex works.
-/

theorem OMA.solution : OMA.R_Erdos1013_erdos_1013_variants_lower_R1.H2 := by
  unfold OMA.R_Erdos1013_erdos_1013_variants_lower_R1.H2
  intro k hk
  rcases Nat.lt_or_ge k 2 with h | h
  · have hk1 : k = 1 := by omega
    subst hk1
    refine ⟨1, ⊥, SimpleGraph.cliqueFree_bot (by norm_num), ?_⟩
    exact_mod_cast (SimpleGraph.chromaticNumber_bot (V := Fin 1))
  · obtain ⟨n, G, hω, hχ⟩ := SimpleGraph.exists_cliqueNum_eq_two_chromaticNumber_eq k h
    refine ⟨n, G, ?_, hχ⟩
    intro s hs
    have h3 := hs.isClique.card_le_cliqueNum
    rw [hs.card_eq, hω] at h3
    omega
