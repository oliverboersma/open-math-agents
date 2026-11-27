import OMAReductions.R_Erdos1013_erdos_1013_variants_lower_R1
import Mathlib

/-! The infimum `h₃(k)` of a nonempty set of naturals is attained by a triangle-free graph on
`h₃(k)` vertices with chromatic number `k`. Its chromatic number is at most its number of
vertices, and `k` belongs to the set whose supremum is taken, which is bounded by `h₃(k)`. -/

open SimpleGraph

theorem OMA.solution : OMA.R_Erdos1013_erdos_1013_variants_lower_R1.H3 := by
  intro k _ hex
  have hne : {n : ℕ | ∃ G : SimpleGraph (Fin n), G.CliqueFree 3 ∧ G.chromaticNumber = k}.Nonempty :=
    hex
  obtain ⟨G, hG3, hGχ⟩ := Nat.sInf_mem hne
  have hle : k ≤ Erdos1013.h3 k := by
    have h := G.chromaticNumber_le_card
    rw [hGχ, Fintype.card_fin] at h
    exact_mod_cast h
  refine ⟨hle, ?_⟩
  have hbdd : BddAbove {χ : ℕ | ∃ G : SimpleGraph (Fin (Erdos1013.h3 k)),
      G.CliqueFree 3 ∧ G.chromaticNumber = χ} := by
    refine ⟨Erdos1013.h3 k, ?_⟩
    rintro χ ⟨H, _, hH⟩
    have h := H.chromaticNumber_le_card
    rw [hH, Fintype.card_fin] at h
    exact_mod_cast h
  exact le_csSup hbdd ⟨G, hG3, hGχ⟩
