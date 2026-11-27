import OMAReductions.R_Erdos151_erdos_151_variants_cliqueFree_four_R2

/-! Split the smallest permitted value of `H n` from the higher range. -/

open Finset SimpleGraph
open scoped Classical

-- Reduction Erdos151.erdos_151.variants.cliqueFree_four.R2.H2.R1 of step Erdos151.erdos_151.variants.cliqueFree_four.R2.H2
-- Credit: @senamakel

namespace OMA.R_Erdos151_erdos_151_variants_cliqueFree_four_R2_H2_R1

def H1 : Prop :=
  ∀ n, Erdos151.H n = 10 → ∀ G : SimpleGraph (Fin n), G.CliqueFree 4 →
    (∀ v, (univ.filter (G.Adj v)).card < Erdos151.H n) →
    (∃ x y, G.Adj x y ∧ 3 ≤ (univ.filter fun z => G.Adj x z ∧ G.Adj y z).card) →
    cliqueTransversalNumber G ≤ n - Erdos151.H n

def H2 : Prop :=
  ∀ n, 11 ≤ Erdos151.H n → ∀ G : SimpleGraph (Fin n), G.CliqueFree 4 →
    (∀ v, (univ.filter (G.Adj v)).card < Erdos151.H n) →
    (∃ x y, G.Adj x y ∧ 3 ≤ (univ.filter fun z => G.Adj x z ∧ G.Adj y z).card) →
    cliqueTransversalNumber G ≤ n - Erdos151.H n

theorem main : H1 → H2 → OMA.R_Erdos151_erdos_151_variants_cliqueFree_four_R2.H2 := by
  intro h10 h11 n hn G hG hDeg hEdge
  unfold H1 at h10
  unfold H2 at h11
  by_cases hEq : Erdos151.H n = 10
  · exact h10 n hEq G hG hDeg hEdge
  · apply h11 n _ G hG hDeg hEdge
    omega

end OMA.R_Erdos151_erdos_151_variants_cliqueFree_four_R2_H2_R1
