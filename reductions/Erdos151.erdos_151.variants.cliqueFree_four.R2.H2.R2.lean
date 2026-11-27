import OMAReductions.R_Erdos151_erdos_151_variants_cliqueFree_four_R2

/-! Split the residual clique-transversal problem after threshold eleven. -/

open Finset SimpleGraph
open scoped Classical

namespace OMA.R_Erdos151_erdos_151_variants_cliqueFree_four_R2_H2_R2

/-- The first two thresholds of the residual problem. -/
def H1 : Prop :=
  ∀ n, (10 ≤ Erdos151.H n ∧ Erdos151.H n ≤ 11) →
    ∀ G : SimpleGraph (Fin n), G.CliqueFree 4 →
    (∀ v, (univ.filter (G.Adj v)).card < Erdos151.H n) →
    (∃ x y, G.Adj x y ∧ 3 ≤ (univ.filter fun z => G.Adj x z ∧ G.Adj y z).card) →
    cliqueTransversalNumber G ≤ n - Erdos151.H n

/-- The same graph case at thresholds at least twelve. -/
def H2 : Prop :=
  ∀ n, 12 ≤ Erdos151.H n → ∀ G : SimpleGraph (Fin n), G.CliqueFree 4 →
    (∀ v, (univ.filter (G.Adj v)).card < Erdos151.H n) →
    (∃ x y, G.Adj x y ∧ 3 ≤ (univ.filter fun z => G.Adj x z ∧ G.Adj y z).card) →
    cliqueTransversalNumber G ≤ n - Erdos151.H n

theorem main : H1 → H2 → OMA.R_Erdos151_erdos_151_variants_cliqueFree_four_R2.H2 := by
  intro hfirst hrest n hn G hG hdegree hedge
  by_cases ht : Erdos151.H n ≤ 11
  · exact hfirst n ⟨hn, ht⟩ G hG hdegree hedge
  · exact hrest n (by omega) G hG hdegree hedge

end OMA.R_Erdos151_erdos_151_variants_cliqueFree_four_R2_H2_R2
