import OMAReductions.R_LovaszPlummerConjecture_sheehan_conjecture_R1

/-! Split the unmatched-chord case using a dominated boundary on the given cycle. -/

namespace OMA.R_LovaszPlummerConjecture_sheehan_conjecture_R1_H2_R1

open SimpleGraph LovaszPlummerConjecture

/-- The rotation lemma with domination required only at cycle-neighbors of I. -/
def H1 : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (v : V) (c : G.Walk v v), IsHamiltonianCycle G c →
    ∀ I : Finset V, I.Nonempty →
      (∀ x ∈ I, ∀ y ∈ I, s(x,y) ∉ c.edges) →
      (∀ u : V, u ∉ I → (∃ x ∈ I, s(u,x) ∈ c.edges) →
        ∃ w ∈ I, G.Adj u w ∧ s(u,w) ∉ c.edges) →
      ∃ (w : V) (d : G.Walk w w), IsHamiltonianCycle G d ∧
        d.edges.toFinset ≠ c.edges.toFinset

open scoped Classical in
/-- The residual quartic case in which neither a removable chord matching
nor a nonempty cycle-independent set with dominated cycle-boundary exists. -/
def H2 : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (_hreg : ∀ u, G.degree u = 4) (v : V) (c : G.Walk v v), IsHamiltonianCycle G c →
    (¬ ∃ (M : SimpleGraph V) (e : Sym2 V), M ≤ G ∧ e ∈ c.edges ∧
      (∀ u, M.degree u ≤ 1) ∧ (∀ u, M.degree u = 0 → u ∈ e) ∧
      (∀ f ∈ c.edges, f ∉ M.edgeSet)) →
    (¬ ∃ I : Finset V, I.Nonempty ∧
      (∀ x ∈ I, ∀ y ∈ I, s(x,y) ∉ c.edges) ∧
      (∀ u : V, u ∉ I → (∃ x ∈ I, s(u,x) ∈ c.edges) →
        ∃ w ∈ I, G.Adj u w ∧ s(u,w) ∉ c.edges)) →
    ∃ (w : V) (d : G.Walk w w), IsHamiltonianCycle G d ∧
      d.edges.toFinset ≠ c.edges.toFinset

theorem main : H1 → H2 → OMA.R_LovaszPlummerConjecture_sheehan_conjecture_R1.H2 := by
  intro rotate residual V _ _ G _ hreg v c hc noMatching
  by_cases good : ∃ I : Finset V, I.Nonempty ∧
      (∀ x ∈ I, ∀ y ∈ I, s(x,y) ∉ c.edges) ∧
      (∀ u : V, u ∉ I → (∃ x ∈ I, s(u,x) ∈ c.edges) →
        ∃ w ∈ I, G.Adj u w ∧ s(u,w) ∉ c.edges)
  · obtain ⟨I,hne,hind,hboundary⟩ := good
    exact rotate G v c hc I hne hind hboundary
  · exact residual G hreg v c hc noMatching good

end OMA.R_LovaszPlummerConjecture_sheehan_conjecture_R1_H2_R1

