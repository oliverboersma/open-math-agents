import OMAReductions.R_Arxiv_2507_17780_tx_graffiti_conjecture_1_R1

/-!
Separate the Havel–Hakimi residue bound into a local Maxine inequality and
an elementary bound on the list recursion. The main proof is the complete
strong induction on the number of vertices: delete a vertex of positive
maximum degree, and embed an independent set of the smaller induced graph
back into the original graph. The terminal edgeless graph is handled by H2.

The local comparison is motivated by Griggs–Kleitman,
Independence and the Havel–Hakimi residue, Discrete Mathematics 127 (1994),
209–212, DOI 10.1016/0012-365X(92)00479-B. No claim is made here that either
new hypothesis has been proved.
-/

namespace OMA.R_Arxiv_2507_17780_tx_graffiti_conjecture_1_R1_H1_R1

open SimpleGraph

/-- Removing a positive maximum-degree vertex cannot decrease the residue. -/
def H1 : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (v : V),
    0 < G.degree v → (∀ w : V, G.degree w ≤ G.degree v) →
    G.residue ≤ (G.induce {w : V | w ≠ v}).residue

/-- The Havel–Hakimi list recursion never returns more than the input length. -/
def H2 : Prop :=
  ∀ s : List ℕ, SimpleGraph.residueAux s ≤ s.length

lemma indepNum_induce_le {V : Type} [Fintype V] (G : SimpleGraph V)
    (S : Set V) [Fintype S] : (G.induce S).indepNum ≤ G.indepNum := by
  classical
  obtain ⟨s, hs⟩ := (G.induce S).exists_isNIndepSet_indepNum
  let e : S ↪ V := ⟨Subtype.val, Subtype.val_injective⟩
  have hI : G.IsIndepSet (↑(s.map e) : Set V) := by
    intro x hx y hy hxy hadj
    obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hx
    obtain ⟨b, hb, rfl⟩ := Finset.mem_map.mp hy
    exact hs.isIndepSet ha hb (fun hab => hxy (congrArg e hab)) hadj
  simpa only [Finset.card_map, hs.card_eq] using hI.card_le_indepNum

theorem main : H1 → H2 → OMA.R_Arxiv_2507_17780_tx_graffiti_conjecture_1_R1.H1 := by
  intro hstep hlength
  have aux : ∀ n : ℕ, ∀ (V : Type) [Fintype V] (G : SimpleGraph V)
      [DecidableRel G.Adj], Fintype.card V = n → G.residue ≤ G.indepNum := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro V _ G _ hn
      classical
      by_cases hbot : G = ⊥
      · have hres : G.residue ≤ Fintype.card V := by
          unfold SimpleGraph.residue
          simpa using hlength ((Finset.univ.val.map fun v => G.degree v).sort (· ≥ ·))
        have hI : G.IsIndepSet (↑(Finset.univ : Finset V) : Set V) := by
          rw [hbot]
          intro x hx y hy hxy hadj
          exact hadj
        exact hres.trans (by simpa using hI.card_le_indepNum)
      · have hmax : 0 < G.maxDegree := by
          exact Nat.pos_of_ne_zero (fun hz => hbot (G.maxDegree_eq_zero_iff.mp hz))
        haveI : Nonempty V := by
          by_contra hne
          haveI : IsEmpty V := not_nonempty_iff.mp hne
          simp at hmax
        obtain ⟨v, hv⟩ := G.exists_maximal_degree_vertex
        have hvpos : 0 < G.degree v := by omega
        have hvmax : ∀ w : V, G.degree w ≤ G.degree v := by
          intro w
          exact hv ▸ G.degree_le_maxDegree w
        have hcard : Fintype.card {w : V | w ≠ v} < n := by
          rw [← hn]
          exact Fintype.card_subtype_lt (x := v) (by simp)
        exact (hstep V G v hvpos hvmax).trans
          ((ih _ hcard {w : V | w ≠ v} (G.induce {w : V | w ≠ v}) rfl).trans
            (indepNum_induce_le G _))
  intro V _ G _
  exact aux _ V G rfl

end OMA.R_Arxiv_2507_17780_tx_graffiti_conjecture_1_R1_H1_R1
