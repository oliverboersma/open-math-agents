import OMAReductions.R_RamseyNumbers_ramsey_number_four_five_R1
import Mathlib.Data.Fin.Tuple.Embedding

/-!
# The degree-eight case of R(4,5)=25

A triangle-free eight-set leaves sixteen vertices. If those vertices have
no independent four-set, the complementary block is a Ramsey(4,4,16)
graph. Its classification and the two gluing exclusions suffice.

The two graph words are from McKay's Ramsey(4,4,16) catalogue at
https://users.cecs.anu.edu.au/~bdm/data/ramsey.html. Graph6 column order puts
edge (i,j) at bit j*(j-1)/2+i for i<j.
-/

open Finset SimpleGraph

namespace OMA.R_RamseyNumbers_ramsey_number_four_five_R1_H1_R1

private theorem exclude_of_labels {G : SimpleGraph (Fin 24)}
    (hG : G.CliqueFree 4) (hC : Gᶜ.CliqueFree 5)
    (inner : Fin 8 ↪ Fin 24) (outer : Fin 16 ↪ Fin 24)
    (apart : Disjoint (Set.range inner) (Set.range outer))
    (triangleFree : (G.comap inner).CliqueFree 3) (word : Nat)
    (fixed : ∀ i j : Fin 16, i < j →
      (G.Adj (outer i) (outer j) ↔ word.testBit (j.val*(j.val-1)/2+i.val) = true))
    (exclude : ∀ K : SimpleGraph (Fin 24), K.CliqueFree 4 → Kᶜ.CliqueFree 5 →
      (K.comap (Fin.castAdd 16 : Fin 8 → Fin 24)).CliqueFree 3 →
      (∀ i j : Fin 16, i < j →
        (K.Adj (Fin.natAdd 8 i) (Fin.natAdd 8 j) ↔
          word.testBit (j.val*(j.val-1)/2+i.val) = true)) → False) : False := by
  let joined := Fin.Embedding.append apart
  let e : Fin 24 ≃ Fin 24 := Equiv.ofBijective joined
    ⟨joined.injective,Finite.surjective_of_injective joined.injective⟩
  have el (i : Fin 8) : e (Fin.castAdd 16 i) = inner i := Fin.append_left inner outer i
  have er (i : Fin 16) : e (Fin.natAdd 8 i) = outer i := Fin.append_right inner outer i
  let K := G.comap e
  have iso : K ≃g G := SimpleGraph.Iso.comap e G
  have hK : K.CliqueFree 4 := hG.comap iso.toEmbedding.isContained
  have hKC : Kᶜ.CliqueFree 5 := hC.comap (SimpleGraph.Embedding.complEquiv iso.toEmbedding).isContained
  have block : K.comap (Fin.castAdd 16 : Fin 8 → Fin 24) = G.comap inner := by
    ext i j
    change G.Adj (e (Fin.castAdd 16 i)) (e (Fin.castAdd 16 j)) ↔ G.Adj (inner i) (inner j)
    rw [el,el]
  apply exclude K hK hKC (block.symm ▸ triangleFree)
  intro i j hij
  change G.Adj (e (Fin.natAdd 8 i)) (e (Fin.natAdd 8 j)) ↔ _
  rw [er,er]
  exact fixed i j hij

/-- Classify the possible sixteen-vertex outside graphs up to relabeling. -/
def H1 : Prop :=
  ∀ G : SimpleGraph (Fin 16), G.CliqueFree 4 → Gᶜ.CliqueFree 4 →
    ∃ word : Nat, (word = 0xcb94e332f53ae143a3b6933356490b ∨
      word = 0xacb96354eb266b51b2b6553699403b) ∧
      ∃ e : Fin 16 ≃ Fin 16, ∀ i j : Fin 16, i < j →
        (G.Adj (e i) (e j) ↔ word.testBit (j.val*(j.val-1)/2+i.val) = true)

/-- The first outside graph admits no gluing to a triangle-free eight-set. -/
def H2 : Prop :=
  ∀ G : SimpleGraph (Fin 24), G.CliqueFree 4 → Gᶜ.CliqueFree 5 →
    (G.comap (Fin.castAdd 16 : Fin 8 → Fin 24)).CliqueFree 3 →
    (∀ i j : Fin 16, i < j →
      (G.Adj (Fin.natAdd 8 i) (Fin.natAdd 8 j) ↔
        (0xcb94e332f53ae143a3b6933356490b : Nat).testBit (j.val*(j.val-1)/2+i.val) = true)) → False

/-- The second outside graph admits no gluing to a triangle-free eight-set. -/
def H3 : Prop :=
  ∀ G : SimpleGraph (Fin 24), G.CliqueFree 4 → Gᶜ.CliqueFree 5 →
    (G.comap (Fin.castAdd 16 : Fin 8 → Fin 24)).CliqueFree 3 →
    (∀ i j : Fin 16, i < j →
      (G.Adj (Fin.natAdd 8 i) (Fin.natAdd 8 j) ↔
        (0xacb96354eb266b51b2b6553699403b : Nat).testBit (j.val*(j.val-1)/2+i.val) = true)) → False

theorem main : H1 → H2 → H3 → OMA.R_RamseyNumbers_ramsey_number_four_five_R1.H1 := by
  classical
  intro classify first second G hG hC T eight
  by_cases htri : ∃ S ⊆ T, G.IsNClique 3 S
  · exact Or.inl htri
  by_cases hind : ∃ S : Finset (Fin 24), Disjoint S T ∧ Gᶜ.IsNClique 4 S
  · exact Or.inr hind
  exfalso
  have sixteen : Tᶜ.card = 16 := by rw [Finset.card_compl, Fintype.card_fin, eight]
  let inner : Fin 8 ↪ Fin 24 :=
    (T.equivFinOfCardEq eight).symm.toEmbedding.trans (Function.Embedding.subtype (· ∈ T))
  let outer : Fin 16 ↪ Fin 24 :=
    (Tᶜ.equivFinOfCardEq sixteen).symm.toEmbedding.trans (Function.Embedding.subtype (· ∈ Tᶜ))
  have hin (i : Fin 8) : inner i ∈ T := ((T.equivFinOfCardEq eight).symm i).property
  have hout (i : Fin 16) : outer i ∉ T :=
    Finset.mem_compl.mp ((Tᶜ.equivFinOfCardEq sixteen).symm i).property
  have innerFree : (G.comap inner).CliqueFree 3 := by
    intro S clique
    refine htri ⟨S.map inner,?_ , OMA.R_RamseyNumbers_ramsey_number_four_five_R1.map_clique
      (SimpleGraph.Embedding.comap inner G) clique⟩
    intro w hw
    obtain ⟨i,_,rfl⟩ := mem_map.mp hw
    exact hin i
  let O := G.comap outer
  let embed : O ↪g G := SimpleGraph.Embedding.comap outer G
  have outerFree : O.CliqueFree 4 := hG.comap embed.isContained
  have outerCompFree : Oᶜ.CliqueFree 4 := by
    intro S clique
    have mapped : Gᶜ.IsNClique 4 (S.map outer) :=
      OMA.R_RamseyNumbers_ramsey_number_four_five_R1.map_clique
        (SimpleGraph.Embedding.complEquiv embed) clique
    refine hind ⟨S.map outer,Finset.disjoint_left.mpr ?_,mapped⟩
    intro w hw ht
    obtain ⟨i,_,rfl⟩ := mem_map.mp hw
    exact hout i ht
  obtain ⟨word,cases,e,fixed⟩ := classify O outerFree outerCompFree
  let outer' := e.toEmbedding.trans outer
  have apart : Disjoint (Set.range inner) (Set.range outer') := by
    apply Set.disjoint_left.mpr
    rintro w ⟨i,rfl⟩ ⟨j,he⟩
    exact hout (e j) (he.symm ▸ hin i)
  have edges (i j : Fin 16) (hij : i < j) :
      G.Adj (outer' i) (outer' j) ↔ word.testBit (j.val*(j.val-1)/2+i.val) = true :=
    fixed i j hij
  rcases cases with rfl | rfl
  · exact exclude_of_labels hG hC inner outer' apart innerFree _ edges first
  · exact exclude_of_labels hG hC inner outer' apart innerFree _ edges second

end OMA.R_RamseyNumbers_ramsey_number_four_five_R1_H1_R1