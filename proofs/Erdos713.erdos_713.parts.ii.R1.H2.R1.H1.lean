import OMAReductions.R_Erdos713_erdos_713_parts_ii_R1_H2_R1
import Mathlib

-- Step Erdos713.erdos_713.parts.ii.R1.H2.R1.H1: hypothesis H1 of reduction Erdos713.erdos_713.parts.ii.R1.H2.R1
-- Credit: @ivillar
--
-- Proof. Pick a vertex `a` and let `S` be its connected component; since `G` is disconnected,
-- some `b` lies outside `S`. Take `G₁ = G[S]` and `G₂ = G[Sᶜ]`, moved to `Fin` vertex types.
-- Every neighbour of a vertex lies in its component, so degrees are unchanged and both pieces
-- keep minimum degree at least two. For the extremal bound, let `H` be a `G`-free host on
-- `n` vertices. If `H` has no copy of `G₁` we are done. Otherwise let `T` be the vertex set of a
-- copy of `G₁`, and delete every edge meeting `T`; this removes at most `|T| n ≤ q n` edges.
-- A copy of `G₂` in what remains avoids `T` (each vertex of `G₂` has a neighbour), so together
-- with the copy of `G₁` it would give a copy of `G` in `H`. Hence the remainder is `G₂`-free.

open SimpleGraph Finset

namespace OMA.Erdos713iiH2H1

open scoped Classical

/-- The graph `H` with every edge meeting `T` deleted. -/
def avoid {n : ℕ} (H : SimpleGraph (Fin n)) (T : Finset (Fin n)) : SimpleGraph (Fin n) where
  Adj x y := H.Adj x y ∧ x ∉ T ∧ y ∉ T
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩
  loopless := ⟨fun x h => H.loopless.irrefl x h.1⟩

lemma card_edgeFinset_le_avoid {n : ℕ} (H : SimpleGraph (Fin n)) (T : Finset (Fin n)) :
    #H.edgeFinset ≤ #(avoid H T).edgeFinset + #T * n := by
  have hsub : H.edgeFinset ⊆ (avoid H T).edgeFinset ∪ T.biUnion (fun t => H.incidenceFinset t) := by
    intro e he
    induction e using Sym2.ind with
    | _ x y =>
      rw [mem_edgeFinset, mem_edgeSet] at he
      by_cases hx : x ∈ T
      · apply Finset.mem_union_right
        rw [Finset.mem_biUnion]
        exact ⟨x, hx, by rw [mem_incidenceFinset, mem_incidenceSet]; exact he⟩
      · by_cases hy : y ∈ T
        · apply Finset.mem_union_right
          rw [Finset.mem_biUnion]
          refine ⟨y, hy, ?_⟩
          rw [mem_incidenceFinset, Sym2.eq_swap, mem_incidenceSet]
          exact he.symm
        · apply Finset.mem_union_left
          rw [mem_edgeFinset, mem_edgeSet]
          exact ⟨he, hx, hy⟩
  calc #H.edgeFinset ≤ #((avoid H T).edgeFinset ∪ T.biUnion (fun t => H.incidenceFinset t)) :=
        Finset.card_le_card hsub
    _ ≤ #(avoid H T).edgeFinset + #(T.biUnion (fun t => H.incidenceFinset t)) :=
        Finset.card_union_le _ _
    _ ≤ #(avoid H T).edgeFinset + ∑ t ∈ T, #(H.incidenceFinset t) := by
        gcongr
        exact Finset.card_biUnion_le
    _ ≤ #(avoid H T).edgeFinset + ∑ _t ∈ T, n := by
        gcongr with t ht
        rw [card_incidenceFinset_eq_degree]
        have := H.degree_lt_card_verts t
        rw [Fintype.card_fin] at this
        omega
    _ = #(avoid H T).edgeFinset + #T * n := by
        rw [Finset.sum_const, smul_eq_mul]

/-- The extremal bound for a graph split along a set closed under adjacency. -/
lemma extremal_split {q : ℕ} (G : SimpleGraph (Fin q)) (S : Set (Fin q))
    (hS : ∀ x y, G.Adj x y → (x ∈ S ↔ y ∈ S))
    {W₁ W₂ : Type} [Fintype W₁] [Fintype W₂]
    (G₁ : SimpleGraph W₁) (G₂ : SimpleGraph W₂)
    (e₁ : G₁ ≃g G.induce S) (e₂ : G₂ ≃g G.induce Sᶜ)
    (hW₁ : Fintype.card W₁ ≤ q) (hnb : ∀ v : W₂, ∃ w, G₂.Adj v w) (n : ℕ) :
    extremalNumber n G ≤ extremalNumber n G₁ + extremalNumber n G₂ + q * n := by
  have key : ∀ (H : SimpleGraph (Fin n)), G.Free H →
      #H.edgeFinset ≤ extremalNumber n G₁ + extremalNumber n G₂ + q * n := by
    intro H hfree
    by_cases h1 : G₁ ⊑ H
    · obtain ⟨f⟩ := h1
      let T : Finset (Fin n) := Finset.univ.image f
      have hT : #T ≤ q := Finset.card_image_le.trans (by rw [Finset.card_univ]; exact hW₁)
      have hcount := card_edgeFinset_le_avoid H T
      by_cases h2 : G₂ ⊑ avoid H T
      · exfalso
        obtain ⟨g⟩ := h2
        apply hfree
        -- g avoids T
        have hgT : ∀ z : W₂, g z ∉ T := by
          intro z
          obtain ⟨w, hw⟩ := hnb z
          exact (g.toHom.map_adj hw).2.1
        let φ : Fin q → Fin n := fun x =>
          if hx : x ∈ S then f (e₁.symm ⟨x, hx⟩) else g (e₂.symm ⟨x, hx⟩)
        have hφS : ∀ x (hx : x ∈ S), φ x = f (e₁.symm ⟨x, hx⟩) := by
          intro x hx
          simp only [φ, dif_pos hx]
        have hφN : ∀ x (hx : x ∉ S), φ x = g (e₂.symm ⟨x, hx⟩) := by
          intro x hx
          simp only [φ, dif_neg hx]
        have hmap : ∀ {x y : Fin q}, G.Adj x y → H.Adj (φ x) (φ y) := by
          intro x y hxy
          by_cases hx : x ∈ S
          · have hy : y ∈ S := (hS x y hxy).mp hx
            rw [hφS x hx, hφS y hy]
            apply f.toHom.map_adj
            rw [e₁.symm.map_adj_iff]
            simpa using hxy
          · have hy : y ∉ S := fun hy => hx ((hS x y hxy).mpr hy)
            rw [hφN x hx, hφN y hy]
            have := g.toHom.map_adj (show G₂.Adj (e₂.symm ⟨x, hx⟩) (e₂.symm ⟨y, hy⟩) by
              rw [e₂.symm.map_adj_iff]
              simpa using hxy)
            exact this.1
        have hinj : Function.Injective φ := by
          intro x y hxy
          by_cases hx : x ∈ S
          · by_cases hy : y ∈ S
            · rw [hφS x hx, hφS y hy] at hxy
              have := e₁.symm.injective (f.injective hxy)
              simpa using congrArg Subtype.val this
            · exfalso
              rw [hφS x hx, hφN y hy] at hxy
              exact hgT _ (hxy ▸ Finset.mem_image_of_mem f (Finset.mem_univ _))
          · by_cases hy : y ∈ S
            · exfalso
              rw [hφN x hx, hφS y hy] at hxy
              exact hgT _ (hxy.symm ▸ Finset.mem_image_of_mem f (Finset.mem_univ _))
            · rw [hφN x hx, hφN y hy] at hxy
              have := e₂.symm.injective (g.injective hxy)
              simpa using congrArg Subtype.val this
        exact ⟨⟨⟨φ, hmap⟩, hinj⟩⟩
      · have h3 := card_edgeFinset_le_extremalNumber h2
        rw [Fintype.card_fin] at h3
        have : #T * n ≤ q * n := Nat.mul_le_mul_right n hT
        omega
    · have h3 := card_edgeFinset_le_extremalNumber h1
      rw [Fintype.card_fin] at h3
      omega
  have := (extremalNumber_le_iff (V := Fin n) G
    (extremalNumber n G₁ + extremalNumber n G₂ + q * n)).mpr (fun H _ hH => by
      convert key H hH)
  rwa [Fintype.card_fin] at this

end OMA.Erdos713iiH2H1

open OMA.Erdos713iiH2H1 in
theorem OMA.solution : OMA.R_Erdos713_erdos_713_parts_ii_R1_H2_R1.H1 := by
  classical
  unfold OMA.R_Erdos713_erdos_713_parts_ii_R1_H2_R1.H1
  intro q G hq hdeg hnc
  have a : Fin q := ⟨0, hq⟩
  rw [connected_iff_exists_forall_reachable] at hnc
  push Not at hnc
  obtain ⟨b, hb⟩ := hnc a
  let S : Set (Fin q) := {x | G.Reachable a x}
  have haS : a ∈ S := Reachable.refl a
  have hbS : b ∉ S := hb
  have hS : ∀ x y, G.Adj x y → (x ∈ S ↔ y ∈ S) := by
    intro x y hxy
    constructor
    · intro hx; exact Reachable.trans hx hxy.reachable
    · intro hy; exact Reachable.trans hy hxy.symm.reachable
  have hSc : ∀ x y, G.Adj x y → (x ∈ Sᶜ ↔ y ∈ Sᶜ) := by
    intro x y hxy
    simp only [Set.mem_compl_iff]
    exact not_congr (hS x y hxy)
  let G₁ := (G.induce S).overFin rfl
  let G₂ := (G.induce Sᶜ).overFin rfl
  let e₁ : G₁ ≃g G.induce S := ((G.induce S).overFinIso rfl).symm
  let e₂ : G₂ ≃g G.induce Sᶜ := ((G.induce Sᶜ).overFinIso rfl).symm
  have hdeg_ind : ∀ (T : Set (Fin q)), (∀ x y, G.Adj x y → (x ∈ T ↔ y ∈ T)) →
      ∀ v : T, 2 ≤ (G.induce T).degree v := by
    intro T hT v
    rw [degree_induce_of_neighborSet_subset]
    · exact hdeg v
    · intro w hw
      exact (hT v w hw).mp v.2
  have hd₁ : ∀ v, 2 ≤ G₁.degree v := by
    intro v
    rw [← e₁.degree_eq v]
    convert hdeg_ind S hS (e₁ v)
  have hd₂ : ∀ v, 2 ≤ G₂.degree v := by
    intro v
    rw [← e₂.degree_eq v]
    convert hdeg_ind Sᶜ hSc (e₂ v)
  refine ⟨Fintype.card S, Fintype.card (Sᶜ : Set (Fin q)), G₁, G₂, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Fintype.card_pos_iff.mpr ⟨⟨a, haS⟩⟩
  · have := Fintype.card_subtype_lt (p := (· ∈ S)) hbS
    simpa using this
  · exact Fintype.card_pos_iff.mpr ⟨⟨b, hbS⟩⟩
  · have h := Fintype.card_subtype_lt (p := (· ∈ Sᶜ)) (x := a) (by simp [haS])
    rw [Fintype.card_fin] at h
    convert h using 1
  · exact ⟨(Copy.induce G S).comp e₁.toCopy⟩
  · exact ⟨(Copy.induce G Sᶜ).comp e₂.toCopy⟩
  · intro v
    convert hd₁ v
  · intro v
    convert hd₂ v
  · intro n
    refine extremal_split G S hS G₁ G₂ e₁ e₂ ?_ ?_ n
    · simp only [Fintype.card_fin]
      exact (Fintype.card_subtype_le _).trans (by simp)
    · intro v
      have h2 : 0 < G₂.degree v := by
        have := hd₂ v
        omega
      exact (degree_pos_iff_exists_adj G₂ v).mp h2
