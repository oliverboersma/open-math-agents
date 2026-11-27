import FormalConjectures.Wikipedia.ReconstructionConjecture
import Mathlib

/-! # Kelly's tree reconstruction theorem
This file assembles the project's proofs for paths, induced-subtree counting,
and the central and bicentral cases. The original contributors are
@green-notes, @jared-jasinski and Marcus Buffett. @Deldor14 supplied the
small-branch, odd straight-arm and even large-branch cases and the assembly.
The attributed building blocks are reproduced from the Left to Solve repository
at 5c1b834, with the new verified cases incorporated below.
-/


/-
Reduction `ReconstructionConjecture.reconstruction_conjecture.variants.tree.R1` of Kelly's theorem
for trees. Proves Kelly's edge-count, degree-sequence, acyclicity, and tree-recognition lemmas
in-file, reducing the conjecture to four modular subgoals: path/degree-le-2 trees, Kelly's
induced-subgraph counting lemma, central (even diameter) non-path trees, and bicentral (odd
diameter) non-path trees.
-/

-- Reduction ReconstructionConjecture.reconstruction_conjecture.variants.tree.R1 of Trees are reconstructible
-- Credit: @green-notes
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

namespace OMA.R_ReconstructionConjecture_reconstruction_conjecture_variants_tree_R1

open SimpleGraph ReconstructionConjecture

-- Pillar 1: Any two finite trees on the same number of vertices >= 3 with all degrees <= 2
-- (paths) are isomorphic.
def H1 : Prop :=
  ∀ {V W : Type} [Fintype V] [Fintype W],
    3 ≤ Fintype.card V → Fintype.card V = Fintype.card W →
    ∀ (G : SimpleGraph V) (H : SimpleGraph W),
      G.IsTree → H.IsTree →
      (∀ v : V, (G.neighborSet v).ncard ≤ 2) →
      (∀ w : W, (H.neighborSet w).ncard ≤ 2) →
      Nonempty (G ≃g H)

-- Pillar 2: Kelly's induced-subgraph counting lemma for hypomorphic trees.
def H2 : Prop :=
  ∀ {V W : Type} [Fintype V] [Fintype W],
    3 ≤ Fintype.card V →
    ∀ (G : SimpleGraph V) (H : SimpleGraph W),
      G.IsTree → H.IsTree → Hypomorphic G H →
      ∀ (U : Type) [Fintype U] (Q : SimpleGraph U),
        Fintype.card U < Fintype.card V →
        {S : Finset V | Nonempty (G.induce (S : Set V) ≃g Q)}.ncard =
          {T : Finset W | Nonempty (H.induce (T : Set W) ≃g Q)}.ncard

-- Pillar 3: Central (even diameter) non-path hypomorphic trees with matching degrees and
-- induced-subgraph counts are isomorphic.
def H3 : Prop :=
  ∀ {V W : Type} [Fintype V] [Fintype W],
    3 ≤ Fintype.card V →
    ∀ (G : SimpleGraph V) (H : SimpleGraph W) (σ : V ≃ W),
      G.IsTree → H.IsTree →
      (∀ v : V, Nonempty (G.induce {v}ᶜ ≃g H.induce {σ v}ᶜ)) →
      (∀ v : V, (G.neighborSet v).ncard = (H.neighborSet (σ v)).ncard) →
      (∃ v : V, 3 ≤ (G.neighborSet v).ncard) →
      Even G.diam →
      (∀ (U : Type) [Fintype U] (Q : SimpleGraph U),
        Fintype.card U < Fintype.card V →
        {S : Finset V | Nonempty (G.induce (S : Set V) ≃g Q)}.ncard =
          {T : Finset W | Nonempty (H.induce (T : Set W) ≃g Q)}.ncard) →
      Nonempty (G ≃g H)

-- Pillar 4: Bicentral (odd diameter) non-path hypomorphic trees with matching degrees and
-- induced-subgraph counts are isomorphic.
def H4 : Prop :=
  ∀ {V W : Type} [Fintype V] [Fintype W],
    3 ≤ Fintype.card V →
    ∀ (G : SimpleGraph V) (H : SimpleGraph W) (σ : V ≃ W),
      G.IsTree → H.IsTree →
      (∀ v : V, Nonempty (G.induce {v}ᶜ ≃g H.induce {σ v}ᶜ)) →
      (∀ v : V, (G.neighborSet v).ncard = (H.neighborSet (σ v)).ncard) →
      (∃ v : V, 3 ≤ (G.neighborSet v).ncard) →
      Odd G.diam →
      (∀ (U : Type) [Fintype U] (Q : SimpleGraph U),
        Fintype.card U < Fintype.card V →
        {S : Finset V | Nonempty (G.induce (S : Set V) ≃g Q)}.ncard =
          {T : Finset W | Nonempty (H.induce (T : Set W) ≃g Q)}.ncard) →
      Nonempty (G ≃g H)

section KellyRecognition

open Classical

private lemma ncard_neighborSet_eq_degree {U : Type} [Fintype U] (Z : SimpleGraph U) (u : U) :
    (Z.neighborSet u).ncard = Z.degree u := by
  rw [← Z.card_neighborSet_eq_degree, Set.ncard_eq_toFinset_card' (Z.neighborSet u)]
  simp [Set.toFinset_card]

private lemma sum_card_edgeFinset_induce_compl {U : Type} [Fintype U] (Z : SimpleGraph U) :
    (∑ u : U, (Z.induce {u}ᶜ).edgeFinset.card) + 2 * Z.edgeFinset.card =
      Fintype.card U * Z.edgeFinset.card := by
  have hsingle : ∀ u : U, (Z.induce {u}ᶜ).edgeFinset.card + Z.degree u = Z.edgeFinset.card := by
    intro u
    rw [Z.card_edgeFinset_induce_compl_singleton u, Z.card_edgeFinset_deleteIncidenceSet u]
    have hle : Z.degree u ≤ Z.edgeFinset.card := Z.degree_le_card_edgeFinset u
    omega
  have hsum : (∑ u : U, (Z.induce {u}ᶜ).edgeFinset.card) + (∑ u : U, Z.degree u) =
      ∑ _u : U, Z.edgeFinset.card := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun u _ => hsingle u
  rw [Z.sum_degrees_eq_twice_card_edges, Finset.sum_const, Finset.card_univ, smul_eq_mul] at hsum
  exact hsum

private lemma kelly_tree_recognition {V W : Type} [Fintype V] [Fintype W]
    (hV : 3 ≤ Fintype.card V) (G : SimpleGraph V) (H : SimpleGraph W)
    (hTG : G.IsTree) (σ : V ≃ W)
    (hσ : ∀ v : V, Nonempty (G.induce {v}ᶜ ≃g H.induce {σ v}ᶜ)) :
    H.IsTree ∧ ∀ v : V, (G.neighborSet v).ncard = (H.neighborSet (σ v)).ncard := by
  have hcard : Fintype.card V = Fintype.card W := Fintype.card_congr σ
  have hW : 3 ≤ Fintype.card W := hcard ▸ hV
  have hsum_eq :
      (∑ v : V, (G.induce {v}ᶜ).edgeFinset.card) =
        ∑ w : W, (H.induce {w}ᶜ).edgeFinset.card := by
    rw [← Equiv.sum_comp σ (fun w : W => (H.induce {w}ᶜ).edgeFinset.card)]
    refine Finset.sum_congr rfl fun v _ => ?_
    obtain ⟨φ⟩ := hσ v
    exact Iso.card_edgeFinset_eq φ
  have hSG := sum_card_edgeFinset_induce_compl G
  have hSH := sum_card_edgeFinset_induce_compl H
  have hm_eq : G.edgeFinset.card = H.edgeFinset.card := by
    have hmul : (Fintype.card V - 2) * G.edgeFinset.card =
        (Fintype.card V - 2) * H.edgeFinset.card := by
      have h1 : (Fintype.card V - 2) * G.edgeFinset.card + 2 * G.edgeFinset.card =
          Fintype.card V * G.edgeFinset.card := by
        calc
          (Fintype.card V - 2) * G.edgeFinset.card + 2 * G.edgeFinset.card
            = (Fintype.card V - 2 + 2) * G.edgeFinset.card := (Nat.add_mul _ _ _).symm
          _ = Fintype.card V * G.edgeFinset.card := by rw [Nat.sub_add_cancel (by omega)]
      have h2 : (Fintype.card V - 2) * H.edgeFinset.card + 2 * H.edgeFinset.card =
          Fintype.card W * H.edgeFinset.card := by
        calc
          (Fintype.card V - 2) * H.edgeFinset.card + 2 * H.edgeFinset.card
            = (Fintype.card V - 2 + 2) * H.edgeFinset.card := (Nat.add_mul _ _ _).symm
          _ = Fintype.card W * H.edgeFinset.card := by rw [Nat.sub_add_cancel (by omega), hcard]
      omega
    exact Nat.mul_left_cancel (by omega) hmul
  have hdeg : ∀ v : V, (G.neighborSet v).ncard = (H.neighborSet (σ v)).ncard := by
    intro v
    rw [ncard_neighborSet_eq_degree, ncard_neighborSet_eq_degree]
    have h1 : (G.induce {v}ᶜ).edgeFinset.card + G.degree v = G.edgeFinset.card := by
      rw [G.card_edgeFinset_induce_compl_singleton v, G.card_edgeFinset_deleteIncidenceSet v]
      have hle : G.degree v ≤ G.edgeFinset.card := G.degree_le_card_edgeFinset v
      omega
    have h2 : (H.induce {σ v}ᶜ).edgeFinset.card + H.degree (σ v) = H.edgeFinset.card := by
      rw [H.card_edgeFinset_induce_compl_singleton (σ v), H.card_edgeFinset_deleteIncidenceSet (σ v)]
      have hle : H.degree (σ v) ≤ H.edgeFinset.card := H.degree_le_card_edgeFinset (σ v)
      omega
    obtain ⟨φ⟩ := hσ v
    have hc_eq : (G.induce {v}ᶜ).edgeFinset.card = (H.induce {σ v}ᶜ).edgeFinset.card :=
      Iso.card_edgeFinset_eq φ
    omega
  have hmG : G.edgeFinset.card + 1 = Fintype.card V := hTG.card_edgeFinset
  have hmH : H.edgeFinset.card + 1 = Fintype.card W := by omega
  have hHA : H.IsAcyclic := by
    intro w c hc_cyc
    by_cases hmiss : ∃ z : W, z ∉ c.support
    · obtain ⟨z, hz⟩ := hmiss
      have hw_supp : ∀ x ∈ c.support, x ∈ ({z}ᶜ : Set W) := by
        intro x hx
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
        rintro rfl
        exact hz hx
      have hc'_cyc : (c.induce ({z}ᶜ : Set W) hw_supp).IsCycle :=
        Walk.IsCycle.of_map (f := (Embedding.induce ({z}ᶜ : Set W)).toHom)
          (by rw [Walk.map_induce]; exact hc_cyc)
      let v := σ.symm z
      obtain ⟨φ⟩ := hσ v
      have hsz : σ v = z := σ.apply_symm_apply z
      have hA_H : (H.induce {z}ᶜ).IsAcyclic := by
        rw [← hsz, ← φ.isAcyclic_iff]
        exact hTG.isAcyclic.induce {v}ᶜ
      exact hA_H (c.induce ({z}ᶜ : Set W) hw_supp) hc'_cyc
    · push Not at hmiss
      have hmem_tail : ∀ z : W, z ∈ c.support.tail := by
        intro z
        have hz := hmiss z
        have hcons : c.support = w :: c.support.tail := by
          cases c with
          | nil => exact False.elim (hc_cyc.ne_nil rfl)
          | cons _ _ => rfl
        rw [hcons, List.mem_cons] at hz
        rcases hz with rfl | hz
        · exact c.end_mem_tail_support hc_cyc.not_nil
        · exact hz
      have hcard_le : Fintype.card W ≤ c.support.tail.length := by
        calc
          Fintype.card W = (Finset.univ : Finset W).card := rfl
          _ ≤ c.support.tail.toFinset.card := by
            refine Finset.card_le_card fun z _ => ?_
            exact List.mem_toFinset.mpr (hmem_tail z)
          _ = c.support.tail.length := List.toFinset_card_of_nodup hc_cyc.support_nodup
      have hlen_tail : c.support.tail.length = c.length := by
        have hls := c.length_support
        have hne : c.support ≠ [] := by simp
        have hcons : c.support = w :: c.support.tail := by
          cases c with
          | nil => exact False.elim (hc_cyc.ne_nil rfl)
          | cons _ _ => rfl
        have := congrArg List.length hcons
        simp only [List.length_cons] at this
        omega
      have hedges_le : c.edges.length ≤ H.edgeFinset.card := by
        calc
          c.edges.length = c.edges.toFinset.card :=
            (List.toFinset_card_of_nodup hc_cyc.isTrail.edges_nodup).symm
          _ ≤ H.edgeFinset.card := by
            refine Finset.card_le_card fun e he => ?_
            rw [List.mem_toFinset] at he
            exact (H.mem_edgeFinset).mpr (c.edges_subset_edgeSet he)
      have hedges_len : c.edges.length = c.length := c.length_edges
      omega
  have hHC : H.Connected := by
    let f : (Σ c : H.ConnectedComponent, c.toSimpleGraph.edgeSet) → H.edgeSet :=
      fun ⟨c, e⟩ => ⟨e.val.map Subtype.val, by
        rcases e with ⟨e, he⟩
        obtain ⟨⟨u, hu⟩, ⟨v, hv⟩, rfl⟩ : ∃ a b : c.supp, e = s(a, b) :=
          Sym2.ind (fun a b => ⟨a, b, rfl⟩) e
        dsimp only
        rw [Sym2.map_mk, mem_edgeSet]
        exact (c.toSimpleGraph.mem_edgeSet).mp he⟩
    have hfinj : Function.Injective f := by
      rintro ⟨c₁, ⟨e₁, he₁⟩⟩ ⟨c₂, ⟨e₂, he₂⟩⟩ hfe
      have heq_map : e₁.map Subtype.val = e₂.map Subtype.val := congrArg Subtype.val hfe
      obtain ⟨⟨u₁, hu₁⟩, ⟨v₁, hv₁⟩, rfl⟩ : ∃ a b : c₁.supp, e₁ = s(a, b) :=
        Sym2.ind (fun a b => ⟨a, b, rfl⟩) e₁
      obtain ⟨⟨u₂, hu₂⟩, ⟨v₂, hv₂⟩, rfl⟩ : ∃ a b : c₂.supp, e₂ = s(a, b) :=
        Sym2.ind (fun a b => ⟨a, b, rfl⟩) e₂
      rw [Sym2.map_mk, Sym2.map_mk, Sym2.eq_iff] at heq_map
      have hc_eq : c₁ = c₂ := by
        rcases heq_map with ⟨h1, _⟩ | ⟨h1, _⟩
        · dsimp only at h1
          exact ConnectedComponent.eq_of_common_vertex hu₁ (h1 ▸ hu₂)
        · dsimp only at h1
          exact ConnectedComponent.eq_of_common_vertex hu₁ (h1 ▸ hv₂)
      subst hc_eq
      congr 1
      apply Subtype.ext
      rw [Sym2.eq_iff]
      rcases heq_map with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨Subtype.ext h1, Subtype.ext h2⟩
      · exact Or.inr ⟨Subtype.ext h1, Subtype.ext h2⟩
    have hfsurj : Function.Surjective f := by
      rintro ⟨e, he⟩
      obtain ⟨u, v, rfl⟩ : ∃ u v : W, e = s(u, v) := Sym2.ind (fun u v => ⟨u, v, rfl⟩) e
      have hadj : H.Adj u v := (H.mem_edgeSet).mp he
      let c := H.connectedComponentMk u
      have hu : u ∈ c.supp := rfl
      have hv : v ∈ c.supp := (ConnectedComponent.mem_supp_congr_adj c hadj).mp hu
      have he' : s(⟨u, hu⟩, ⟨v, hv⟩) ∈ c.toSimpleGraph.edgeSet := by
        rw [c.toSimpleGraph.mem_edgeSet]
        exact hadj
      refine ⟨⟨c, ⟨s(⟨u, hu⟩, ⟨v, hv⟩), he'⟩⟩, ?_⟩
      apply Subtype.ext
      dsimp only [f]
      rw [Sym2.map_mk]
    let Esum : ℕ := ∑ c : H.ConnectedComponent, Fintype.card c.toSimpleGraph.edgeSet
    have hsum_edges : Esum = H.edgeFinset.card := by
      dsimp only [Esum]
      rw [← Fintype.card_sigma, ← H.card_edgeSet]
      exact Fintype.card_of_bijective ⟨hfinj, hfsurj⟩
    have hv_eq : (∑ c : H.ConnectedComponent, Fintype.card c) = Fintype.card W := by
      rw [← Fintype.card_sigma]
      refine Fintype.card_congr
        ⟨fun ⟨_, ⟨w, _⟩⟩ => w, fun w => ⟨H.connectedComponentMk w, ⟨w, rfl⟩⟩, ?_, ?_⟩
      · rintro ⟨c, ⟨w, hw⟩⟩
        have hcw : H.connectedComponentMk w = c := (ConnectedComponent.mem_supp_iff c w).mp hw
        subst hcw
        rfl
      · intro w
        rfl
    have htree_sum : Esum + Fintype.card H.ConnectedComponent = Fintype.card W := by
      calc
        Esum + Fintype.card H.ConnectedComponent
          = ∑ c : H.ConnectedComponent, (Fintype.card c.toSimpleGraph.edgeSet + 1) := by
            dsimp only [Esum]
            rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one]
        _ = ∑ c : H.ConnectedComponent, Fintype.card c := by
            refine Finset.sum_congr rfl fun c _ => ?_
            rw [c.toSimpleGraph.card_edgeSet]
            exact (hHA.isTree_connectedComponent c).card_edgeFinset
        _ = Fintype.card W := hv_eq
    have hcc_le : Fintype.card H.ConnectedComponent ≤ 1 := by omega
    have hss : Subsingleton H.ConnectedComponent :=
      Fintype.card_le_one_iff_subsingleton.mp hcc_le
    have : Nonempty W := Fintype.card_pos_iff.mp (by omega)
    exact Connected.mk fun u v =>
      ConnectedComponent.exact (Subsingleton.elim (H.connectedComponentMk u) (H.connectedComponentMk v))
  exact ⟨⟨hHC, hHA⟩, hdeg⟩

end KellyRecognition

theorem main : H1 → H2 → H3 → H4 → type_of% @ReconstructionConjecture.reconstruction_conjecture.variants.tree := by
  intro h1 h2 h3 h4 V W _ _ hV G H hc ha h
  obtain ⟨σ, hσ⟩ := h
  obtain ⟨hTH, hdeg⟩ := kelly_tree_recognition hV G H ⟨hc, ha⟩ σ hσ
  have hcard : Fintype.card V = Fintype.card W := Fintype.card_congr σ
  by_cases hpath : ∀ v : V, (G.neighborSet v).ncard ≤ 2
  · have hpathH : ∀ w : W, (H.neighborSet w).ncard ≤ 2 := by
      intro w
      rw [← σ.apply_symm_apply w, ← hdeg (σ.symm w)]
      exact hpath (σ.symm w)
    exact h1 hV hcard G H ⟨hc, ha⟩ hTH hpath hpathH
  · push Not at hpath
    have hsub : ∀ (U : Type) [Fintype U] (Q : SimpleGraph U),
        Fintype.card U < Fintype.card V →
        {S : Finset V | Nonempty (G.induce (S : Set V) ≃g Q)}.ncard =
          {T : Finset W | Nonempty (H.induce (T : Set W) ≃g Q)}.ncard :=
      h2 hV G H ⟨hc, ha⟩ hTH ⟨σ, hσ⟩
    rcases Nat.even_or_odd G.diam with heven | hodd
    · exact h3 hV G H σ ⟨hc, ha⟩ hTH hσ hdeg hpath heven hsub
    · exact h4 hV G H σ ⟨hc, ha⟩ hTH hσ hdeg hpath hodd hsub

end OMA.R_ReconstructionConjecture_reconstruction_conjecture_variants_tree_R1


/-
Reduction `ReconstructionConjecture.reconstruction_conjecture.variants.tree.R1.H3.R1` of the central
(even diameter) non-path tree case of Kelly's theorem (`H3` of `tree.R1`). Proves the radius-1
star case in-file and splits the remainder into four modular subgoals:
1. `H1`: Diameter equality and unique center existence (`G.diam = H.diam = 2 * r`, `r >= 1`).
2. `H2`: Center degree equality and singleton-limb elimination (for `r >= 2`).
3. `H3`: Isomorphism when every center component has cardinality at most `r`.
4. `H4`: Isomorphism when some center component has cardinality strictly greater than `r`.
-/

-- Reduction ReconstructionConjecture.reconstruction_conjecture.variants.tree.R1.H3.R1
-- Credit: @green-notes

namespace OMA.R_ReconstructionConjecture_reconstruction_conjecture_variants_tree_R1_H3_R1

open SimpleGraph

def H1 : Prop :=
  ∀ {V W : Type} [Fintype V] [Fintype W],
    3 ≤ Fintype.card V →
    ∀ (G : SimpleGraph V) (H : SimpleGraph W) (σ : V ≃ W),
      G.IsTree → H.IsTree →
      (∀ v : V, Nonempty (G.induce {v}ᶜ ≃g H.induce {σ v}ᶜ)) →
      (∀ v : V, (G.neighborSet v).ncard = (H.neighborSet (σ v)).ncard) →
      (∃ v : V, 3 ≤ (G.neighborSet v).ncard) →
      Even G.diam →
      (∀ (U : Type) [Fintype U] (Q : SimpleGraph U),
        Fintype.card U < Fintype.card V →
        {S : Finset V | Nonempty (G.induce (S : Set V) ≃g Q)}.ncard =
          {T : Finset W | Nonempty (H.induce (T : Set W) ≃g Q)}.ncard) →
      ∃ (r : ℕ) (cG : V) (cH : W),
        1 ≤ r ∧ G.diam = 2 * r ∧ H.diam = 2 * r ∧
        G.eccent cG = r ∧ H.eccent cH = r ∧
        (∀ v : V, v ≠ cG → (r : ℕ∞) < G.eccent v) ∧
        (∀ w : W, w ≠ cH → (r : ℕ∞) < H.eccent w)

def H2 : Prop :=
  ∀ {V W : Type} [Fintype V] [Fintype W],
    3 ≤ Fintype.card V →
    ∀ (G : SimpleGraph V) (H : SimpleGraph W) (σ : V ≃ W),
      G.IsTree → H.IsTree →
      (∀ v : V, Nonempty (G.induce {v}ᶜ ≃g H.induce {σ v}ᶜ)) →
      (∀ v : V, (G.neighborSet v).ncard = (H.neighborSet (σ v)).ncard) →
      (∃ v : V, 3 ≤ (G.neighborSet v).ncard) →
      ∀ (r : ℕ) (cG : V) (cH : W),
        2 ≤ r → G.diam = 2 * r → H.diam = 2 * r →
        G.eccent cG = r → H.eccent cH = r →
        (∀ v : V, v ≠ cG → (r : ℕ∞) < G.eccent v) →
        (∀ w : W, w ≠ cH → (r : ℕ∞) < H.eccent w) →
        (∀ (U : Type) [Fintype U] (Q : SimpleGraph U),
          Fintype.card U < Fintype.card V →
          {S : Finset V | Nonempty (G.induce (S : Set V) ≃g Q)}.ncard =
            {T : Finset W | Nonempty (H.induce (T : Set W) ≃g Q)}.ncard) →
        Nonempty (G ≃g H) ∨
          ((G.neighborSet cG).ncard = (H.neighborSet cH).ncard ∧
            (∀ v : V, G.Adj cG v → 2 ≤ (G.neighborSet v).ncard) ∧
            (∀ w : W, H.Adj cH w → 2 ≤ (H.neighborSet w).ncard))

def H3 : Prop :=
  ∀ {V W : Type} [Fintype V] [Fintype W],
    3 ≤ Fintype.card V →
    ∀ (G : SimpleGraph V) (H : SimpleGraph W) (σ : V ≃ W),
      G.IsTree → H.IsTree →
      (∀ v : V, Nonempty (G.induce {v}ᶜ ≃g H.induce {σ v}ᶜ)) →
      (∀ v : V, (G.neighborSet v).ncard = (H.neighborSet (σ v)).ncard) →
      (∃ v : V, 3 ≤ (G.neighborSet v).ncard) →
      ∀ (r : ℕ) (cG : V) (cH : W),
        2 ≤ r → G.diam = 2 * r → H.diam = 2 * r →
        G.eccent cG = r → H.eccent cH = r →
        (∀ v : V, v ≠ cG → (r : ℕ∞) < G.eccent v) →
        (∀ w : W, w ≠ cH → (r : ℕ∞) < H.eccent w) →
        (∀ (U : Type) [Fintype U] (Q : SimpleGraph U),
          Fintype.card U < Fintype.card V →
          {S : Finset V | Nonempty (G.induce (S : Set V) ≃g Q)}.ncard =
            {T : Finset W | Nonempty (H.induce (T : Set W) ≃g Q)}.ncard) →
        (G.neighborSet cG).ncard = (H.neighborSet cH).ncard →
        (∀ v : V, G.Adj cG v → 2 ≤ (G.neighborSet v).ncard) →
        (∀ w : W, H.Adj cH w → 2 ≤ (H.neighborSet w).ncard) →
        (∀ C : (G.induce {cG}ᶜ).ConnectedComponent, C.supp.ncard ≤ r) →
        (∀ D : (H.induce {cH}ᶜ).ConnectedComponent, D.supp.ncard ≤ r) →
        Nonempty (G ≃g H)

def H4 : Prop :=
  ∀ {V W : Type} [Fintype V] [Fintype W],
    3 ≤ Fintype.card V →
    ∀ (G : SimpleGraph V) (H : SimpleGraph W) (σ : V ≃ W),
      G.IsTree → H.IsTree →
      (∀ v : V, Nonempty (G.induce {v}ᶜ ≃g H.induce {σ v}ᶜ)) →
      (∀ v : V, (G.neighborSet v).ncard = (H.neighborSet (σ v)).ncard) →
      (∃ v : V, 3 ≤ (G.neighborSet v).ncard) →
      ∀ (r : ℕ) (cG : V) (cH : W),
        2 ≤ r → G.diam = 2 * r → H.diam = 2 * r →
        G.eccent cG = r → H.eccent cH = r →
        (∀ v : V, v ≠ cG → (r : ℕ∞) < G.eccent v) →
        (∀ w : W, w ≠ cH → (r : ℕ∞) < H.eccent w) →
        (∀ (U : Type) [Fintype U] (Q : SimpleGraph U),
          Fintype.card U < Fintype.card V →
          {S : Finset V | Nonempty (G.induce (S : Set V) ≃g Q)}.ncard =
            {T : Finset W | Nonempty (H.induce (T : Set W) ≃g Q)}.ncard) →
        (G.neighborSet cG).ncard = (H.neighborSet cH).ncard →
        (∀ v : V, G.Adj cG v → 2 ≤ (G.neighborSet v).ncard) →
        (∀ w : W, H.Adj cH w → 2 ≤ (H.neighborSet w).ncard) →
        ((∃ C : (G.induce {cG}ᶜ).ConnectedComponent, r < C.supp.ncard) ∨
          (∃ D : (H.induce {cH}ᶜ).ConnectedComponent, r < D.supp.ncard)) →
        Nonempty (G ≃g H)

section StarRadiusOne

open Classical

private lemma adj_iff_center_of_eccent_one {U : Type} (T : SimpleGraph U) (hT : T.IsTree)
    (c : U) (hecc : T.eccent c = 1) (a b : U) :
    T.Adj a b ↔ (a = c ∧ b ≠ c) ∨ (b = c ∧ a ≠ c) := by
  have hadj : ∀ x : U, c ≠ x → T.Adj c x := (T.eccent_le_one_iff c).mp hecc.le
  constructor
  · intro hab
    by_cases hac : a = c
    · exact Or.inl ⟨hac, fun hbc => T.ne_of_adj hab (hac.trans hbc.symm)⟩
    · by_cases hbc : b = c
      · exact Or.inr ⟨hbc, hac⟩
      · have h1 : T.dist c a = 1 := dist_eq_one_iff_adj.mpr (hadj a (Ne.symm hac))
        have h2 : T.dist c b = 1 := dist_eq_one_iff_adj.mpr (hadj b (Ne.symm hbc))
        exact False.elim (hT.dist_ne_of_adj c hab (h1.trans h2.symm))
  · rintro (⟨rfl, hbc⟩ | ⟨rfl, hac⟩)
    · exact hadj b (Ne.symm hbc)
    · exact (hadj a (Ne.symm hac)).symm

private lemma iso_of_eccent_one {V W : Type} (G : SimpleGraph V) (H : SimpleGraph W)
    (σ : V ≃ W) (hTG : G.IsTree) (hTH : H.IsTree) (cG : V) (cH : W)
    (heccG : G.eccent cG = 1) (heccH : H.eccent cH = 1) :
    Nonempty (G ≃g H) := by
  classical
  let τ : V ≃ W := σ.trans (Equiv.swap (σ cG) cH)
  have hτc : τ cG = cH := by simp [τ]
  refine ⟨⟨τ, ?_⟩⟩
  intro a b
  rw [adj_iff_center_of_eccent_one H hTH cH heccH,
      adj_iff_center_of_eccent_one G hTG cG heccG]
  have ha : τ a = cH ↔ a = cG := by
    rw [← hτc]
    exact τ.apply_eq_iff_eq
  have hb : τ b = cH ↔ b = cG := by
    rw [← hτc]
    exact τ.apply_eq_iff_eq
  simp only [ne_eq, ha, hb]

end StarRadiusOne

theorem main : H1 → H2 → H3 → H4 → OMA.R_ReconstructionConjecture_reconstruction_conjecture_variants_tree_R1.H3 := by
  intro h1 h2 h3 h4 V W _ _ hV G H σ hTG hTH hσ hdeg hnonpath heven hsub
  obtain ⟨r, cG, cH, hr1, hdiamG, hdiamH, heccG, heccH, huG, huH⟩ :=
    h1 hV G H σ hTG hTH hσ hdeg hnonpath heven hsub
  by_cases hr2 : 2 ≤ r
  · rcases h2 hV G H σ hTG hTH hσ hdeg hnonpath r cG cH hr2 hdiamG hdiamH heccG heccH huG huH hsub with
      hiso | ⟨hdegc, hnoleafG, hnoleafH⟩
    · exact hiso
    · by_cases hG : ∃ C : (G.induce {cG}ᶜ).ConnectedComponent, r < C.supp.ncard
      · exact h4 hV G H σ hTG hTH hσ hdeg hnonpath r cG cH hr2 hdiamG hdiamH heccG heccH huG huH hsub
          hdegc hnoleafG hnoleafH (Or.inl hG)
      · by_cases hH : ∃ D : (H.induce {cH}ᶜ).ConnectedComponent, r < D.supp.ncard
        · exact h4 hV G H σ hTG hTH hσ hdeg hnonpath r cG cH hr2 hdiamG hdiamH heccG heccH huG huH hsub
            hdegc hnoleafG hnoleafH (Or.inr hH)
        · exact h3 hV G H σ hTG hTH hσ hdeg hnonpath r cG cH hr2 hdiamG hdiamH heccG heccH huG huH hsub
            hdegc hnoleafG hnoleafH
            (fun C => Nat.le_of_not_lt fun hlt => hG ⟨C, hlt⟩)
            (fun D => Nat.le_of_not_lt fun hlt => hH ⟨D, hlt⟩)
  · have hr_eq : r = 1 := by omega
    subst hr_eq
    simp only [Nat.cast_one] at heccG heccH
    exact iso_of_eccent_one G H σ hTG hTH cG cH heccG heccH

end OMA.R_ReconstructionConjecture_reconstruction_conjecture_variants_tree_R1_H3_R1


-- Reduction ReconstructionConjecture.reconstruction_conjecture.variants.tree.R1.H4.R1 of step ReconstructionConjecture.reconstruction_conjecture.variants.tree.R1.H4
-- Credit: @green-notes

/-
Splits the bicentral (odd-diameter) non-path tree reconstruction step `tree.R1.H4` into four
independent mathematical subgoals:
1. `H1`: Diameter preservation (`3 ≤ G.diam` and `G.diam = H.diam`) for non-path hypomorphic trees
   via Kelly's subgraph-counting hypothesis on a diametral path.
2. `H2`: Jordan's bicenter decomposition for any finite tree of odd diameter `2 * r + 1 ≥ 3`:
   existence of the central edge `{c₁, c₂} = T.center`, metric partition into two trees of height
   at most `r`, and distance factorization across `{c₁, c₂}`.
3. `H3`: Kelly's non-path-limb reconstruction when all four central limbs have size `≥ r + 2`
   (counting induced subtrees of diameter `2 * r + 1` with one limb a path of length `r`).
4. `H4`: Kelly's path-limb reconstruction when at least one central limb has size `≤ r + 1`
   (i.e. is a path of length `r`).
-/

namespace OMA.R_ReconstructionConjecture_reconstruction_conjecture_variants_tree_R1_H4_R1

open SimpleGraph ReconstructionConjecture

def H1 : Prop :=
  ∀ {V W : Type} [Fintype V] [Fintype W],
    3 ≤ Fintype.card V →
    ∀ (G : SimpleGraph V) (H : SimpleGraph W) (σ : V ≃ W),
      G.IsTree → H.IsTree →
      (∀ v : V, (G.neighborSet v).ncard = (H.neighborSet (σ v)).ncard) →
      (∃ v : V, 3 ≤ (G.neighborSet v).ncard) →
      Odd G.diam →
      (∀ (U : Type) [Fintype U] (Q : SimpleGraph U),
        Fintype.card U < Fintype.card V →
        {S : Finset V | Nonempty (G.induce (S : Set V) ≃g Q)}.ncard =
          {T : Finset W | Nonempty (H.induce (T : Set W) ≃g Q)}.ncard) →
      3 ≤ G.diam ∧ G.diam = H.diam

def H2 : Prop :=
  ∀ {U : Type} [Fintype U] (T : SimpleGraph U),
    T.IsTree → 3 ≤ T.diam → Odd T.diam →
    ∃ c₁ c₂ : U, T.Adj c₁ c₂ ∧
      T.center = {c₁, c₂} ∧
      (∀ x : U, T.dist x c₁ ≠ T.dist x c₂) ∧
      (∀ x : U, T.dist x c₁ < T.dist x c₂ → T.dist x c₁ ≤ (T.diam - 1) / 2) ∧
      (∀ x : U, T.dist x c₂ < T.dist x c₁ → T.dist x c₂ ≤ (T.diam - 1) / 2) ∧
      (T.induce {x : U | T.dist x c₁ < T.dist x c₂}).IsTree ∧
      (T.induce {x : U | T.dist x c₂ < T.dist x c₁}).IsTree ∧
      (∀ x y : U, T.dist x c₁ < T.dist x c₂ → T.dist y c₂ < T.dist y c₁ →
        T.dist x y = T.dist x c₁ + 1 + T.dist c₂ y)

def H3 : Prop :=
  ∀ {V W : Type} [Fintype V] [Fintype W] (G : SimpleGraph V) (H : SimpleGraph W),
    G.IsTree → H.IsTree → Fintype.card V = Fintype.card W →
    ∀ r : ℕ, 1 ≤ r → G.diam = 2 * r + 1 → H.diam = 2 * r + 1 →
      (∀ (U : Type) [Fintype U] (Q : SimpleGraph U),
        Fintype.card U < Fintype.card V →
        {S : Finset V | Nonempty (G.induce (S : Set V) ≃g Q)}.ncard =
          {T : Finset W | Nonempty (H.induce (T : Set W) ≃g Q)}.ncard) →
      ∀ c₁ c₂ : V, G.Adj c₁ c₂ →
        (∀ x : V, G.dist x c₁ ≠ G.dist x c₂) →
        (∀ x : V, G.dist x c₁ < G.dist x c₂ → G.dist x c₁ ≤ r) →
        (∀ x : V, G.dist x c₂ < G.dist x c₁ → G.dist x c₂ ≤ r) →
        (G.induce {x : V | G.dist x c₁ < G.dist x c₂}).IsTree →
        (G.induce {x : V | G.dist x c₂ < G.dist x c₁}).IsTree →
        (∀ x y : V, G.dist x c₁ < G.dist x c₂ → G.dist y c₂ < G.dist y c₁ →
          G.dist x y = G.dist x c₁ + 1 + G.dist c₂ y) →
        r + 2 ≤ {x : V | G.dist x c₁ < G.dist x c₂}.ncard →
        r + 2 ≤ {x : V | G.dist x c₂ < G.dist x c₁}.ncard →
      ∀ d₁ d₂ : W, H.Adj d₁ d₂ →
        (∀ y : W, H.dist y d₁ ≠ H.dist y d₂) →
        (∀ y : W, H.dist y d₁ < H.dist y d₂ → H.dist y d₁ ≤ r) →
        (∀ y : W, H.dist y d₂ < H.dist y d₁ → H.dist y d₂ ≤ r) →
        (H.induce {y : W | H.dist y d₁ < H.dist y d₂}).IsTree →
        (H.induce {y : W | H.dist y d₂ < H.dist y d₁}).IsTree →
        (∀ x y : W, H.dist x d₁ < H.dist x d₂ → H.dist y d₂ < H.dist y d₁ →
          H.dist x y = H.dist x d₁ + 1 + H.dist d₂ y) →
        r + 2 ≤ {y : W | H.dist y d₁ < H.dist y d₂}.ncard →
        r + 2 ≤ {y : W | H.dist y d₂ < H.dist y d₁}.ncard →
      Nonempty (G ≃g H)

def H4 : Prop :=
  ∀ {V W : Type} [Fintype V] [Fintype W],
    3 ≤ Fintype.card V →
    ∀ (G : SimpleGraph V) (H : SimpleGraph W) (σ : V ≃ W),
      G.IsTree → H.IsTree →
      (∀ v : V, Nonempty (G.induce {v}ᶜ ≃g H.induce {σ v}ᶜ)) →
      (∀ v : V, (G.neighborSet v).ncard = (H.neighborSet (σ v)).ncard) →
      (∃ v : V, 3 ≤ (G.neighborSet v).ncard) →
      ∀ r : ℕ, 1 ≤ r → G.diam = 2 * r + 1 → H.diam = 2 * r + 1 →
      (∀ (U : Type) [Fintype U] (Q : SimpleGraph U),
        Fintype.card U < Fintype.card V →
        {S : Finset V | Nonempty (G.induce (S : Set V) ≃g Q)}.ncard =
          {T : Finset W | Nonempty (H.induce (T : Set W) ≃g Q)}.ncard) →
      ∀ c₁ c₂ : V, G.Adj c₁ c₂ → G.center = {c₁, c₂} →
        (∀ x : V, G.dist x c₁ ≠ G.dist x c₂) →
        (∀ x : V, G.dist x c₁ < G.dist x c₂ → G.dist x c₁ ≤ r) →
        (∀ x : V, G.dist x c₂ < G.dist x c₁ → G.dist x c₂ ≤ r) →
        (G.induce {x : V | G.dist x c₁ < G.dist x c₂}).IsTree →
        (G.induce {x : V | G.dist x c₂ < G.dist x c₁}).IsTree →
        (∀ x y : V, G.dist x c₁ < G.dist x c₂ → G.dist y c₂ < G.dist y c₁ →
          G.dist x y = G.dist x c₁ + 1 + G.dist c₂ y) →
      ∀ d₁ d₂ : W, H.Adj d₁ d₂ → H.center = {d₁, d₂} →
        (∀ y : W, H.dist y d₁ ≠ H.dist y d₂) →
        (∀ y : W, H.dist y d₁ < H.dist y d₂ → H.dist y d₁ ≤ r) →
        (∀ y : W, H.dist y d₂ < H.dist y d₁ → H.dist y d₂ ≤ r) →
        (H.induce {y : W | H.dist y d₁ < H.dist y d₂}).IsTree →
        (H.induce {y : W | H.dist y d₂ < H.dist y d₁}).IsTree →
        (∀ x y : W, H.dist x d₁ < H.dist x d₂ → H.dist y d₂ < H.dist y d₁ →
          H.dist x y = H.dist x d₁ + 1 + H.dist d₂ y) →
      ({x : V | G.dist x c₁ < G.dist x c₂}.ncard ≤ r + 1 ∨
       {x : V | G.dist x c₂ < G.dist x c₁}.ncard ≤ r + 1 ∨
       {y : W | H.dist y d₁ < H.dist y d₂}.ncard ≤ r + 1 ∨
       {y : W | H.dist y d₂ < H.dist y d₁}.ncard ≤ r + 1) →
      Nonempty (G ≃g H)

theorem main : H1 → H2 → H3 → H4 → OMA.R_ReconstructionConjecture_reconstruction_conjecture_variants_tree_R1.H4 := by
  intro h1 h2 h3 h4 V W _ _ hV G H σ hTG hTH hσ hdeg hnonpath hodd hkelly
  obtain ⟨hd3, hd_eq⟩ := h1 hV G H σ hTG hTH hdeg hnonpath hodd hkelly
  have hoddH : Odd H.diam := hd_eq ▸ hodd
  have hd3H : 3 ≤ H.diam := hd_eq ▸ hd3
  obtain ⟨c₁, c₂, hc_adj, hc_ctr, hc_ne, hc_le1, hc_le2, hc_t1, hc_t2, hc_dist⟩ :=
    h2 G hTG hd3 hodd
  obtain ⟨d₁, d₂, hd_adj, hd_ctr, hd_ne, hd_le1, hd_le2, hd_t1, hd_t2, hd_dist⟩ :=
    h2 H hTH hd3H hoddH
  set r := (G.diam - 1) / 2
  have hr1 : 1 ≤ r := by omega
  have hGdiam : G.diam = 2 * r + 1 := by
    obtain ⟨k, hk⟩ := hodd
    omega
  have hHdiam : H.diam = 2 * r + 1 := by
    rw [← hd_eq]
    exact hGdiam
  have hr_eqH : (H.diam - 1) / 2 = r := by rw [← hd_eq]
  rw [hr_eqH] at hd_le1 hd_le2
  by_cases hsmall :
      {x : V | G.dist x c₁ < G.dist x c₂}.ncard ≤ r + 1 ∨
      {x : V | G.dist x c₂ < G.dist x c₁}.ncard ≤ r + 1 ∨
      {y : W | H.dist y d₁ < H.dist y d₂}.ncard ≤ r + 1 ∨
      {y : W | H.dist y d₂ < H.dist y d₁}.ncard ≤ r + 1
  · exact h4 hV G H σ hTG hTH hσ hdeg hnonpath r hr1 hGdiam hHdiam hkelly
      c₁ c₂ hc_adj hc_ctr hc_ne hc_le1 hc_le2 hc_t1 hc_t2 hc_dist
      d₁ d₂ hd_adj hd_ctr hd_ne hd_le1 hd_le2 hd_t1 hd_t2 hd_dist hsmall
  · push Not at hsmall
    have hcard : Fintype.card V = Fintype.card W := Fintype.card_congr σ
    exact h3 G H hTG hTH hcard r hr1 hGdiam hHdiam hkelly
      c₁ c₂ hc_adj hc_ne hc_le1 hc_le2 hc_t1 hc_t2 hc_dist (by omega) (by omega)
      d₁ d₂ hd_adj hd_ne hd_le1 hd_le2 hd_t1 hd_t2 hd_dist (by omega) (by omega)

end OMA.R_ReconstructionConjecture_reconstruction_conjecture_variants_tree_R1_H4_R1

namespace KellyStep1

/-
# Path trees (`degree <= 2`) are isomorphic (`tree.R1.H1` offline pre-proof)

Every finite tree on `n + 1` vertices with maximum degree at most `2` has a vertex of degree at
most `1`, and deleting that endpoint gives an inductive isomorphism with the canonical path graph
on `Fin (n + 1)`.
-/

-- Credit: @green-notes

open SimpleGraph

section TreeR1H1

open Classical

private def pathG (n : ℕ) : SimpleGraph (Fin n) where
  Adj i j := i.val + 1 = j.val ∨ j.val + 1 = i.val
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨fun _ h => by omega⟩

private lemma exists_deg_le_one_of_tree {V : Type} [Fintype V] (G : SimpleGraph V)
    (hG : G.IsTree) (_hV : 1 ≤ Fintype.card V) (hdeg : ∀ v : V, G.degree v ≤ 2) :
    ∃ u : V, G.degree u ≤ 1 := by
  by_contra hno
  push Not at hno
  have htwo : ∀ v : V, G.degree v = 2 := fun v => by have := hdeg v; have := hno v; omega
  have hsum := G.sum_degrees_eq_twice_card_edges
  have hcard := hG.card_edgeFinset
  simp only [htwo, Finset.sum_const, Finset.card_univ, smul_eq_mul] at hsum
  omega

private lemma isAcyclic_induce {V : Type*} (G : SimpleGraph V) (hG : G.IsAcyclic) (S : Set V) :
    (G.induce S).IsAcyclic := by
  intro v c hc
  let f : G.induce S →g G := ⟨Subtype.val, fun h => h⟩
  have hf : Function.Injective f := Subtype.val_injective
  exact hG (c.map f) (hc.map hf)

private lemma ncard_neighborSet_eq_degree {U : Type} [Fintype U] (Z : SimpleGraph U) (u : U) :
    (Z.neighborSet u).ncard = Z.degree u := by
  rw [← Z.card_neighborSet_eq_degree, Set.ncard_eq_toFinset_card' (Z.neighborSet u)]
  simp [Set.toFinset_card]

private lemma path_tree_from_end :
    ∀ (n : ℕ) {V : Type} [Fintype V] (G : SimpleGraph V),
      G.IsTree → Fintype.card V = n + 1 → (∀ v : V, G.degree v ≤ 2) →
      ∀ u : V, G.degree u ≤ 1 →
      ∃ φ : G ≃g pathG (n + 1), φ u = 0 := by
  intro n
  induction n with
  | zero =>
    intro V _ G _ hcard _ u _
    have hss : Subsingleton V := Fintype.card_le_one_iff_subsingleton.mp (by omega)
    refine ⟨⟨⟨fun _ => 0, fun _ => u, ?_, ?_⟩, ?_⟩, rfl⟩
    · intro v
      exact Subsingleton.elim u v
    · intro i
      fin_cases i
      rfl
    · intro a b
      have hab : a = b := Subsingleton.elim a b
      subst hab
      simp [pathG]
  | succ n ih =>
    intro V _ G hG hcard hdeg u hu
    have hnt : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
    obtain ⟨w, hwu⟩ := exists_ne u
    obtain ⟨p⟩ := hG.connected.preconnected u w
    have hu_deg1 : G.degree u = 1 := by
      rcases p with _ | ⟨hadj, _⟩
      · exact False.elim (hwu rfl)
      · have hpos : 0 < G.degree u := by
          rw [← G.card_neighborFinset_eq_degree]
          exact Finset.card_pos.mpr ⟨_, (G.mem_neighborFinset u _).mpr hadj⟩
        omega
    obtain ⟨u', huu', hu'_uniq⟩ := SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp hu_deg1
    let V' := ({u}ᶜ : Set V)
    let G' := G.induce V'
    have hV' : Fintype.card V' = n + 1 := by
      have eV' : V' ≃ ↥(Finset.univ.erase u) :=
        ⟨fun x => ⟨x.1, Finset.mem_erase.mpr ⟨x.2, Finset.mem_univ _⟩⟩,
         fun x => ⟨x.1, (Finset.mem_erase.mp x.2).1⟩,
         fun _ => rfl, fun _ => rfl⟩
      rw [Fintype.card_congr eV', Fintype.card_coe, Finset.card_erase_of_mem (Finset.mem_univ u),
        Finset.card_univ, hcard]
      omega
    have hconn' : G'.Connected :=
      hG.connected.induce_compl_singleton_of_degree_eq_one hu_deg1
    have hG' : G'.IsTree := ⟨hconn', isAcyclic_induce G hG.isAcyclic V'⟩
    have hsub (x : V') :
        (G'.neighborFinset x).map ⟨Subtype.val, Subtype.val_injective⟩ ⊆ G.neighborFinset x.1 := by
      intro y hy
      rw [Finset.mem_map] at hy
      obtain ⟨z, hz, rfl⟩ := hy
      rw [SimpleGraph.mem_neighborFinset] at hz ⊢
      exact hz
    have hdeg' (x : V') : G'.degree x ≤ 2 := by
      have hc : G'.degree x ≤ G.degree x.1 := by
        rw [← G'.card_neighborFinset_eq_degree, ← G.card_neighborFinset_eq_degree,
          ← Finset.card_map ⟨Subtype.val, Subtype.val_injective⟩]
        exact Finset.card_le_card (hsub x)
      exact hc.trans (hdeg x.1)
    have hu'u : u' ∈ V' := huu'.ne.symm
    let x₀ : V' := ⟨u', hu'u⟩
    have hx₀_deg : G'.degree x₀ ≤ 1 := by
      have hunot : u ∉ (G'.neighborFinset x₀).map ⟨Subtype.val, Subtype.val_injective⟩ := by
        intro h
        rw [Finset.mem_map] at h
        obtain ⟨z, _, hzu⟩ := h
        exact z.2 hzu
      have hins :
          insert u ((G'.neighborFinset x₀).map ⟨Subtype.val, Subtype.val_injective⟩) ⊆
            G.neighborFinset u' := by
        intro y hy
        rcases Finset.mem_insert.mp hy with hyu | hy'
        · subst hyu
          rw [SimpleGraph.mem_neighborFinset]
          exact huu'.symm
        · exact hsub x₀ hy'
      have hc := Finset.card_le_card hins
      rw [Finset.card_insert_of_notMem hunot, Finset.card_map,
        G'.card_neighborFinset_eq_degree, G.card_neighborFinset_eq_degree] at hc
      have := hdeg u'
      omega
    obtain ⟨φ', hφ0⟩ := ih G' hG' hV' hdeg' x₀ hx₀_deg
    let toF : V → Fin (n + 2) := fun v => if hv : v = u then 0 else (φ' ⟨v, hv⟩).succ
    let invF : Fin (n + 2) → V := Fin.cases u (fun j => (φ'.symm j).val)
    have hleft : Function.LeftInverse invF toF := by
      intro v
      dsimp only [toF, invF]
      by_cases hv : v = u
      · subst hv
        simp
      · rw [dif_neg hv]
        simp
    have hright : Function.RightInverse invF toF := by
      intro i
      dsimp only [toF, invF]
      induction i using Fin.cases with
      | zero => simp
      | succ j =>
        have hne : (φ'.symm j).val ≠ u := (φ'.symm j).2
        simp [hne]
    refine ⟨⟨⟨toF, invF, hleft, hright⟩, ?_⟩, ?_⟩
    · intro a b
      dsimp only [Equiv.coe_fn_mk, toF]
      by_cases ha : a = u <;> by_cases hb : b = u
      · subst ha; subst hb
        simp [pathG]
      · subst ha
        rw [dif_pos rfl, dif_neg hb]
        constructor
        · intro hadj
          have h0 : φ' ⟨b, hb⟩ = 0 := by
            change (0 : Fin (n + 2)).val + 1 = (φ' ⟨b, hb⟩).succ.val ∨
                (φ' ⟨b, hb⟩).succ.val + 1 = (0 : Fin (n + 2)).val at hadj
            simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, Fin.val_succ] at hadj
            apply Fin.ext
            rw [Fin.val_zero]
            omega
          have hbx : (⟨b, hb⟩ : V') = x₀ := φ'.injective (h0.trans hφ0.symm)
          have hbu : b = u' := congrArg Subtype.val hbx
          subst hbu
          exact huu'
        · intro hadj
          have hbu : b = u' := hu'_uniq b hadj
          have hbx : (⟨b, hb⟩ : V') = x₀ := Subtype.ext hbu
          have h0 : φ' ⟨b, hb⟩ = 0 := (congrArg φ' hbx).trans hφ0
          rw [h0]
          simp [pathG]
      · subst hb
        rw [dif_neg ha, dif_pos rfl]
        constructor
        · intro hadj
          have h0 : φ' ⟨a, ha⟩ = 0 := by
            change (φ' ⟨a, ha⟩).succ.val + 1 = (0 : Fin (n + 2)).val ∨
                (0 : Fin (n + 2)).val + 1 = (φ' ⟨a, ha⟩).succ.val at hadj
            simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, Fin.val_succ] at hadj
            apply Fin.ext
            rw [Fin.val_zero]
            omega
          have hax : (⟨a, ha⟩ : V') = x₀ := φ'.injective (h0.trans hφ0.symm)
          have hau : a = u' := congrArg Subtype.val hax
          subst hau
          exact huu'.symm
        · intro hadj
          have hau : a = u' := hu'_uniq a hadj.symm
          have hax : (⟨a, ha⟩ : V') = x₀ := Subtype.ext hau
          have h0 : φ' ⟨a, ha⟩ = 0 := (congrArg φ' hax).trans hφ0
          rw [h0]
          simp [pathG]
      · rw [dif_neg ha, dif_neg hb]
        have hstep : (pathG (n + 2)).Adj (φ' ⟨a, ha⟩).succ (φ' ⟨b, hb⟩).succ ↔
            (pathG (n + 1)).Adj (φ' ⟨a, ha⟩) (φ' ⟨b, hb⟩) := by
          simp only [pathG, Fin.val_succ]
          omega
        exact hstep.trans (φ'.map_rel_iff (a := ⟨a, ha⟩) (b := ⟨b, hb⟩))
    · dsimp only [RelIso.coe_fn_mk, Equiv.coe_fn_mk, toF]
      exact dif_pos rfl

private lemma tree_R1_H1 :
    ∀ {V W : Type} [Fintype V] [Fintype W],
      3 ≤ Fintype.card V → Fintype.card V = Fintype.card W →
      ∀ (G : SimpleGraph V) (H : SimpleGraph W),
        G.IsTree → H.IsTree →
        (∀ v : V, (G.neighborSet v).ncard ≤ 2) →
        (∀ w : W, (H.neighborSet w).ncard ≤ 2) →
        Nonempty (G ≃g H) := by
  intro V W _ _ hV hVW G H hG hH hdegG hdegH
  obtain ⟨m, hm⟩ : ∃ m : ℕ, Fintype.card V = m + 1 := ⟨Fintype.card V - 1, by omega⟩
  have hmW : Fintype.card W = m + 1 := hVW.symm.trans hm
  have hdegG' : ∀ v : V, G.degree v ≤ 2 := fun v => by
    rw [← ncard_neighborSet_eq_degree]
    exact hdegG v
  have hdegH' : ∀ w : W, H.degree w ≤ 2 := fun w => by
    rw [← ncard_neighborSet_eq_degree]
    exact hdegH w
  obtain ⟨uG, huG⟩ := exists_deg_le_one_of_tree G hG (by omega) hdegG'
  obtain ⟨uH, huH⟩ := exists_deg_le_one_of_tree H hH (by omega) hdegH'
  obtain ⟨φG, _⟩ := path_tree_from_end m G hG hm hdegG' uG huG
  obtain ⟨φH, _⟩ := path_tree_from_end m H hH hmW hdegH' uH huH
  exact ⟨φG.trans φH.symm⟩

end TreeR1H1

theorem result : OMA.R_ReconstructionConjecture_reconstruction_conjecture_variants_tree_R1.H1 := by
  exact tree_R1_H1

end KellyStep1

namespace KellyStep2

/-
# Kelly's Lemma for hypomorphic graphs (`tree.R1.H2` offline pre-proof)

Double-counting occurrences of an induced subgraph isomorphic to `Q` across all vertex-deleted
subgraphs gives `(card V - card U) * s(Q, G) = ∑ v, s(Q, G - v)`, which implies equality when
`G` and `H` are hypomorphic and `card U < card V`.
-/

-- Credit: @green-notes

open SimpleGraph ReconstructionConjecture

section TreeR1H2

open Classical

private noncomputable def subgraphs {V U : Type} [Fintype V] [Fintype U]
    (G : SimpleGraph V) (Q : SimpleGraph U) : Finset (Finset V) :=
  Finset.univ.filter fun S : Finset V => Nonempty (G.induce (S : Set V) ≃g Q)

private lemma ncard_subgraphs_eq {V U : Type} [Fintype V] [Fintype U]
    (G : SimpleGraph V) (Q : SimpleGraph U) :
    {S : Finset V | Nonempty (G.induce (S : Set V) ≃g Q)}.ncard = (subgraphs G Q).card := by
  have h : {S : Finset V | Nonempty (G.induce (S : Set V) ≃g Q)} =
      ((subgraphs G Q : Finset (Finset V)) : Set (Finset V)) := by
    ext S
    simp [subgraphs]
  rw [h, Set.ncard_coe_finset]

private noncomputable def induce_iso_map {A B : Type*} {GA : SimpleGraph A} {GB : SimpleGraph B}
    (φ : GA ≃g GB) (S : Finset A) :
    (GA.induce (S : Set A)) ≃g
      (GB.induce ((S.map φ.toEquiv.toEmbedding : Finset B) : Set B)) where
  toFun x := ⟨φ x.1, Finset.mem_coe.mpr (Finset.mem_map.mpr ⟨x.1, Finset.mem_coe.mp x.2, rfl⟩)⟩
  invFun y :=
    ⟨φ.symm y.1, by
      obtain ⟨a, ha, hfa⟩ := Finset.mem_map.mp (Finset.mem_coe.mp y.2)
      have ha' : φ.symm y.1 = a := by
        have h := congrArg φ.symm hfa
        simpa using h.symm
      rw [Finset.mem_coe, ha']
      exact ha⟩
  left_inv x := Subtype.ext (φ.symm_apply_apply x.1)
  right_inv y := Subtype.ext (φ.apply_symm_apply y.1)
  map_rel_iff' := @fun x₁ x₂ => φ.map_rel_iff

private lemma subgraphs_card_eq_of_iso {A B U : Type} [Fintype A] [Fintype B] [Fintype U]
    {GA : SimpleGraph A} {GB : SimpleGraph B} (φ : GA ≃g GB) (Q : SimpleGraph U) :
    (subgraphs GA Q).card = (subgraphs GB Q).card := by
  refine Finset.card_bij (fun S _ => S.map φ.toEquiv.toEmbedding) ?_ ?_ ?_
  · intro S hS
    simp only [subgraphs, Finset.mem_filter, Finset.mem_univ, true_and] at hS ⊢
    obtain ⟨e⟩ := hS
    exact ⟨(induce_iso_map φ S).symm.trans e⟩
  · intro S₁ _ S₂ _ h
    ext a
    have hm := Finset.ext_iff.mp h (φ a)
    simp only [Finset.mem_map, RelIso.coe_fn_toEquiv, Equiv.coe_toEmbedding] at hm
    constructor <;> intro ha
    · obtain ⟨b, hb, hba⟩ := hm.mp ⟨a, ha, rfl⟩
      exact (φ.injective hba) ▸ hb
    · obtain ⟨b, hb, hba⟩ := hm.mpr ⟨a, ha, rfl⟩
      exact (φ.injective hba) ▸ hb
  · intro T hT
    simp only [subgraphs, Finset.mem_filter, Finset.mem_univ, true_and] at hT
    obtain ⟨e⟩ := hT
    refine ⟨T.map φ.symm.toEquiv.toEmbedding, ?_, ?_⟩
    · simp only [subgraphs, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨(induce_iso_map φ.symm T).symm.trans e⟩
    · ext b
      rw [Finset.mem_map]
      constructor
      · rintro ⟨a, ha, hba⟩
        rw [Finset.mem_map] at ha
        obtain ⟨b', hb', hbb'⟩ := ha
        have heq : b' = b := by
          have h := congrArg φ hbb'
          simpa using h.trans hba
        exact heq ▸ hb'
      · intro hb
        exact ⟨φ.symm b, Finset.mem_map.mpr ⟨b, hb, rfl⟩, by simp⟩

private noncomputable def induce_compl_iso_map {V : Type*} (G : SimpleGraph V) (v : V)
    (T : Finset ({v}ᶜ : Set V)) :
    (G.induce {v}ᶜ).induce (T : Set ({v}ᶜ : Set V)) ≃g
      G.induce ((T.map ⟨Subtype.val, Subtype.val_injective⟩ : Finset V) : Set V) where
  toFun x := ⟨x.1.1, Finset.mem_coe.mpr (Finset.mem_map.mpr ⟨x.1, Finset.mem_coe.mp x.2, rfl⟩)⟩
  invFun y :=
    let hy := Finset.mem_map.mp (Finset.mem_coe.mp y.2)
    ⟨hy.choose, Finset.mem_coe.mpr hy.choose_spec.1⟩
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    have hy := Finset.mem_map.mp (Finset.mem_coe.mp
      (Finset.mem_coe.mpr (Finset.mem_map.mpr ⟨x.1, Finset.mem_coe.mp x.2, rfl⟩) :
        x.1.1 ∈ ((T.map ⟨Subtype.val, Subtype.val_injective⟩ : Finset V) : Set V)))
    exact hy.choose_spec.2
  right_inv y := by
    apply Subtype.ext
    have hy := Finset.mem_map.mp (Finset.mem_coe.mp y.2)
    exact hy.choose_spec.2
  map_rel_iff' := @fun x₁ x₂ => by
    rfl

private lemma induced_count_identity {V U : Type} [Fintype V] [Fintype U]
    (G : SimpleGraph V) (Q : SimpleGraph U) :
    (subgraphs G Q).card * (Fintype.card V - Fintype.card U) =
      ∑ v : V, (subgraphs (G.induce {v}ᶜ) Q).card := by
  have hL : (subgraphs G Q).card * (Fintype.card V - Fintype.card U) =
      ((subgraphs G Q).sigma fun S : Finset V => Sᶜ).card := by
    rw [Finset.card_sigma]
    refine (Finset.sum_const_nat fun S hS => ?_).symm
    simp only [subgraphs, Finset.mem_filter, Finset.mem_univ, true_and] at hS
    obtain ⟨e⟩ := hS
    have hcardS : S.card = Fintype.card U :=
      (Fintype.card_coe S).symm.trans (Fintype.card_congr e.toEquiv)
    rw [Finset.card_compl, hcardS]
  have hR : ∑ v : V, (subgraphs (G.induce {v}ᶜ) Q).card =
      ((Finset.univ : Finset V).sigma fun v : V => subgraphs (G.induce {v}ᶜ) Q).card := by
    rw [Finset.card_sigma]
  rw [hL, hR]
  refine Finset.card_bij
    (fun ⟨S, v⟩ _ => ⟨v, Finset.univ.filter fun x : ({v}ᶜ : Set V) => x.1 ∈ S⟩) ?_ ?_ ?_
  · rintro ⟨S, v⟩ hsv
    simp only [subgraphs, Finset.mem_sigma, Finset.mem_compl, Finset.mem_filter,
      Finset.mem_univ, true_and] at hsv ⊢
    rcases hsv with ⟨⟨e⟩, hvS⟩
    refine ⟨?_⟩
    let T : Finset ({v}ᶜ : Set V) := Finset.univ.filter fun x : ({v}ᶜ : Set V) => x.1 ∈ S
    have hTS : T.map ⟨Subtype.val, Subtype.val_injective⟩ = S := by
      ext y
      simp only [T, Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
        Function.Embedding.coeFn_mk]
      constructor
      · rintro ⟨⟨z, _⟩, hzS, rfl⟩
        exact hzS
      · intro hyS
        have hyv : y ∈ ({v}ᶜ : Set V) := fun h => hvS (h ▸ hyS)
        exact ⟨⟨y, hyv⟩, hyS, rfl⟩
    refine (induce_compl_iso_map G v T).trans ?_
    rw [hTS]
    exact e
  · rintro ⟨S₁, v₁⟩ h1 ⟨S₂, v₂⟩ h2 heq
    rw [Finset.mem_sigma, Finset.mem_compl] at h1 h2
    have hv : v₁ = v₂ := congrArg Sigma.fst heq
    subst hv
    have hT : (Finset.univ.filter fun x : ({v₁}ᶜ : Set V) => x.1 ∈ S₁) =
        Finset.univ.filter fun x : ({v₁}ᶜ : Set V) => x.1 ∈ S₂ :=
      eq_of_heq (Sigma.ext_iff.mp heq).2
    have hS : S₁ = S₂ := by
      ext y
      by_cases hy : y = v₁
      · subst hy
        exact ⟨fun h => False.elim (h1.2 h), fun h => False.elim (h2.2 h)⟩
      · have hm := Finset.ext_iff.mp hT ⟨y, hy⟩
        simpa using hm
    subst hS
    rfl
  · rintro ⟨v, T⟩ hvt
    simp only [subgraphs, Finset.mem_sigma, Finset.mem_filter, Finset.mem_univ, true_and] at hvt
    obtain ⟨e⟩ := hvt
    let S : Finset V := T.map ⟨Subtype.val, Subtype.val_injective⟩
    have hvS : v ∉ S := by
      intro h
      obtain ⟨⟨x, hx⟩, _, hxv⟩ := Finset.mem_map.mp h
      exact hx (Set.mem_singleton_iff.mpr hxv)
    refine ⟨⟨S, v⟩, ?_, ?_⟩
    · simp only [subgraphs, Finset.mem_sigma, Finset.mem_compl, Finset.mem_filter,
        Finset.mem_univ, true_and]
      exact ⟨⟨(induce_compl_iso_map G v T).symm.trans e⟩, hvS⟩
    · refine Sigma.ext rfl (heq_of_eq ?_)
      ext ⟨x, hx⟩
      simp [S]

private lemma tree_R1_H2 :
    ∀ {V W : Type} [Fintype V] [Fintype W],
      3 ≤ Fintype.card V →
      ∀ (G : SimpleGraph V) (H : SimpleGraph W),
        G.IsTree → H.IsTree → Hypomorphic G H →
        ∀ (U : Type) [Fintype U] (Q : SimpleGraph U),
          Fintype.card U < Fintype.card V →
          {S : Finset V | Nonempty (G.induce (S : Set V) ≃g Q)}.ncard =
            {T : Finset W | Nonempty (H.induce (T : Set W) ≃g Q)}.ncard := by
  intro V W _ _ _ G H _ _ hhyp U _ Q hUV
  rw [ncard_subgraphs_eq, ncard_subgraphs_eq]
  have hpos : 0 < Fintype.card V - Fintype.card U := Nat.sub_pos_of_lt hUV
  refine Nat.eq_of_mul_eq_mul_right hpos ?_
  rw [induced_count_identity G Q, hhyp.card_eq, induced_count_identity H Q]
  obtain ⟨σ, hσ⟩ := hhyp
  refine Fintype.sum_equiv σ _ _ fun v => ?_
  obtain ⟨φ⟩ := hσ v
  exact subgraphs_card_eq_of_iso φ Q

end TreeR1H2

theorem result : OMA.R_ReconstructionConjecture_reconstruction_conjecture_variants_tree_R1.H2 := by
  exact tree_R1_H2

end KellyStep2

namespace KellyStep3

-- Step ReconstructionConjecture.reconstruction_conjecture.variants.tree.R1.H3.R1.H1
-- Credit: @jared-jasinski

namespace ReconTreeH3R1H1

open SimpleGraph

private abbrev pathG (m : ℕ) : SimpleGraph (Fin m) where
  Adj i j := i.val + 1 = j.val ∨ j.val + 1 = i.val
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨fun _ h => by omega⟩

private lemma pathG_neighborSet_ncard_le_two (m : ℕ) (i : Fin m) :
    ((pathG m).neighborSet i).ncard ≤ 2 := by
  have hsub : (pathG m).neighborSet i ⊆
      ({j : Fin m | j.val = i.val + 1} ∪ {j : Fin m | j.val + 1 = i.val}) := by
    intro j hj
    rcases hj with h | h
    · exact Or.inl h.symm
    · exact Or.inr h
  have h1 : ({j : Fin m | j.val = i.val + 1}).ncard ≤ 1 :=
    (Set.ncard_le_one (Set.toFinite _)).mpr fun a ha b hb => by
      change a.val = i.val + 1 at ha
      change b.val = i.val + 1 at hb
      exact Fin.ext (ha.trans hb.symm)
  have h2 : ({j : Fin m | j.val + 1 = i.val}).ncard ≤ 1 :=
    (Set.ncard_le_one (Set.toFinite _)).mpr fun a ha b hb => by
      change a.val + 1 = i.val at ha
      change b.val + 1 = i.val at hb
      exact Fin.ext (by omega)
  calc
    ((pathG m).neighborSet i).ncard
        ≤ ({j : Fin m | j.val = i.val + 1} ∪ {j : Fin m | j.val + 1 = i.val}).ncard :=
          Set.ncard_le_ncard hsub
    _ ≤ ({j : Fin m | j.val = i.val + 1}).ncard + ({j : Fin m | j.val + 1 = i.val}).ncard :=
          Set.ncard_union_le _ _
    _ ≤ 2 := by omega

private lemma walk_of_pathG_iso {V : Type} {G : SimpleGraph V} {S : Finset V} {m : ℕ}
    (e : G.induce (S : Set V) ≃g pathG m) :
    ∀ (k : ℕ) (hk : k < m),
      ∃ p : G.Walk (e.symm ⟨0, by omega⟩).val (e.symm ⟨k, hk⟩).val,
        p.length = k ∧ p.IsPath ∧
        ∀ x ∈ p.support, ∃ i : Fin m, i.val ≤ k ∧ x = (e.symm i).val := by
  intro k
  induction k with
  | zero =>
    intro hk
    refine ⟨Walk.nil, rfl, Walk.IsPath.nil, ?_⟩
    intro x hx
    simp only [Walk.support_nil, List.mem_singleton] at hx
    exact ⟨⟨0, hk⟩, le_rfl, hx⟩
  | succ k ih =>
    intro hk
    obtain ⟨p, hlen, hpath, hsupp⟩ := ih (by omega)
    have hadj_path : (pathG m).Adj ⟨k, by omega⟩ ⟨k + 1, hk⟩ := Or.inl rfl
    have hadj_G : G.Adj (e.symm ⟨k, by omega⟩).val (e.symm ⟨k + 1, hk⟩).val :=
      (e.symm.map_rel_iff).mpr hadj_path
    have hnotmem : (e.symm ⟨k + 1, hk⟩).val ∉ p.support := by
      intro hmem
      obtain ⟨i, hi, heq⟩ := hsupp _ hmem
      have hsub : e.symm ⟨k + 1, hk⟩ = e.symm i := Subtype.ext heq
      have hfin : (⟨k + 1, hk⟩ : Fin m) = i := e.symm.injective hsub
      have : k + 1 = i.val := congrArg Fin.val hfin
      omega
    let q := p.concat hadj_G
    refine ⟨q, by simp [q, hlen], ?_, ?_⟩
    · rw [Walk.isPath_def, Walk.support_concat, List.nodup_append]
      refine ⟨hpath.support_nodup, List.nodup_singleton _, ?_⟩
      intro x hx y hy
      simp only [List.mem_singleton] at hy
      subst hy
      exact fun heq => hnotmem (heq ▸ hx)
    · intro x hx
      rw [Walk.support_concat, List.mem_append, List.mem_singleton] at hx
      rcases hx with hx | rfl
      · obtain ⟨i, hi, rfl⟩ := hsupp x hx
        exact ⟨i, by omega, rfl⟩
      · exact ⟨⟨k + 1, hk⟩, le_rfl, rfl⟩

private lemma le_diam_of_induced_pathG {V : Type} [Fintype V] {G : SimpleGraph V}
    (hT : G.IsTree) {S : Finset V} {d : ℕ}
    (e : G.induce (S : Set V) ≃g pathG (d + 1)) :
    d ≤ G.diam := by
  classical
  obtain ⟨p, hlen, hpath, -⟩ := walk_of_pathG_iso e d (Nat.lt_succ_self d)
  let u := (e.symm ⟨0, Nat.zero_lt_succ d⟩).val
  let v := (e.symm ⟨d, Nat.lt_succ_self d⟩).val
  have : Nonempty V := ⟨u⟩
  obtain ⟨q, hqlen⟩ := hT.connected.exists_walk_length_eq_dist u v
  have : Subsingleton (G.Path u v) :=
    (SimpleGraph.isAcyclic_iff_subsingleton_path.mp hT.isAcyclic) u v
  have huniq : (⟨q.bypass, q.bypass_isPath⟩ : G.Path u v) = ⟨p, hpath⟩ :=
    Subsingleton.elim _ _
  have hle : p.length ≤ q.length := by
    have h1 : q.bypass.length ≤ q.length := q.length_bypass_le_length
    have h2 : q.bypass = p := congrArg Subtype.val huniq
    rw [h2] at h1
    exact h1
  have hdist : d ≤ G.dist u v := by omega
  have hediam : G.ediam ≠ ⊤ := G.connected_iff_ediam_ne_top.mp hT.connected
  exact hdist.trans (G.dist_le_diam hediam)

private lemma exists_induced_pathG_diam {V : Type} [Fintype V] [Nonempty V]
    {G : SimpleGraph V} (hT : G.IsTree) :
    ∃ S : Finset V, S.card = G.diam + 1 ∧ Nonempty (G.induce (S : Set V) ≃g pathG (G.diam + 1)) := by
  classical
  obtain ⟨u, v, huv⟩ := G.exists_dist_eq_diam
  obtain ⟨p0, hp0len⟩ := hT.connected.exists_walk_length_eq_dist u v
  let p : G.Walk u v := p0.bypass
  have hp_path : p.IsPath := p0.bypass_isPath
  have hp_dist : p.length = G.dist u v := by
    have hle : p.length ≤ p0.length := p0.length_bypass_le_length
    have hge : G.dist u v ≤ p.length := G.dist_le p
    omega
  have hp_len : p.length = G.diam := hp_dist.trans huv
  let f : Fin (G.diam + 1) → V := fun i => p.getVert i.val
  have hf_inj : Function.Injective f := by
    intro i j hij
    have hi : i.val ≤ p.length := by omega
    have hj : j.val ≤ p.length := by omega
    have hi' : i.val < p.support.length := by rw [Walk.length_support]; omega
    have hj' : j.val < p.support.length := by rw [Walk.length_support]; omega
    change p.getVert i.val = p.getVert j.val at hij
    rw [Walk.getVert_eq_support_getElem p hi, Walk.getVert_eq_support_getElem p hj] at hij
    exact Fin.ext ((List.Nodup.getElem_inj_iff hp_path.support_nodup).mp hij)
  let S : Finset V := Finset.univ.image f
  have hScard : S.card = G.diam + 1 := by
    rw [Finset.card_image_of_injective _ hf_inj, Finset.card_univ, Fintype.card_fin]
  have hf_mem : ∀ i : Fin (G.diam + 1), f i ∈ (S : Set V) := fun i =>
    Finset.mem_coe.mpr (Finset.mem_image_of_mem f (Finset.mem_univ i))
  let toFun : Fin (G.diam + 1) → (S : Set V) := fun i => ⟨f i, hf_mem i⟩
  have hbij : Function.Bijective toFun := by
    constructor
    · intro i j hij
      exact hf_inj (congrArg Subtype.val hij)
    · rintro ⟨x, hx⟩
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hx)
      exact ⟨i, rfl⟩
  let eqv : Fin (G.diam + 1) ≃ (S : Set V) := Equiv.ofBijective toFun hbij
  have hrel : ∀ i j : Fin (G.diam + 1), (pathG (G.diam + 1)).Adj i j ↔ G.Adj (f i) (f j) := by
    intro i j
    constructor
    · rintro (h | h)
      · have hi : i.val < p.length := by omega
        have := p.adj_getVert_succ hi
        simpa [f, h] using this
      · have hj : j.val < p.length := by omega
        have := p.adj_getVert_succ hj
        exact (by simpa [f, h] using this : G.Adj (f j) (f i)).symm
    · intro hadj
      by_contra hnot
      have hnot1 : i.val + 1 ≠ j.val := fun h => hnot (Or.inl h)
      have hnot2 : j.val + 1 ≠ i.val := fun h => hnot (Or.inr h)
      have hne : i.val ≠ j.val := fun he => G.ne_of_adj hadj (congrArg f (Fin.ext he))
      have hlt_or : i.val + 1 < j.val ∨ j.val + 1 < i.val := by omega
      have shortcut : ∀ a b : Fin (G.diam + 1), a.val + 1 < b.val → G.Adj (f a) (f b) → False := by
        intro a b hab hAB
        have ha_le : a.val ≤ p.length := by omega
        have hb_le : b.val ≤ p.length := by omega
        have ha_lt : a.val < p.support.length := by rw [Walk.length_support]; omega
        have hb_lt : b.val < p.support.length := by rw [Walk.length_support]; omega
        let p1 := p.takeUntil (p.getVert a.val) (p.getVert_mem_support a.val)
        let p2 := p.dropUntil (p.getVert b.val) (p.getVert_mem_support b.val)
        have hidx_a : p.support.idxOf (p.getVert a.val) = a.val := by
          rw [Walk.getVert_eq_support_getElem p ha_le]
          exact hp_path.support_nodup.idxOf_getElem a.val ha_lt
        have hidx_b : p.support.idxOf (p.getVert b.val) = b.val := by
          rw [Walk.getVert_eq_support_getElem p hb_le]
          exact hp_path.support_nodup.idxOf_getElem b.val hb_lt
        have hp1_len : p1.length = a.val := by
          rw [Walk.length_takeUntil, hidx_a]
        have hp2_len : p2.length = p.length - b.val := by
          have hspec := p.take_spec (p.getVert_mem_support b.val)
          have hsum := congrArg Walk.length hspec
          rw [Walk.length_append, Walk.length_takeUntil, hidx_b] at hsum
          change b.val + p2.length = p.length at hsum
          omega
        let q : G.Walk u v := p1.append (Walk.cons hAB p2)
        have hqlen : q.length < p.length := by
          simp only [q, Walk.length_append, Walk.length_cons]
          omega
        have hdist_le : G.dist u v ≤ q.length := G.dist_le q
        omega
      rcases hlt_or with h | h
      · exact shortcut i j h hadj
      · exact shortcut j i h hadj.symm
  refine ⟨S, hScard, ⟨(RelIso.mk eqv (fun {i j} => (hrel i j).symm)).symm⟩⟩

private lemma diam_add_one_lt_card {V : Type} [Fintype V] {G : SimpleGraph V}
    (hT : G.IsTree) (hdeg3 : ∃ v : V, 3 ≤ (G.neighborSet v).ncard) :
    G.diam + 1 < Fintype.card V := by
  classical
  obtain ⟨v₀, hv₀⟩ := hdeg3
  have : Nonempty V := ⟨v₀⟩
  obtain ⟨S, hScard, ⟨e⟩⟩ := exists_induced_pathG_diam hT
  have hle : S.card ≤ Fintype.card V := Finset.card_le_univ S
  by_contra hnot
  have heq : S.card = Fintype.card V := by omega
  have hSuniv : S = Finset.univ := Finset.eq_univ_of_card S heq
  have hv₀S : v₀ ∈ (S : Set V) := by simp [hSuniv]
  let i0 : Fin (G.diam + 1) := e ⟨v₀, hv₀S⟩
  have hnb_le : (G.neighborSet v₀).ncard ≤ ((pathG (G.diam + 1)).neighborSet i0).ncard := by
    let g : G.neighborSet v₀ → (pathG (G.diam + 1)).neighborSet i0 := fun ⟨w, hw⟩ =>
      ⟨e ⟨w, by simp [hSuniv]⟩, by
        change (pathG (G.diam + 1)).Adj (e ⟨v₀, hv₀S⟩) (e ⟨w, by simp [hSuniv]⟩)
        exact e.map_rel_iff.mpr hw⟩
    have hginj : Function.Injective g := by
      intro ⟨w1, hw1⟩ ⟨w2, hw2⟩ h
      have h1 : e ⟨w1, by simp [hSuniv]⟩ = e ⟨w2, by simp [hSuniv]⟩ := congrArg Subtype.val h
      have hw : w1 = w2 := congrArg Subtype.val (e.injective h1)
      exact Subtype.ext hw
    have hcard := Fintype.card_le_of_injective g hginj
    simpa [Set.ncard_eq_toFinset_card'] using hcard
  have hle2 := pathG_neighborSet_ncard_le_two (G.diam + 1) i0
  omega

private lemma two_le_diam_of_deg3 {V : Type} [Fintype V] {G : SimpleGraph V}
    (hT : G.IsTree) (hdeg3 : ∃ v : V, 3 ≤ (G.neighborSet v).ncard) :
    2 ≤ G.diam := by
  obtain ⟨v₀, hv₀⟩ := hdeg3
  have : Nonempty V := ⟨v₀⟩
  have h1lt : 1 < (G.neighborSet v₀).ncard := by omega
  obtain ⟨a, ha, b, hb, hab⟩ := (Set.one_lt_ncard (Set.toFinite _)).mp h1lt
  have hnotadj : ¬ G.Adj a b := by
    intro hAB
    have ha' : G.Adj v₀ a := ha
    have hb' : G.Adj v₀ b := hb
    have ha_ne : a ≠ v₀ := (G.ne_of_adj ha').symm
    have hb_ne : b ≠ v₀ := (G.ne_of_adj hb').symm
    let p1 : G.Walk a b := Walk.cons hAB Walk.nil
    let p2 : G.Walk a b := Walk.cons ha'.symm (Walk.cons hb' Walk.nil)
    have hp1 : p1.IsPath := by
      rw [Walk.isPath_def]
      simp [p1, hab]
    have hp2 : p2.IsPath := by
      dsimp only [p2]
      rw [Walk.cons_isPath_iff, Walk.cons_isPath_iff]
      simp [ha_ne, hb_ne.symm, hab]
    have hsub : Subsingleton (G.Path a b) :=
      (SimpleGraph.isAcyclic_iff_subsingleton_path.mp hT.isAcyclic) a b
    have heq : (⟨p1, hp1⟩ : G.Path a b) = ⟨p2, hp2⟩ := Subsingleton.elim _ _
    have hlen : p1.length = p2.length := congrArg (fun x : G.Path a b => x.1.length) heq
    simp [p1, p2] at hlen
  have hdist_ne0 : G.dist a b ≠ 0 := by
    intro h0
    exact hab ((hT.connected.dist_eq_zero_iff).mp h0)
  have hdist_ne1 : G.dist a b ≠ 1 := by
    intro h1
    exact hnotadj (G.dist_eq_one_iff_adj.mp h1)
  have hdist_ge2 : 2 ≤ G.dist a b := by omega
  have hediam : G.ediam ≠ ⊤ := G.connected_iff_ediam_ne_top.mp hT.connected
  exact hdist_ge2.trans (G.dist_le_diam hediam)

-- In a tree, the length of any path equals the graph distance between its endpoints.
private lemma tree_path_length_eq_dist {V : Type} {G : SimpleGraph V} (hT : G.IsTree)
    {u v : V} {p : G.Walk u v} (hp : p.IsPath) : p.length = G.dist u v := by
  classical
  obtain ⟨q, hqlen⟩ := hT.connected.exists_walk_length_eq_dist u v
  have : Subsingleton (G.Path u v) :=
    (SimpleGraph.isAcyclic_iff_subsingleton_path.mp hT.isAcyclic) u v
  have heq : (⟨q.bypass, q.bypass_isPath⟩ : G.Path u v) = ⟨p, hp⟩ := Subsingleton.elim _ _
  have h1 : p.length ≤ q.length := by
    have hle := q.length_bypass_le_length
    have h2 : q.bypass = p := congrArg Subtype.val heq
    rwa [h2] at hle
  have h2 : G.dist u v ≤ p.length := G.dist_le p
  omega

-- In a tree, if c lies on a path from u to v, then for every x either
-- dist x u = dist x c + dist c u or dist x v = dist x c + dist c v.
private lemma tree_split_dist {V : Type} {G : SimpleGraph V} (hT : G.IsTree)
    {u v c : V} {p : G.Walk u v} (hp : p.IsPath) (hc : c ∈ p.support) (x : V) :
    G.dist x u = G.dist x c + G.dist c u ∨ G.dist x v = G.dist x c + G.dist c v := by
  classical
  obtain ⟨q1_0, hq1_0⟩ := hT.connected.exists_walk_length_eq_dist x u
  obtain ⟨q2_0, hq2_0⟩ := hT.connected.exists_walk_length_eq_dist x v
  let q1 := q1_0.bypass
  let q2 := q2_0.bypass
  have hq1_path : q1.IsPath := q1_0.bypass_isPath
  have hq2_path : q2.IsPath := q2_0.bypass_isPath
  have hmem : c ∈ q1.support ∨ c ∈ q2.support := by
    by_contra hneither
    push Not at hneither
    let w : G.Walk u v := (q1.reverse.append q2).bypass
    have hw_path : w.IsPath := (q1.reverse.append q2).bypass_isPath
    have : Subsingleton (G.Path u v) :=
      (SimpleGraph.isAcyclic_iff_subsingleton_path.mp hT.isAcyclic) u v
    have heq : (⟨w, hw_path⟩ : G.Path u v) = ⟨p, hp⟩ := Subsingleton.elim _ _
    have hw_eq : w = p := congrArg Subtype.val heq
    have hc_w : c ∈ w.support := by rwa [hw_eq]
    have hc_app : c ∈ (q1.reverse.append q2).support := Walk.support_bypass_subset_support _ hc_w
    rw [Walk.support_append, List.mem_append] at hc_app
    rcases hc_app with h1 | h2
    · exact hneither.1 (by simpa [Walk.support_reverse] using h1)
    · exact hneither.2 (List.mem_of_mem_tail h2)
  have split_of_mem : ∀ {y : V} (q : G.Walk x y), q.IsPath → c ∈ q.support →
      G.dist x y = G.dist x c + G.dist c y := by
    intro y q hq hcq
    have h1 := tree_path_length_eq_dist hT hq
    have h2 := tree_path_length_eq_dist hT (hq.takeUntil hcq)
    have h3 := tree_path_length_eq_dist hT (hq.dropUntil hcq)
    have hspec := congrArg Walk.length (q.take_spec hcq)
    rw [Walk.length_append] at hspec
    omega
  rcases hmem with h1 | h2
  · exact Or.inl (split_of_mem q1 hq1_path h1)
  · exact Or.inr (split_of_mem q2 hq2_path h2)

-- Jordan's unique center for a finite tree of even diameter 2 * r.
private lemma exists_unique_center {V : Type} [Fintype V] [Nonempty V]
    {G : SimpleGraph V} (hT : G.IsTree) (r : ℕ) (hdiam : G.diam = 2 * r) :
    ∃ c : V, G.eccent c = (r : ℕ∞) ∧ ∀ v : V, v ≠ c → (r : ℕ∞) < G.eccent v := by
  classical
  obtain ⟨u, v, huv⟩ := G.exists_dist_eq_diam
  obtain ⟨p0, hp0⟩ := hT.connected.exists_walk_length_eq_dist u v
  let p : G.Walk u v := p0.bypass
  have hp_path : p.IsPath := p0.bypass_isPath
  have hp_len : p.length = 2 * r := by
    rw [tree_path_length_eq_dist hT hp_path, huv, hdiam]
  let c : V := p.getVert r
  have hc_mem : c ∈ p.support := p.getVert_mem_support r
  have hr_le : r ≤ p.length := by omega
  have hr_lt : r < p.support.length := by rw [Walk.length_support]; omega
  have hidx : p.support.idxOf c = r := by
    dsimp only [c]
    rw [Walk.getVert_eq_support_getElem p hr_le]
    exact hp_path.support_nodup.idxOf_getElem r hr_lt
  have hdist_uc : G.dist u c = r := by
    rw [← tree_path_length_eq_dist hT (hp_path.takeUntil hc_mem), Walk.length_takeUntil, hidx]
  have hdist_cu : G.dist c u = r := by rw [G.dist_comm, hdist_uc]
  have hdist_cv : G.dist c v = r := by
    have hspec := congrArg Walk.length (p.take_spec hc_mem)
    rw [Walk.length_append, Walk.length_takeUntil, hidx] at hspec
    rw [← tree_path_length_eq_dist hT (hp_path.dropUntil hc_mem)]
    omega
  have hediam : G.ediam ≠ ⊤ := G.connected_iff_ediam_ne_top.mp hT.connected
  have edist_eq : ∀ a b : V, G.edist a b = (G.dist a b : ℕ∞) := fun a b =>
    (ENat.natCast_toNat (ne_top_of_le_ne_top hediam G.edist_le_ediam)).symm
  refine ⟨c, ?_, ?_⟩
  · apply le_antisymm
    · rw [G.eccent_le_iff]
      intro x
      rw [edist_eq c x, G.dist_comm]
      have hx_le : G.dist x c ≤ r := by
        have hxu : G.dist x u ≤ 2 * r := hdiam ▸ G.dist_le_diam hediam
        have hxv : G.dist x v ≤ 2 * r := hdiam ▸ G.dist_le_diam hediam
        rcases tree_split_dist hT hp_path hc_mem x with h1 | h2 <;> omega
      exact_mod_cast hx_le
    · have hle : G.edist c u ≤ G.eccent c := G.edist_le_eccent
      rw [edist_eq c u, hdist_cu] at hle
      exact hle
  · intro x hxc
    have hxc_pos : 0 < G.dist x c := by
      have hne : G.dist x c ≠ 0 := fun h0 => hxc ((hT.connected.dist_eq_zero_iff).mp h0)
      omega
    rcases tree_split_dist hT hp_path hc_mem x with h1 | h2
    · have hlt : (r : ℕ∞) < G.edist x u := by
        rw [edist_eq x u]
        exact_mod_cast (show r < G.dist x u by omega)
      exact lt_of_lt_of_le hlt G.edist_le_eccent
    · have hlt : (r : ℕ∞) < G.edist x v := by
        rw [edist_eq x v]
        exact_mod_cast (show r < G.dist x v by omega)
      exact lt_of_lt_of_le hlt G.edist_le_eccent

end ReconTreeH3R1H1

theorem result : OMA.R_ReconstructionConjecture_reconstruction_conjecture_variants_tree_R1_H3_R1.H1 := by
  intro V W _ _ hV G H σ hTG hTH _ hdeg hnonpath heven hkelly
  have hcardVW : Fintype.card V = Fintype.card W := Fintype.card_congr σ
  have hnonpathH : ∃ w : W, 3 ≤ (H.neighborSet w).ncard := by
    obtain ⟨v₀, hv₀⟩ := hnonpath
    exact ⟨σ v₀, by rw [← hdeg v₀]; exact hv₀⟩
  have hG2 : 2 ≤ G.diam := ReconTreeH3R1H1.two_le_diam_of_deg3 hTG hnonpath
  have hGlt : G.diam + 1 < Fintype.card V := ReconTreeH3R1H1.diam_add_one_lt_card hTG hnonpath
  have hHlt : H.diam + 1 < Fintype.card V := by
    rw [hcardVW]
    exact ReconTreeH3R1H1.diam_add_one_lt_card hTH hnonpathH
  have : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  have : Nonempty W := ⟨σ (Classical.arbitrary V)⟩
  have hGH : G.diam ≤ H.diam := by
    obtain ⟨S, -, hSiso⟩ := ReconTreeH3R1H1.exists_induced_pathG_diam hTG
    have hpos : 0 < {S : Finset V | Nonempty (G.induce (S : Set V) ≃g ReconTreeH3R1H1.pathG (G.diam + 1))}.ncard :=
      (Set.ncard_pos (Set.toFinite _)).mpr ⟨S, hSiso⟩
    rw [hkelly (Fin (G.diam + 1)) (ReconTreeH3R1H1.pathG (G.diam + 1)) (by simpa using hGlt)] at hpos
    obtain ⟨T, ⟨eT⟩⟩ := (Set.ncard_pos (Set.toFinite _)).mp hpos
    exact ReconTreeH3R1H1.le_diam_of_induced_pathG hTH eT
  have hHG : H.diam ≤ G.diam := by
    obtain ⟨T, -, hTiso⟩ := ReconTreeH3R1H1.exists_induced_pathG_diam hTH
    have hpos : 0 < {T : Finset W | Nonempty (H.induce (T : Set W) ≃g ReconTreeH3R1H1.pathG (H.diam + 1))}.ncard :=
      (Set.ncard_pos (Set.toFinite _)).mpr ⟨T, hTiso⟩
    rw [← hkelly (Fin (H.diam + 1)) (ReconTreeH3R1H1.pathG (H.diam + 1)) (by simpa using hHlt)] at hpos
    obtain ⟨S, ⟨eS⟩⟩ := (Set.ncard_pos (Set.toFinite _)).mp hpos
    exact ReconTreeH3R1H1.le_diam_of_induced_pathG hTG eS
  have hdiam_eq : G.diam = H.diam := le_antisymm hGH hHG
  obtain ⟨r, hr⟩ := heven
  have hGdiam : G.diam = 2 * r := by omega
  have hHdiam : H.diam = 2 * r := hdiam_eq.symm.trans hGdiam
  have hr1 : 1 ≤ r := by omega
  obtain ⟨cG, hcG_ecc, hcG_uniq⟩ := ReconTreeH3R1H1.exists_unique_center hTG r hGdiam
  obtain ⟨cH, hcH_ecc, hcH_uniq⟩ := ReconTreeH3R1H1.exists_unique_center hTH r hHdiam
  exact ⟨r, cG, cH, hr1, hGdiam, hHdiam, hcG_ecc, hcH_ecc, hcG_uniq, hcH_uniq⟩

end KellyStep3

namespace KellyStep4

/-
# Proof of `tree.R1.H3.R1.H2`

Center degree equality and singleton-limb elimination for even-diameter (`2 * r`, `r >= 2`) non-path hypomorphic trees (`tree.R1.H3.R1.H2`).
-/

-- Credit: @green-notes

open SimpleGraph

section TreeR1H3R1H2

open Classical

private def pathG (n : ℕ) : SimpleGraph (Fin n) where
  Adj i j := i.val + 1 = j.val ∨ j.val + 1 = i.val
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨fun _ h => by omega⟩

private lemma isTree_dist_eq_length_of_isPath {U : Type} (T : SimpleGraph U) (hT : T.IsTree)
    {x y : U} (p : T.Walk x y) (hp : p.IsPath) :
    p.length = T.dist x y := by
  obtain ⟨q, hq, hqlen⟩ := hT.connected.exists_path_of_dist x y
  have hsub : (⟨p, hp⟩ : T.Path x y) = ⟨q, hq⟩ := (hT.isAcyclic.subsingleton_path x y).elim _ _
  have hpq : p = q := congrArg Subtype.val hsub
  rw [hpq, hqlen]

private lemma isTree_path_eq {U : Type} (T : SimpleGraph U) (hT : T.IsTree)
    {x y : U} {p q : T.Walk x y} (hp : p.IsPath) (hq : q.IsPath) :
    p = q :=
  congrArg Subtype.val ((hT.isAcyclic.subsingleton_path x y).elim ⟨p, hp⟩ ⟨q, hq⟩)

private lemma ncard_neighborSet_eq_degree {U : Type} [Fintype U] (T : SimpleGraph U) (u : U) :
    (T.neighborSet u).ncard = T.degree u := by
  rw [← T.card_neighborSet_eq_degree, Set.ncard_eq_toFinset_card' (T.neighborSet u)]
  simp [Set.toFinset_card]

private lemma split_walk_first_mem {U : Type} (T : SimpleGraph U) (P : Set U)
    [DecidablePred (· ∈ P)] {y c : U} (q : T.Walk y c) (hc : c ∈ P) :
    ∃ (z : U) (q₁ : T.Walk y z) (q₂ : T.Walk z c),
      z ∈ P ∧ q = q₁.append q₂ ∧ (∀ u ∈ q₁.support, u ∈ P → u = z) := by
  induction q with
  | nil =>
    exact ⟨_, Walk.nil, Walk.nil, hc, rfl, fun u hu _ => by simp only [Walk.support_nil, List.mem_singleton] at hu; exact hu⟩
  | @cons a b c h q' ih =>
    by_cases ha : a ∈ P
    · exact ⟨a, Walk.nil, Walk.cons h q', ha, rfl, fun u hu _ => by simp only [Walk.support_nil, List.mem_singleton] at hu; exact hu⟩
    · obtain ⟨z, q₁, q₂, hz, hq', huniq⟩ := ih hc
      refine ⟨z, Walk.cons h q₁, q₂, hz, by rw [hq']; rfl, fun u hu huP => ?_⟩
      simp only [Walk.support_cons, List.mem_cons] at hu
      rcases hu with rfl | hu
      · exact False.elim (ha huP)
      · exact huniq u hu huP

private lemma start_notMem_tail_support_of_isPath {U : Type} {T : SimpleGraph U} {a b : U}
    {w : T.Walk a b} (hw : w.IsPath) : a ∉ w.support.tail := by
  cases w <;> simp_all [Walk.isPath_def]

private lemma isPath_append_of_first_meet {U : Type} {T : SimpleGraph U}
    {y z x : U} {q₁ : T.Walk y z} {s : T.Walk z x}
    (hq₁ : q₁.IsPath) (hs : s.IsPath)
    (hmeet : ∀ u ∈ q₁.support, u ∈ s.support.tail → u = z) :
    (q₁.append s).IsPath := by
  rw [Walk.isPath_def, Walk.support_append, List.nodup_append']
  refine ⟨hq₁.support_nodup, hs.support_nodup.tail, fun u huq hus => ?_⟩
  have huz : u = z := hmeet u huq hus
  subst huz
  exact start_notMem_tail_support_of_isPath hs hus

private lemma exists_unique_center_of_diam_eq_two_mul {U : Type} [Fintype U]
    (T : SimpleGraph U) (hT : T.IsTree) {r : ℕ} (hr : 1 ≤ r) (hdiam : T.diam = 2 * r) :
    ∃ c : U, T.eccent c = r ∧ ∀ v : U, v ≠ c → (r : ℕ∞) < T.eccent v := by
  have : Nonempty U := hT.connected.nonempty
  obtain ⟨x0, xd, hxd⟩ := T.exists_dist_eq_diam
  obtain ⟨p, hp, hplen⟩ := hT.connected.exists_path_of_dist x0 xd
  have hplen_r : p.length = 2 * r := hplen.trans (hxd.trans hdiam)
  let c : U := p.getVert r
  let p₁ : T.Walk x0 c := p.take r
  let p₂ : T.Walk c xd := p.drop r
  have hp1 : p₁.IsPath := hp.take r
  have hp2 : p₂.IsPath := hp.drop r
  have hp1_len : p₁.length = r := by rw [Walk.take_length]; omega
  have hp2_len : p₂.length = r := by rw [Walk.drop_length]; omega
  have hp_app : p₁.append p₂ = p := p.append_take_drop_eq r
  have hkey : ∀ y : U, (T.dist y xd = T.dist y c + r ∨ T.dist y x0 = T.dist y c + r) := by
    intro y
    obtain ⟨q, hq, hqlen⟩ := hT.connected.exists_path_of_dist y c
    obtain ⟨z, q₁, q₂, hz_mem, hq_eq, hq_first⟩ :=
      split_walk_first_mem T {u | u ∈ p.support} q (p.getVert_mem_support r)
    have hq_app : (q₁.append q₂).IsPath := hq_eq ▸ hq
    have hq1 : q₁.IsPath := hq_app.of_append_left
    have hq2 : q₂.IsPath := hq_app.of_append_right
    have hq_len : q.length = q₁.length + q₂.length := by rw [hq_eq, Walk.length_append]
    have hz12 : z ∈ p₁.support ∨ z ∈ p₂.support :=
      (Walk.mem_support_append_iff p₁ p₂).mp (hp_app.symm ▸ hz_mem)
    rcases hz12 with hz1 | hz2
    · obtain ⟨a, b, ha, hb, hp1_eq⟩ := hp1.mem_support_iff_exists_append.mp hz1
      let pR : T.Walk z xd := b.append p₂
      have hp_decomp : p = a.append pR := by rw [← hp_app, hp1_eq, Walk.append_assoc]
      have hpR : pR.IsPath := (hp_decomp ▸ hp).of_append_right
      have hb_eq : q₂ = b := isTree_path_eq T hT hq2 hb
      have hpR_len : pR.length = q₂.length + r := by rw [Walk.length_append, hp2_len, hb_eq]
      have hmeet : ∀ u ∈ q₁.support, u ∈ pR.support.tail → u = z := by
        intro u huq hus
        exact hq_first u huq (hp_decomp ▸ Walk.support_subset_support_append_right a pR (List.mem_of_mem_tail hus))
      have hqpR : (q₁.append pR).IsPath := isPath_append_of_first_meet hq1 hpR hmeet
      have hdist : (q₁.append pR).length = T.dist y xd :=
        isTree_dist_eq_length_of_isPath T hT (q₁.append pR) hqpR
      left
      rw [Walk.length_append, hpR_len] at hdist
      omega
    · obtain ⟨a, b, ha, hb, hp2_eq⟩ := hp2.mem_support_iff_exists_append.mp hz2
      let pL : T.Walk x0 z := p₁.append a
      have hp_decomp : p = pL.append b := by rw [← hp_app, hp2_eq, ← Walk.append_assoc]
      have hpL : pL.IsPath := (hp_decomp ▸ hp).of_append_left
      have ha_eq : q₂ = a.reverse := isTree_path_eq T hT hq2 ha.reverse
      have hpL_len : pL.reverse.length = r + q₂.length := by
        rw [Walk.length_reverse, Walk.length_append, hp1_len, ha_eq, Walk.length_reverse]
      have hmeet : ∀ u ∈ q₁.support, u ∈ pL.reverse.support.tail → u = z := by
        intro u huq hus
        have hus1 : u ∈ pL.reverse.support := List.mem_of_mem_tail hus
        rw [Walk.support_reverse, List.mem_reverse] at hus1
        exact hq_first u huq (hp_decomp ▸ Walk.support_subset_support_append_left pL b hus1)
      have hqpL : (q₁.append pL.reverse).IsPath := isPath_append_of_first_meet hq1 hpL.reverse hmeet
      have hdist : (q₁.append pL.reverse).length = T.dist y x0 :=
        isTree_dist_eq_length_of_isPath T hT (q₁.append pL.reverse) hqpL
      right
      rw [Walk.length_append, hpL_len] at hdist
      omega
  have hediam : T.ediam ≠ ⊤ := connected_iff_ediam_ne_top.mp hT.connected
  have hle_r : ∀ y : U, T.dist y c ≤ r := by
    intro y
    rcases hkey y with hy | hy
    · have := dist_le_diam hediam (u := y) (v := xd); omega
    · have := dist_le_diam hediam (u := y) (v := x0); omega
  have hecc_le : T.eccent c ≤ r := by
    rw [SimpleGraph.eccent_le_iff]
    intro y
    rw [← (hT.connected c y).coe_dist_eq_edist, SimpleGraph.dist_comm]
    exact Nat.cast_le.mpr (hle_r y)
  have hecc_ge : (r : ℕ∞) ≤ T.eccent c := by
    have hcx0 : T.dist c x0 = r := by
      have h := isTree_dist_eq_length_of_isPath T hT p₁ hp1
      rw [SimpleGraph.dist_comm, ← h, hp1_len]
    rw [← hcx0, (hT.connected c x0).coe_dist_eq_edist]
    exact SimpleGraph.edist_le_eccent
  refine ⟨c, le_antisymm hecc_le hecc_ge, fun v hvc => ?_⟩
  have hpos : 0 < T.dist v c := hT.connected.pos_dist_of_ne hvc
  rcases hkey v with hv | hv
  · have hlt : (r : ℕ∞) < (T.dist v xd : ℕ∞) := Nat.cast_lt.mpr (by omega)
    rw [(hT.connected v xd).coe_dist_eq_edist] at hlt
    exact lt_of_lt_of_le hlt SimpleGraph.edist_le_eccent
  · have hlt : (r : ℕ∞) < (T.dist v x0 : ℕ∞) := Nat.cast_lt.mpr (by omega)
    rw [(hT.connected v x0).coe_dist_eq_edist] at hlt
    exact lt_of_lt_of_le hlt SimpleGraph.edist_le_eccent

private lemma induce_support_iso_pathG {U : Type} [Fintype U] (T : SimpleGraph U) (hT : T.IsTree)
    {a b : U} (p : T.Walk a b) (hp : p.IsPath) :
    Nonempty (T.induce (p.support.toFinset : Set U) ≃g pathG (p.length + 1)) := by
  let S : Finset U := p.support.toFinset
  let f : Fin (p.length + 1) → S := fun i =>
    ⟨p.getVert i.val, List.mem_toFinset.mpr (p.getVert_mem_support i.val)⟩
  have hfinj : Function.Injective f := by
    intro i j hij
    have hval : p.getVert i.val = p.getVert j.val := congrArg Subtype.val hij
    exact Fin.ext (hp.getVert_injOn (Nat.lt_succ_iff.mp i.isLt) (Nat.lt_succ_iff.mp j.isLt) hval)
  have hfsurj : Function.Surjective f := by
    rintro ⟨v, hv⟩
    rw [List.mem_toFinset, Walk.mem_support_iff_exists_getVert] at hv
    obtain ⟨i, hi_eq, hi_le⟩ := hv
    exact ⟨⟨i, Nat.lt_succ_of_le hi_le⟩, Subtype.ext hi_eq⟩
  let e : Fin (p.length + 1) ≃ S := Equiv.ofBijective f ⟨hfinj, hfsurj⟩
  have hrel : ∀ i j : Fin (p.length + 1),
      (T.induce (S : Set U)).Adj (e i) (e j) ↔ (pathG (p.length + 1)).Adj i j := by
    intro i j
    change T.Adj (p.getVert i.val) (p.getVert j.val) ↔ (i.val + 1 = j.val ∨ j.val + 1 = i.val)
    constructor
    · intro hadj
      rcases Nat.lt_trichotomy i.val j.val with hij | hij | hji
      · left
        let q : T.Walk (p.getVert i.val) (p.getVert j.val) :=
          ((p.take j.val).drop i.val).copy
            (by simp [Walk.take_getVert, Nat.min_eq_right hij.le]) rfl
        have hq : q.IsPath := by rw [Walk.isPath_copy]; exact (hp.take j.val).drop i.val
        have hqlen : q.length = j.val - i.val := by
          rw [Walk.length_copy, Walk.drop_length, Walk.take_length]
          have hj : j.val ≤ p.length := Nat.lt_succ_iff.mp j.isLt
          omega
        have hq_eq : q = (Path.singleton hadj).val :=
          isTree_path_eq T hT hq (Path.singleton hadj).isPath
        have hlen1 : q.length = 1 := by rw [hq_eq]; rfl
        omega
      · exact False.elim (T.ne_of_adj hadj (by rw [hij]))
      · right
        let q : T.Walk (p.getVert j.val) (p.getVert i.val) :=
          ((p.take i.val).drop j.val).copy
            (by simp [Walk.take_getVert, Nat.min_eq_right hji.le]) rfl
        have hq : q.IsPath := by rw [Walk.isPath_copy]; exact (hp.take i.val).drop j.val
        have hqlen : q.length = i.val - j.val := by
          rw [Walk.length_copy, Walk.drop_length, Walk.take_length]
          have hi : i.val ≤ p.length := Nat.lt_succ_iff.mp i.isLt
          omega
        have hq_eq : q = (Path.singleton hadj.symm).val :=
          isTree_path_eq T hT hq (Path.singleton hadj.symm).isPath
        have hlen1 : q.length = 1 := by rw [hq_eq]; rfl
        omega
    · rintro (hij | hji)
      · have := p.adj_getVert_succ (by omega : i.val < p.length)
        simpa [hij] using this
      · have := p.adj_getVert_succ (by omega : j.val < p.length)
        simpa [hji] using this.symm
  exact ⟨(⟨e, @hrel⟩ : pathG (p.length + 1) ≃g T.induce (S : Set U)).symm⟩

private lemma length_walk_induce {U : Type*} (T : SimpleGraph U) (S : Set U) {a b : U}
    (p : T.Walk a b) (hp : ∀ x ∈ p.support, x ∈ S) :
    (p.induce S hp).length = p.length := by
  have h := congrArg Walk.length (Walk.map_induce p hp)
  rwa [Walk.length_map] at h

private lemma iso_edist_eq {A B : Type*} (GA : SimpleGraph A) (GB : SimpleGraph B)
    (φ : GA ≃g GB) (a₁ a₂ : A) : GB.edist (φ a₁) (φ a₂) = GA.edist a₁ a₂ := by
  apply le_antisymm
  · dsimp only [SimpleGraph.edist]
    rw [le_iInf_iff]
    intro w
    exact (SimpleGraph.edist_le (w.map φ.toHom)).trans (by simp)
  · dsimp only [SimpleGraph.edist]
    rw [le_iInf_iff]
    intro w
    exact (SimpleGraph.edist_le ((w.map φ.symm.toHom).copy (φ.symm_apply_apply a₁) (φ.symm_apply_apply a₂))).trans
      (by rw [Nat.cast_le, Walk.length_copy, Walk.length_map])

private lemma iso_eccent_eq {A B : Type*} (GA : SimpleGraph A) (GB : SimpleGraph B)
    (φ : GA ≃g GB) (a : A) : GB.eccent (φ a) = GA.eccent a := by
  simp only [SimpleGraph.eccent_def]
  apply le_antisymm
  · rw [iSup_le_iff]
    intro b
    rw [← φ.apply_symm_apply b, iso_edist_eq GA GB φ a (φ.symm b)]
    exact le_iSup (GA.edist a) (φ.symm b)
  · rw [iSup_le_iff]
    intro a'
    rw [← iso_edist_eq GA GB φ a a']
    exact le_iSup (GB.edist (φ a)) (φ a')

private lemma iso_diam_eq {A B : Type*} (GA : SimpleGraph A) (GB : SimpleGraph B)
    (φ : GA ≃g GB) : GA.diam = GB.diam := by
  simp only [SimpleGraph.diam, SimpleGraph.ediam]
  congr 1
  apply le_antisymm
  · rw [iSup_le_iff]
    intro a
    rw [← iso_eccent_eq GA GB φ a]
    exact le_iSup GB.eccent (φ a)
  · rw [iSup_le_iff]
    intro b
    rw [← φ.apply_symm_apply b, iso_eccent_eq GA GB φ (φ.symm b)]
    exact le_iSup GA.eccent (φ.symm b)

private lemma degree_induce_compl_singleton_of_adj {U : Type} [Fintype U]
    (T : SimpleGraph U) {a v : U} (hav : a ∈ ({v}ᶜ : Set U)) (hadj : T.Adj a v) :
    (T.induce {v}ᶜ).degree ⟨a, hav⟩ + 1 = T.degree a := by
  let f : ({v}ᶜ : Set U) ↪ U := ⟨Subtype.val, Subtype.val_injective⟩
  have hmap_not : v ∉ ((T.induce {v}ᶜ).neighborFinset ⟨a, hav⟩).map f := by
    intro h
    rw [Finset.mem_map] at h
    obtain ⟨x, _, hxv⟩ := h
    exact x.2 hxv
  have heq : insert v (((T.induce {v}ᶜ).neighborFinset ⟨a, hav⟩).map f) = T.neighborFinset a := by
    ext y
    rw [Finset.mem_insert, Finset.mem_map, SimpleGraph.mem_neighborFinset]
    constructor
    · rintro (rfl | ⟨x, hx, rfl⟩)
      · exact hadj
      · rw [SimpleGraph.mem_neighborFinset] at hx
        exact hx
    · intro hay
      by_cases hyv : y = v
      · exact Or.inl hyv
      · refine Or.inr ⟨⟨y, hyv⟩, ?_, rfl⟩
        rw [SimpleGraph.mem_neighborFinset]
        exact hay
  have hcard := congrArg Finset.card heq
  rw [Finset.card_insert_of_notMem hmap_not, Finset.card_map,
    (T.induce {v}ᶜ).card_neighborFinset_eq_degree, T.card_neighborFinset_eq_degree] at hcard
  omega

private lemma degree_induce_compl_singleton_of_not_adj {U : Type} [Fintype U]
    (T : SimpleGraph U) {a v : U} (hav : a ∈ ({v}ᶜ : Set U)) (hnadj : ¬ T.Adj a v) :
    (T.induce {v}ᶜ).degree ⟨a, hav⟩ = T.degree a := by
  let f : ({v}ᶜ : Set U) ↪ U := ⟨Subtype.val, Subtype.val_injective⟩
  have heq : ((T.induce {v}ᶜ).neighborFinset ⟨a, hav⟩).map f = T.neighborFinset a := by
    ext y
    rw [Finset.mem_map, SimpleGraph.mem_neighborFinset]
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [SimpleGraph.mem_neighborFinset] at hx
      exact hx
    · intro hay
      have hyv : y ≠ v := fun h => hnadj (h ▸ hay)
      refine ⟨⟨y, hyv⟩, ?_, rfl⟩
      rw [SimpleGraph.mem_neighborFinset]
      exact hay
  have hcard := congrArg Finset.card heq
  rw [Finset.card_map, (T.induce {v}ᶜ).card_neighborFinset_eq_degree,
    T.card_neighborFinset_eq_degree] at hcard
  exact hcard

private lemma degree_induce_compl_le {U : Type} [Fintype U]
    (T : SimpleGraph U) {a v : U} (hav : a ∈ ({v}ᶜ : Set U)) :
    (T.induce {v}ᶜ).degree ⟨a, hav⟩ ≤ T.degree a := by
  by_cases hadj : T.Adj a v
  · have := degree_induce_compl_singleton_of_adj T hav hadj
    omega
  · rw [degree_induce_compl_singleton_of_not_adj T hav hadj]

private lemma induce_compl_singleton_isTree_of_deg_one {U : Type} [Fintype U]
    (T : SimpleGraph U) (hT : T.IsTree) {v : U} (hdeg1 : T.degree v = 1) :
    (T.induce {v}ᶜ).IsTree :=
  ⟨hT.connected.induce_compl_singleton_of_degree_eq_one hdeg1, hT.isAcyclic.induce {v}ᶜ⟩

private lemma induce_compl_singleton_dist_eq {U : Type} [Fintype U]
    (T : SimpleGraph U) (hT : T.IsTree) {v : U} (hT' : (T.induce {v}ᶜ).IsTree)
    (a b : ({v}ᶜ : Set U)) :
    (T.induce {v}ᶜ).dist a b = T.dist a.1 b.1 := by
  obtain ⟨p, hp, hplen⟩ := hT'.connected.exists_path_of_dist a b
  let g : T.induce {v}ᶜ →g T := (SimpleGraph.Embedding.induce ({v}ᶜ : Set U)).toHom
  have hmap : (p.map g).IsPath := hp.map Subtype.val_injective
  have hdist := isTree_dist_eq_length_of_isPath T hT (p.map g) hmap
  rw [Walk.length_map, hplen] at hdist
  exact hdist

private lemma induce_compl_singleton_diam_le {U : Type} [Fintype U]
    (T : SimpleGraph U) (hT : T.IsTree) {v : U} (hdeg1 : T.degree v = 1) :
    (T.induce {v}ᶜ).diam ≤ T.diam := by
  have : Nonempty U := hT.connected.nonempty
  have hT' : (T.induce {v}ᶜ).IsTree := induce_compl_singleton_isTree_of_deg_one T hT hdeg1
  have : Nonempty ({v}ᶜ : Set U) := hT'.connected.nonempty
  obtain ⟨a, b, hab⟩ := (T.induce {v}ᶜ).exists_dist_eq_diam
  rw [← hab, induce_compl_singleton_dist_eq T hT hT']
  exact dist_le_diam (connected_iff_ediam_ne_top.mp hT.connected)

private lemma ne_center_of_deg_one {U : Type} [Fintype U]
    (T : SimpleGraph U) (hT : T.IsTree) {r : ℕ} (hr : 1 ≤ r) (c : U)
    (hecc : T.eccent c = r) (huniq_c : ∀ z : U, z ≠ c → (r : ℕ∞) < T.eccent z)
    {v : U} (hdeg1 : T.degree v = 1) : v ≠ c := by
  rintro rfl
  obtain ⟨u, huv, huniq⟩ := SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp hdeg1
  have huc : u ≠ v := huv.ne.symm
  have hle : T.eccent u ≤ r := by
    rw [SimpleGraph.eccent_le_iff]
    intro y
    rw [← (hT.connected u y).coe_dist_eq_edist]
    norm_cast
    by_cases hyv : y = v
    · subst hyv
      have hd : T.dist u y = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr huv.symm
      omega
    · obtain ⟨p, hp, hplen⟩ := hT.connected.exists_path_of_dist v y
      have hnp : ¬ p.Nil := Walk.not_nil_of_ne (Ne.symm hyv)
      have hsnd : p.snd = u := huniq p.snd (p.adj_snd hnp)
      let p' : T.Walk u y := p.tail.copy hsnd rfl
      have hp' : p'.IsPath := (Walk.isPath_copy _ _ _).mpr hp.tail
      have hdist_u : T.dist u y = p'.length :=
        (isTree_dist_eq_length_of_isPath T hT p' hp').symm
      have hvy_le : T.dist v y ≤ r := by
        have h1 : (T.dist v y : ℕ∞) ≤ r := by
          rw [(hT.connected v y).coe_dist_eq_edist, ← hecc]
          exact SimpleGraph.edist_le_eccent
        exact Nat.cast_le.mp h1
      rw [hdist_u, Walk.length_copy, Walk.length_tail, hplen]
      omega
  have hlt := huniq_c u huc
  exact absurd (lt_of_lt_of_le hlt hle) (lt_irrefl _)

private lemma center_induce_compl_of_good_leaf {U : Type} [Fintype U]
    (T : SimpleGraph U) (hT : T.IsTree) {r : ℕ} (hr : 1 ≤ r)
    (c : U) (hecc : T.eccent c = r) (huniq_c : ∀ z : U, z ≠ c → (r : ℕ∞) < T.eccent z)
    {v : U} (hdeg1 : T.degree v = 1) (hdiam' : (T.induce {v}ᶜ).diam = 2 * r) :
    ∃ hc : c ∈ ({v}ᶜ : Set U),
      (T.induce {v}ᶜ).eccent ⟨c, hc⟩ = r ∧
      ∀ z' : ({v}ᶜ : Set U), z' ≠ ⟨c, hc⟩ → (r : ℕ∞) < (T.induce {v}ᶜ).eccent z' := by
  have hc : c ∈ ({v}ᶜ : Set U) := Set.mem_compl_singleton_iff.mpr (ne_center_of_deg_one T hT hr c hecc huniq_c hdeg1).symm
  refine ⟨hc, ?_⟩
  let T' := T.induce ({v}ᶜ : Set U)
  have hT' : T'.IsTree := induce_compl_singleton_isTree_of_deg_one T hT hdeg1
  let c' : ({v}ᶜ : Set U) := ⟨c, hc⟩
  have hle_r : ∀ y' : ({v}ᶜ : Set U), T'.dist c' y' ≤ r := by
    intro y'
    rw [induce_compl_singleton_dist_eq T hT hT']
    have h1 : (T.dist c y'.1 : ℕ∞) ≤ r := by
      rw [(hT.connected c y'.1).coe_dist_eq_edist, ← hecc]
      exact SimpleGraph.edist_le_eccent
    exact Nat.cast_le.mp h1
  have hecc_le : T'.eccent c' ≤ r := by
    rw [SimpleGraph.eccent_le_iff]
    intro y'
    rw [← (hT'.connected c' y').coe_dist_eq_edist]
    exact Nat.cast_le.mpr (hle_r y')
  have : Nonempty ({v}ᶜ : Set U) := hT'.connected.nonempty
  obtain ⟨a, b, hab⟩ := T'.exists_dist_eq_diam
  rw [hdiam'] at hab
  have hda : T'.dist c' a = r := by
    have htri := hT'.connected.dist_triangle (u := a) (v := c') (w := b)
    rw [SimpleGraph.dist_comm (u := a) (v := c')] at htri
    have ha := hle_r a
    have hb := hle_r b
    omega
  have hecc_ge : (r : ℕ∞) ≤ T'.eccent c' := by
    rw [← hda, (hT'.connected c' a).coe_dist_eq_edist]
    exact SimpleGraph.edist_le_eccent
  have hecc_eq : T'.eccent c' = r := le_antisymm hecc_le hecc_ge
  obtain ⟨c₀, _, huniq₀⟩ := exists_unique_center_of_diam_eq_two_mul T' hT' hr hdiam'
  have hc₀ : c' = c₀ := by
    by_contra hne
    have hlt := huniq₀ c' hne
    rw [hecc_eq] at hlt
    exact absurd hlt (lt_irrefl _)
  subst hc₀
  exact ⟨hecc_eq, huniq₀⟩

private lemma iso_map_center_of_good_leaf {V W : Type} [Fintype V] [Fintype W]
    (G : SimpleGraph V) (H : SimpleGraph W) (hTG : G.IsTree) (hTH : H.IsTree)
    {r : ℕ} (hr : 1 ≤ r) (cG : V) (cH : W)
    (heccG : G.eccent cG = r) (huG : ∀ v : V, v ≠ cG → (r : ℕ∞) < G.eccent v)
    (heccH : H.eccent cH = r) (huH : ∀ w : W, w ≠ cH → (r : ℕ∞) < H.eccent w)
    {v : V} {w : W} (hv1 : G.degree v = 1) (hw1 : H.degree w = 1)
    (hdiamG' : (G.induce {v}ᶜ).diam = 2 * r)
    (φ : G.induce {v}ᶜ ≃g H.induce {w}ᶜ) :
    ∃ (hcG : cG ∈ ({v}ᶜ : Set V)) (hcH : cH ∈ ({w}ᶜ : Set W)), φ ⟨cG, hcG⟩ = ⟨cH, hcH⟩ := by
  have hdiamH' : (H.induce {w}ᶜ).diam = 2 * r :=
    (iso_diam_eq _ _ φ).symm.trans hdiamG'
  obtain ⟨hcG, heccG', _⟩ := center_induce_compl_of_good_leaf G hTG hr cG heccG huG hv1 hdiamG'
  obtain ⟨hcH, _, huH'⟩ := center_induce_compl_of_good_leaf H hTH hr cH heccH huH hw1 hdiamH'
  refine ⟨hcG, hcH, ?_⟩
  by_contra hne
  have hlt := huH' (φ ⟨cG, hcG⟩) hne
  rw [iso_eccent_eq _ _ φ ⟨cG, hcG⟩, heccG'] at hlt
  exact absurd hlt (lt_irrefl _)

private lemma three_le_leaves_card {U : Type} [Fintype U] (T : SimpleGraph U) (hT : T.IsTree)
    (hU : 3 ≤ Fintype.card U) (hdeg : ∃ v₀ : U, 3 ≤ T.degree v₀) :
    3 ≤ (Finset.univ.filter fun v : U => T.degree v = 1).card := by
  obtain ⟨v₀, hv₀⟩ := hdeg
  have : Nontrivial U := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  let L : Finset U := Finset.univ.filter fun v : U => T.degree v = 1
  have hv₀_not : v₀ ∉ L := by
    simp only [L, Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  have hpos : ∀ v : U, 1 ≤ T.degree v := fun v => hT.preconnected.degree_pos_of_nontrivial v
  have hge2 : ∀ v ∈ Lᶜ, 2 ≤ T.degree v := by
    intro v hv
    simp only [L, Finset.mem_compl, Finset.mem_filter, Finset.mem_univ, true_and] at hv
    have := hpos v
    omega
  have hsum_deg : ∑ v : U, T.degree v = 2 * Fintype.card U - 2 := by
    rw [T.sum_degrees_eq_twice_card_edges]
    have := hT.card_edgeFinset
    omega
  have hsplit : (∑ v ∈ L, T.degree v) + ∑ v ∈ Lᶜ, T.degree v = ∑ v : U, T.degree v :=
    Finset.sum_add_sum_compl L (fun v => T.degree v)
  have hsum_L : ∑ v ∈ L, T.degree v = L.card := by
    calc
      ∑ v ∈ L, T.degree v = ∑ _v ∈ L, 1 := Finset.sum_congr rfl fun v hv => (Finset.mem_filter.mp hv).2
      _ = L.card := by simp
  have hv₀_mem : v₀ ∈ Lᶜ := Finset.mem_compl.mpr hv₀_not
  have hsum_Lc : 2 * Lᶜ.card + 1 ≤ ∑ v ∈ Lᶜ, T.degree v := by
    have h1 : ∑ v ∈ Lᶜ, T.degree v = T.degree v₀ + ∑ v ∈ Lᶜ.erase v₀, T.degree v :=
      (Finset.add_sum_erase Lᶜ (fun v => T.degree v) hv₀_mem).symm
    have h2 : ∑ v ∈ Lᶜ.erase v₀, 2 ≤ ∑ v ∈ Lᶜ.erase v₀, T.degree v :=
      Finset.sum_le_sum fun v hv => hge2 v (Finset.mem_of_mem_erase hv)
    have hcard_er : (Lᶜ.erase v₀).card + 1 = Lᶜ.card := by
      rw [Finset.card_erase_of_mem hv₀_mem]
      have : 0 < Lᶜ.card := Finset.card_pos.mpr ⟨v₀, hv₀_mem⟩
      omega
    simp only [Finset.sum_const, smul_eq_mul] at h2
    omega
  have hcard_compl : L.card + Lᶜ.card = Fintype.card U := by
    rw [Finset.card_compl]
    have : L.card ≤ Fintype.card U := Finset.card_le_univ L
    omega
  change 3 ≤ L.card
  omega

private lemma good_leaf_of_ne_diam_ends {U : Type} [Fintype U] (T : SimpleGraph U) (hT : T.IsTree)
    {r : ℕ} (_hr : 2 ≤ r) (hdiam : T.diam = 2 * r) {x0 xd : U} (hxd : T.dist x0 xd = 2 * r)
    {v : U} (hv1 : T.degree v = 1) (hx0 : v ≠ x0) (hxd_ne : v ≠ xd) :
    (T.induce {v}ᶜ).diam = 2 * r := by
  obtain ⟨p, hp, hplen⟩ := hT.connected.exists_path_of_dist x0 xd
  have hnot : v ∉ p.support := by
    intro hv_mem
    obtain ⟨q, s, hq, hs, hp_eq⟩ := hp.mem_support_iff_exists_append.mp hv_mem
    have hq_nn : ¬ q.Nil := Walk.not_nil_of_ne hx0.symm
    have hs_nn : ¬ s.Nil := Walk.not_nil_of_ne hxd_ne
    have hadj1 : T.Adj v q.penultimate := (q.adj_penultimate hq_nn).symm
    have hadj2 : T.Adj v s.snd := s.adj_snd hs_nn
    have hne12 : q.penultimate ≠ s.snd := by
      have hdisj : q.support.Disjoint s.tail.support := by
        have h1 := (hp_eq ▸ hp).support_nodup
        rw [Walk.support_append, List.nodup_append', ← Walk.support_tail_of_not_nil s hs_nn] at h1
        exact h1.2.2
      have hm1 : q.penultimate ∈ q.support := Walk.getVert_mem_support q (q.length - 1)
      have hm2 : s.snd ∈ s.tail.support := by
        rw [Walk.support_tail_of_not_nil s hs_nn]
        exact s.snd_mem_tail_support hs_nn
      intro heq
      rw [heq] at hm1
      exact hdisj hm1 hm2
    have h2 : 2 ≤ T.degree v := by
      rw [← T.card_neighborFinset_eq_degree]
      have hsub : {q.penultimate, s.snd} ⊆ T.neighborFinset v := by
        intro z hz
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rw [SimpleGraph.mem_neighborFinset]
        rcases hz with rfl | rfl <;> assumption
      calc
        2 = ({q.penultimate, s.snd} : Finset U).card := (Finset.card_pair hne12).symm
        _ ≤ (T.neighborFinset v).card := Finset.card_le_card hsub
    omega
  have hw_supp : ∀ x ∈ p.support, x ∈ ({v}ᶜ : Set U) := fun x hx =>
    Set.mem_compl_singleton_iff.mpr fun heq => hnot (heq ▸ hx)
  let p' := p.induce ({v}ᶜ : Set U) hw_supp
  have hp' : p'.IsPath := by
    refine Walk.IsPath.of_map (f := (SimpleGraph.Embedding.induce ({v}ᶜ : Set U)).toHom) ?_
    rw [Walk.map_induce]
    exact hp
  have hT' : (T.induce {v}ᶜ).IsTree := induce_compl_singleton_isTree_of_deg_one T hT hv1
  have : Nonempty ({v}ᶜ : Set U) := hT'.connected.nonempty
  have hdist : (T.induce {v}ᶜ).dist ⟨x0, hw_supp x0 p.start_mem_support⟩
      ⟨xd, hw_supp xd p.end_mem_support⟩ = 2 * r := by
    have h1 := isTree_dist_eq_length_of_isPath (T.induce {v}ᶜ) hT' p' hp'
    rw [← h1, length_walk_induce, hplen, hxd]
  have hediam' : (T.induce {v}ᶜ).ediam ≠ ⊤ := connected_iff_ediam_ne_top.mp hT'.connected
  have hge : 2 * r ≤ (T.induce {v}ᶜ).diam := hdist ▸ dist_le_diam hediam'
  have hle : (T.induce {v}ᶜ).diam ≤ 2 * r := hdiam ▸ induce_compl_singleton_diam_le T hT hv1
  omega

private lemma exists_good_leaf {U : Type} [Fintype U] (T : SimpleGraph U) (hT : T.IsTree)
    (hU : 3 ≤ Fintype.card U) (hdeg : ∃ v₀ : U, 3 ≤ T.degree v₀)
    {r : ℕ} (hr : 2 ≤ r) (hdiam : T.diam = 2 * r) :
    ∃ v : U, T.degree v = 1 ∧ (T.induce {v}ᶜ).diam = 2 * r := by
  have : Nonempty U := hT.connected.nonempty
  obtain ⟨x0, xd, hxd⟩ := T.exists_dist_eq_diam
  have hxd_r : T.dist x0 xd = 2 * r := hxd.trans hdiam
  let L : Finset U := Finset.univ.filter fun v : U => T.degree v = 1
  have hL3 : 3 ≤ L.card := three_le_leaves_card T hT hU hdeg
  have hdiff : 0 < (L \ {x0, xd}).card := by
    have hsub : L ⊆ (L \ {x0, xd}) ∪ {x0, xd} := fun z hz => by
      by_cases hzm : z ∈ ({x0, xd} : Finset U)
      · exact Finset.mem_union_right _ hzm
      · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hz, hzm⟩)
    have hcard2 : ({x0, xd} : Finset U).card ≤ 2 :=
      (Finset.card_insert_le _ _).trans (by simp)
    have hle := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    omega
  obtain ⟨v, hv⟩ := Finset.card_pos.mp hdiff
  simp only [L, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_insert, Finset.mem_singleton, not_or] at hv
  exact ⟨v, hv.1, good_leaf_of_ne_diam_ends T hT hr hdiam hxd_r hv.1 hv.2.1 hv.2.2⟩

private lemma iso_of_deg_center_eq_and_leaf_adj {V W : Type} [Fintype V] [Fintype W]
    (G : SimpleGraph V) (H : SimpleGraph W) (σ : V ≃ W)
    (hTG : G.IsTree) (hTH : H.IsTree)
    (hdeg : ∀ v : V, (G.neighborSet v).ncard = (H.neighborSet (σ v)).ncard)
    {r : ℕ} (hr : 2 ≤ r) (hdiamG : G.diam = 2 * r)
    (cG : V) (cH : W)
    (heccG : G.eccent cG = r) (huG : ∀ v : V, v ≠ cG → (r : ℕ∞) < G.eccent v)
    (heccH : H.eccent cH = r) (huH : ∀ w : W, w ≠ cH → (r : ℕ∞) < H.eccent w)
    (hdegc : G.degree cG = H.degree cH)
    {v : V} (hadj : G.Adj cG v) (hv1 : G.degree v = 1)
    (hσv : Nonempty (G.induce {v}ᶜ ≃g H.induce {σ v}ᶜ)) :
    Nonempty (G ≃g H) := by
  have : Nonempty V := hTG.connected.nonempty
  obtain ⟨x0, xd, hxd⟩ := G.exists_dist_eq_diam
  have hxd_r : G.dist x0 xd = 2 * r := hxd.trans hdiamG
  have hdist_c_x0 : G.dist cG x0 = r := by
    have htri := hTG.connected.dist_triangle (u := x0) (v := cG) (w := xd)
    have h1 : G.dist cG x0 ≤ r := Nat.cast_le.mp (by
      rw [(hTG.connected cG x0).coe_dist_eq_edist, ← heccG]
      exact SimpleGraph.edist_le_eccent)
    have h2 : G.dist cG xd ≤ r := Nat.cast_le.mp (by
      rw [(hTG.connected cG xd).coe_dist_eq_edist, ← heccG]
      exact SimpleGraph.edist_le_eccent)
    rw [SimpleGraph.dist_comm (u := x0) (v := cG)] at htri
    omega
  have hdist_c_xd : G.dist cG xd = r := by
    have htri := hTG.connected.dist_triangle (u := x0) (v := cG) (w := xd)
    have h2 : G.dist cG xd ≤ r := Nat.cast_le.mp (by
      rw [(hTG.connected cG xd).coe_dist_eq_edist, ← heccG]
      exact SimpleGraph.edist_le_eccent)
    rw [SimpleGraph.dist_comm (u := x0) (v := cG)] at htri
    omega
  have hdist_c_v : G.dist cG v = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hadj
  have hv_x0 : v ≠ x0 := fun h => by rw [h, hdist_c_x0] at hdist_c_v; omega
  have hv_xd : v ≠ xd := fun h => by rw [h, hdist_c_xd] at hdist_c_v; omega
  have hdiamG' : (G.induce {v}ᶜ).diam = 2 * r :=
    good_leaf_of_ne_diam_ends G hTG hr hdiamG hxd_r hv1 hv_x0 hv_xd
  have hw1 : H.degree (σ v) = 1 := by
    rw [← ncard_neighborSet_eq_degree, ← hdeg v, ncard_neighborSet_eq_degree, hv1]
  obtain ⟨φ⟩ := hσv
  obtain ⟨hcG, hcH, hφc⟩ :=
    iso_map_center_of_good_leaf G H hTG hTH (by omega) cG cH heccG huG heccH huH hv1 hw1 hdiamG' φ
  have hdeg_ind : (G.induce {v}ᶜ).degree ⟨cG, hcG⟩ = (H.induce {σ v}ᶜ).degree ⟨cH, hcH⟩ := by
    rw [← hφc]
    exact (φ.degree_eq ⟨cG, hcG⟩).symm
  have hdeg_cG_ind := degree_induce_compl_singleton_of_adj G hcG hadj
  have hadjH : H.Adj cH (σ v) := by
    by_contra hnadj
    rw [degree_induce_compl_singleton_of_not_adj H hcH hnadj] at hdeg_ind
    have hG_pos : 0 < G.degree cG := by
      rw [← G.card_neighborFinset_eq_degree]
      exact Finset.card_pos.mpr ⟨v, (G.mem_neighborFinset cG v).mpr hadj⟩
    omega
  have huniqG := (SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp hv1)
  have huniqH := (SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp hw1)
  have hv_only : ∀ x : V, G.Adj v x ↔ x = cG := by
    intro x
    constructor
    · intro h
      obtain ⟨u, hu, hu_uniq⟩ := huniqG
      have h1 : cG = u := hu_uniq cG hadj.symm
      have h2 : x = u := hu_uniq x h
      exact h2.trans h1.symm
    · rintro rfl
      exact hadj.symm
  have hw_only : ∀ y : W, H.Adj (σ v) y ↔ y = cH := by
    intro y
    constructor
    · intro h
      obtain ⟨u, hu, hu_uniq⟩ := huniqH
      have h1 : cH = u := hu_uniq cH hadjH.symm
      have h2 : y = u := hu_uniq y h
      exact h2.trans h1.symm
    · rintro rfl
      exact hadjH.symm
  let toF : V → W := fun x => if hx : x ∈ ({v}ᶜ : Set V) then (φ ⟨x, hx⟩).1 else σ v
  let invF : W → V := fun y => if hy : y ∈ ({σ v}ᶜ : Set W) then (φ.symm ⟨y, hy⟩).1 else v
  have hleft : Function.LeftInverse invF toF := by
    intro x
    dsimp only [toF, invF]
    by_cases hx : x ∈ ({v}ᶜ : Set V)
    · rw [dif_pos hx]
      have hne : (φ ⟨x, hx⟩).1 ∈ ({σ v}ᶜ : Set W) := (φ ⟨x, hx⟩).2
      rw [dif_pos hne, Subtype.coe_eta]
      exact congrArg Subtype.val (φ.left_inv ⟨x, hx⟩)
    · rw [dif_neg hx]
      have hnv : σ v ∉ ({σ v}ᶜ : Set W) := fun h => h rfl
      rw [dif_neg hnv]
      exact (not_not.mp (mt Set.mem_compl_singleton_iff.mpr hx)).symm
  have hright : Function.RightInverse invF toF := by
    intro y
    dsimp only [toF, invF]
    by_cases hy : y ∈ ({σ v}ᶜ : Set W)
    · rw [dif_pos hy]
      have hne : (φ.symm ⟨y, hy⟩).1 ∈ ({v}ᶜ : Set V) := (φ.symm ⟨y, hy⟩).2
      rw [dif_pos hne, Subtype.coe_eta]
      exact congrArg Subtype.val (φ.right_inv ⟨y, hy⟩)
    · rw [dif_neg hy]
      have hnv : v ∉ ({v}ᶜ : Set V) := fun h => h rfl
      rw [dif_neg hnv]
      exact (not_not.mp (mt Set.mem_compl_singleton_iff.mpr hy)).symm
  refine ⟨⟨⟨toF, invF, hleft, hright⟩, ?_⟩⟩
  intro a b
  dsimp only [Equiv.coe_fn_mk, toF]
  by_cases ha : a = v <;> by_cases hb : b = v
  · have ha' : a ∉ ({v}ᶜ : Set V) := fun h => h ha
    have hb' : b ∉ ({v}ᶜ : Set V) := fun h => h hb
    rw [dif_neg ha', dif_neg hb', ha, hb]
    simp
  · have ha' : a ∉ ({v}ᶜ : Set V) := fun h => h ha
    have hb' : b ∈ ({v}ᶜ : Set V) := Set.mem_compl_singleton_iff.mpr hb
    rw [dif_neg ha', dif_pos hb', ha, hw_only (φ ⟨b, hb'⟩).1, hv_only b]
    constructor
    · intro hval
      exact congrArg Subtype.val (φ.injective ((Subtype.ext hval : φ ⟨b, hb'⟩ = ⟨cH, hcH⟩).trans hφc.symm))
    · rintro rfl
      exact congrArg Subtype.val hφc
  · have ha' : a ∈ ({v}ᶜ : Set V) := Set.mem_compl_singleton_iff.mpr ha
    have hb' : b ∉ ({v}ᶜ : Set V) := fun h => h hb
    rw [dif_pos ha', dif_neg hb', hb, H.adj_comm, G.adj_comm, hw_only (φ ⟨a, ha'⟩).1, hv_only a]
    constructor
    · intro hval
      exact congrArg Subtype.val (φ.injective ((Subtype.ext hval : φ ⟨a, ha'⟩ = ⟨cH, hcH⟩).trans hφc.symm))
    · rintro rfl
      exact congrArg Subtype.val hφc
  · have ha' : a ∈ ({v}ᶜ : Set V) := Set.mem_compl_singleton_iff.mpr ha
    have hb' : b ∈ ({v}ᶜ : Set V) := Set.mem_compl_singleton_iff.mpr hb
    rw [dif_pos ha', dif_pos hb']
    exact φ.map_rel_iff (a := ⟨a, ha'⟩) (b := ⟨b, hb'⟩)

private lemma existsUnique_root_of_component {U : Type} [Fintype U]
    (T : SimpleGraph U) (hT : T.IsTree) (c : U)
    (C : (T.induce {c}ᶜ).ConnectedComponent) :
    ∃! u : ({c}ᶜ : Set U), u ∈ C.supp ∧ T.Adj c u.1 := by
  obtain ⟨z, hz⟩ := C.nonempty_supp
  have hzc : z.1 ≠ c := z.2
  obtain ⟨p, hp, _⟩ := hT.connected.exists_path_of_dist c z.1
  have hnp : ¬ p.Nil := Walk.not_nil_of_ne hzc.symm
  let uVal : U := p.snd
  have hadj : T.Adj c uVal := p.adj_snd hnp
  have huc : uVal ∈ ({c}ᶜ : Set U) := Set.mem_compl_singleton_iff.mpr hadj.ne.symm
  let u : ({c}ᶜ : Set U) := ⟨uVal, huc⟩
  have hsupp_tail : ∀ x ∈ p.tail.support, x ∈ ({c}ᶜ : Set U) := by
    intro x hx
    rw [Walk.support_tail_of_not_nil p hnp] at hx
    exact Set.mem_compl_singleton_iff.mpr fun hxc =>
      start_notMem_tail_support_of_isPath hp (hxc ▸ hx)
  let p' : (T.induce {c}ᶜ).Walk u z :=
    (p.tail.induce ({c}ᶜ : Set U) hsupp_tail).copy rfl (Subtype.ext rfl)
  have hreach : (T.induce {c}ᶜ).Reachable u z := ⟨p'⟩
  have hu_mem : u ∈ C.supp := by
    rw [ConnectedComponent.mem_supp_iff] at hz ⊢
    exact (ConnectedComponent.sound hreach).trans hz
  refine ⟨u, ⟨hu_mem, hadj⟩, fun u' ⟨hu'_mem, hadj'⟩ => ?_⟩
  by_contra hne
  have hne_val : uVal ≠ u'.1 := fun h => hne (Subtype.ext h).symm
  obtain ⟨q⟩ := C.reachable_of_mem_supp hu_mem hu'_mem
  let q_path := q.toPath
  let g : T.induce {c}ᶜ →g T := (SimpleGraph.Embedding.induce ({c}ᶜ : Set U)).toHom
  have hqG : (q_path.val.map g).IsPath := q_path.isPath.map Subtype.val_injective
  have hc_not_q : c ∉ (q_path.val.map g).support := by
    rw [Walk.support_map, List.mem_map]
    rintro ⟨x, _, hxc⟩
    exact x.2 hxc
  let two_step : T.Walk uVal u'.1 := Walk.cons hadj.symm (Walk.cons hadj' Walk.nil)
  have htwo_path : two_step.IsPath := by
    simp [two_step, Walk.cons_isPath_iff, hne_val, hadj.ne.symm, hadj'.ne]
  have heq := isTree_path_eq T hT hqG htwo_path
  have hc_in : c ∈ two_step.support := by simp [two_step]
  rw [← heq] at hc_in
  exact hc_not_q hc_in

private lemma component_toSimpleGraph_degree {U : Type} [Fintype U]
    (T : SimpleGraph U) (c : U) (C : (T.induce {c}ᶜ).ConnectedComponent) (x : C.supp) :
    C.toSimpleGraph.degree x = (T.induce {c}ᶜ).degree x.1 := by
  let f : C.supp ↪ ({c}ᶜ : Set U) := ⟨Subtype.val, Subtype.val_injective⟩
  have heq : (C.toSimpleGraph.neighborFinset x).map f = (T.induce {c}ᶜ).neighborFinset x.1 := by
    ext y
    rw [Finset.mem_map, SimpleGraph.mem_neighborFinset]
    constructor
    · rintro ⟨z, hz, rfl⟩
      rw [SimpleGraph.mem_neighborFinset] at hz
      exact hz
    · intro hxy
      have hy : y ∈ C.supp := C.mem_supp_of_adj_mem_supp x.2 hxy
      refine ⟨⟨y, hy⟩, ?_, rfl⟩
      rw [SimpleGraph.mem_neighborFinset]
      exact hxy
  have hcard := congrArg Finset.card heq
  rw [Finset.card_map, C.toSimpleGraph.card_neighborFinset_eq_degree,
    (T.induce {c}ᶜ).card_neighborFinset_eq_degree] at hcard
  exact hcard

private lemma component_degree_sum {U : Type} [Fintype U]
    (T : SimpleGraph U) (hT : T.IsTree) (c : U)
    (C : (T.induce {c}ᶜ).ConnectedComponent) :
    ∑ x : C.supp, T.degree x.1.1 = 2 * Fintype.card C.supp - 1 := by
  obtain ⟨u, ⟨hu_mem, hu_adj⟩, hu_uniq⟩ := existsUnique_root_of_component T hT c C
  let uC : C.supp := ⟨u, hu_mem⟩
  have hdeg_eq : ∀ x : C.supp,
      T.degree x.1.1 = C.toSimpleGraph.degree x + (if x = uC then 1 else 0) := by
    intro x
    rw [component_toSimpleGraph_degree T c C x]
    split_ifs with hxu
    · subst hxu
      exact (degree_induce_compl_singleton_of_adj T u.2 hu_adj.symm).symm
    · have hnadj : ¬ T.Adj x.1.1 c := by
        intro hadj
        have hxeq : x.1 = u := hu_uniq x.1 ⟨x.2, hadj.symm⟩
        exact hxu (Subtype.ext hxeq)
      exact (degree_induce_compl_singleton_of_not_adj T x.1.2 hnadj).symm
  have hsum : ∑ x : C.supp, T.degree x.1.1 =
      (∑ x : C.supp, C.toSimpleGraph.degree x) + ∑ x : C.supp, (if x = uC then 1 else 0) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun x _ => hdeg_eq x
  have hC_tree : C.toSimpleGraph.IsTree :=
    (hT.isAcyclic.induce {c}ᶜ).isTree_connectedComponent C
  have hdeg_sum : (∑ x : C.supp, C.toSimpleGraph.degree x) = 2 * C.toSimpleGraph.edgeFinset.card := by
    convert C.toSimpleGraph.sum_degrees_eq_twice_card_edges
    all_goals exact Iff.rfl
  rw [hdeg_sum] at hsum
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte] at hsum
  have hC_edges : C.toSimpleGraph.edgeFinset.card + 1 = Fintype.card C.supp := by
    convert hC_tree.card_edgeFinset
    all_goals exact Iff.rfl
  have hC_pos : 1 ≤ Fintype.card C.supp := Fintype.card_pos_iff.mpr ⟨uC⟩
  omega

private lemma component_leaves_formula {U : Type} [Fintype U]
    (T : SimpleGraph U) (hT : T.IsTree) (c : U)
    (C : (T.induce {c}ᶜ).ConnectedComponent) :
    let LC := Finset.univ.filter fun x : C.supp => T.degree x.1.1 = 1
    LC.card = 1 + ∑ x ∈ LCᶜ, (T.degree x.1.1 - 2) ∧
      ∀ x ∈ LCᶜ, 2 ≤ T.degree x.1.1 := by
  have hT_pos : ∀ v : U, 1 ≤ T.degree v := by
    intro v
    obtain ⟨w, _⟩ := C.nonempty_supp
    have hwc : c ≠ w.1 := fun h => w.2 (h.symm)
    have : Nontrivial U := ⟨⟨c, w.1, hwc⟩⟩
    exact hT.preconnected.degree_pos_of_nontrivial v
  let LC : Finset C.supp := Finset.univ.filter fun x : C.supp => T.degree x.1.1 = 1
  have hge2 : ∀ x ∈ LCᶜ, 2 ≤ T.degree x.1.1 := by
    intro x hx
    simp only [LC, Finset.mem_compl, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    have := hT_pos x.1.1
    omega
  have hsum := component_degree_sum T hT c C
  have hsplit : (∑ x ∈ LC, T.degree x.1.1) + ∑ x ∈ LCᶜ, T.degree x.1.1 = ∑ x : C.supp, T.degree x.1.1 :=
    Finset.sum_add_sum_compl LC (fun x => T.degree x.1.1)
  have hsum_L : ∑ x ∈ LC, T.degree x.1.1 = LC.card := by
    calc
      ∑ x ∈ LC, T.degree x.1.1 = ∑ _x ∈ LC, 1 := Finset.sum_congr rfl fun x hx => (Finset.mem_filter.mp hx).2
      _ = LC.card := by simp
  have hsum_Lc : ∑ x ∈ LCᶜ, T.degree x.1.1 = 2 * LCᶜ.card + ∑ x ∈ LCᶜ, (T.degree x.1.1 - 2) := by
    calc
      ∑ x ∈ LCᶜ, T.degree x.1.1 = ∑ x ∈ LCᶜ, (2 + (T.degree x.1.1 - 2)) :=
        Finset.sum_congr rfl fun x hx => by have := hge2 x hx; omega
      _ = (∑ _x ∈ LCᶜ, 2) + ∑ x ∈ LCᶜ, (T.degree x.1.1 - 2) := Finset.sum_add_distrib
      _ = 2 * LCᶜ.card + ∑ x ∈ LCᶜ, (T.degree x.1.1 - 2) := by simp [mul_comm]
  have hcard_compl : LC.card + LCᶜ.card = Fintype.card C.supp := by
    rw [Finset.card_compl]
    have : LC.card ≤ Fintype.card C.supp := Finset.card_le_univ LC
    omega
  have hC_pos : 1 ≤ Fintype.card C.supp := by
    obtain ⟨w, hw⟩ := C.nonempty_supp
    exact Fintype.card_pos_iff.mpr ⟨⟨w, hw⟩⟩
  refine ⟨?_, hge2⟩
  change LC.card = 1 + ∑ x ∈ LCᶜ, (T.degree x.1.1 - 2)
  omega

private lemma mem_support_tail_of_ne {U : Type} {T : SimpleGraph U}
    {a b x : U} (w : T.Walk a b) (hx : x ∈ w.support) (hne : x ≠ a) : x ∈ w.support.tail := by
  cases w with
  | nil =>
    simp only [Walk.support_nil, List.mem_singleton] at hx
    exact absurd hx hne
  | cons _ _ =>
    simpa [Walk.support_cons] using Or.resolve_left (List.mem_cons.mp hx) hne

private lemma diam_path_contains_center {U : Type} [Fintype U]
    (T : SimpleGraph U) (hT : T.IsTree) {r : ℕ} (c : U) (hecc : T.eccent c = r)
    {x0 xd : U} (p : T.Walk x0 xd) (hp : p.IsPath) (hplen : p.length = 2 * r) :
    c ∈ p.support ∧ T.dist c x0 = r ∧ T.dist c xd = r := by
  obtain ⟨q1, hq1, hq1len⟩ := hT.connected.exists_path_of_dist x0 c
  obtain ⟨q2, hq2, hq2len⟩ := hT.connected.exists_path_of_dist c xd
  have h1 : T.dist x0 c ≤ r := Nat.cast_le.mp (by
    rw [(hT.connected x0 c).coe_dist_eq_edist, SimpleGraph.edist_comm, ← hecc]
    exact SimpleGraph.edist_le_eccent)
  have h2 : T.dist c xd ≤ r := Nat.cast_le.mp (by
    rw [(hT.connected c xd).coe_dist_eq_edist, ← hecc]
    exact SimpleGraph.edist_le_eccent)
  have hpdist : p.length = T.dist x0 xd := isTree_dist_eq_length_of_isPath T hT p hp
  have htri := hT.connected.dist_triangle (u := x0) (v := c) (w := xd)
  have h1eq : T.dist x0 c = r := by omega
  have h2eq : T.dist c xd = r := by omega
  have hq12_len : (q1.append q2).length = T.dist x0 xd := by
    rw [Walk.length_append, hq1len, hq2len, h1eq, h2eq, ← hpdist, hplen]
    omega
  have hq12_path : (q1.append q2).IsPath :=
    (q1.append q2).isPath_of_length_eq_dist hq12_len
  have heq : q1.append q2 = p := isTree_path_eq T hT hq12_path hp
  have hc_mem : c ∈ p.support := by
    rw [← heq, Walk.mem_support_append_iff]
    exact Or.inl q1.end_mem_support
  rw [SimpleGraph.dist_comm] at h1eq
  exact ⟨hc_mem, h1eq, h2eq⟩

private lemma deg_center_ge_two {U : Type} [Fintype U]
    (T : SimpleGraph U) (hT : T.IsTree) {r : ℕ} (hr : 2 ≤ r)
    (hdiam : T.diam = 2 * r) (c : U) (hecc : T.eccent c = r) :
    2 ≤ T.degree c := by
  have : Nonempty U := hT.connected.nonempty
  obtain ⟨x0, xd, hxd⟩ := T.exists_dist_eq_diam
  obtain ⟨p, hp, hplen⟩ := hT.connected.exists_path_of_dist x0 xd
  have hplen_r : p.length = 2 * r := hplen.trans (hxd.trans hdiam)
  obtain ⟨hc_mem, hcx0, hcxd⟩ := diam_path_contains_center T hT c hecc p hp hplen_r
  obtain ⟨q, s, hq, hs, hp_eq⟩ := hp.mem_support_iff_exists_append.mp hc_mem
  have hcx0_ne : c ≠ x0 := fun h => by rw [h, SimpleGraph.dist_self] at hcx0; omega
  have hcxd_ne : c ≠ xd := fun h => by rw [h, SimpleGraph.dist_self] at hcxd; omega
  have hq_nn : ¬ q.Nil := Walk.not_nil_of_ne hcx0_ne.symm
  have hs_nn : ¬ s.Nil := Walk.not_nil_of_ne hcxd_ne
  have hadj1 : T.Adj c q.penultimate := (q.adj_penultimate hq_nn).symm
  have hadj2 : T.Adj c s.snd := s.adj_snd hs_nn
  have hne12 : q.penultimate ≠ s.snd := by
    have hdisj : q.support.Disjoint s.tail.support := by
      have h1 := (hp_eq ▸ hp).support_nodup
      rw [Walk.support_append, List.nodup_append', ← Walk.support_tail_of_not_nil s hs_nn] at h1
      exact h1.2.2
    have hm1 : q.penultimate ∈ q.support := Walk.getVert_mem_support q (q.length - 1)
    have hm2 : s.snd ∈ s.tail.support := by
      rw [Walk.support_tail_of_not_nil s hs_nn]
      exact s.snd_mem_tail_support hs_nn
    intro heq
    rw [heq] at hm1
    exact hdisj hm1 hm2
  rw [← T.card_neighborFinset_eq_degree]
  have hsub : {q.penultimate, s.snd} ⊆ T.neighborFinset c := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rw [SimpleGraph.mem_neighborFinset]
    rcases hz with rfl | rfl <;> assumption
  calc
    2 = ({q.penultimate, s.snd} : Finset U).card := (Finset.card_pair hne12).symm
    _ ≤ (T.neighborFinset c).card := Finset.card_le_card hsub

private lemma card_component_eq_radius_of_unique_leaf {U : Type} [Fintype U]
    (T : SimpleGraph U) (hT : T.IsTree) {r : ℕ} (hr : 2 ≤ r) (c : U)
    (C : (T.induce {c}ᶜ).ConnectedComponent)
    {x_end : ({c}ᶜ : Set U)} (hx_mem : x_end ∈ C.supp)
    (hx_dist : T.dist c x_end.1 = r)
    (h_all_le2 : ∀ x : C.supp, T.degree x.1.1 ≤ 2)
    (h_uniq_leaf : ∀ x : C.supp, T.degree x.1.1 = 1 → x.1 = x_end) :
    Fintype.card C.supp = r := by
  obtain ⟨u, ⟨hu_mem, hu_adj⟩, hu_uniq⟩ := existsUnique_root_of_component T hT c C
  let uC : C.supp := ⟨u, hu_mem⟩
  let xC : C.supp := ⟨x_end, hx_mem⟩
  have hux_ne : uC ≠ xC := by
    intro h
    have hval : u.1 = x_end.1 := congrArg (fun y : C.supp => y.1.1) h
    have hd : T.dist c u.1 = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hu_adj
    rw [hval, hx_dist] at hd
    omega
  obtain ⟨p, hp, hplen⟩ := hT.connected.exists_path_of_dist c x_end.1
  have hp_len : p.length = r := hplen.trans hx_dist
  have hnp : ¬ p.Nil := Walk.not_nil_of_ne (fun h => by rw [← h, SimpleGraph.dist_self] at hx_dist; omega)
  have p_tail_supp : ∀ y ∈ p.tail.support, y ∈ ({c}ᶜ : Set U) := by
    intro y hy
    rw [Walk.support_tail_of_not_nil p hnp] at hy
    exact Set.mem_compl_singleton_iff.mpr fun hyc =>
      start_notMem_tail_support_of_isPath hp (hyc ▸ hy)
  have hsnd : (⟨p.snd, p_tail_supp p.snd (Walk.start_mem_support _)⟩ : ({c}ᶜ : Set U)) = u := by
    have hreach : (T.induce {c}ᶜ).Reachable ⟨p.snd, p_tail_supp p.snd (Walk.start_mem_support _)⟩ x_end :=
      ⟨(p.tail.induce ({c}ᶜ : Set U) p_tail_supp).copy rfl (Subtype.ext rfl)⟩
    have hsnd_mem : (⟨p.snd, p_tail_supp p.snd (Walk.start_mem_support _)⟩ : ({c}ᶜ : Set U)) ∈ C.supp := by
      rw [ConnectedComponent.mem_supp_iff] at hx_mem ⊢
      exact (ConnectedComponent.sound hreach).trans hx_mem
    exact hu_uniq ⟨p.snd, _⟩ ⟨hsnd_mem, p.adj_snd hnp⟩
  let p' : (T.induce {c}ᶜ).Walk u x_end :=
    (p.tail.induce ({c}ᶜ : Set U) p_tail_supp).copy hsnd (Subtype.ext rfl)
  have hp' : p'.IsPath := by
    rw [Walk.isPath_copy]
    refine Walk.IsPath.of_map (f := (SimpleGraph.Embedding.induce ({c}ᶜ : Set U)).toHom) ?_
    rw [Walk.map_induce]
    exact hp.tail
  have hp'_len : p'.length = r - 1 := by
    rw [Walk.length_copy, length_walk_induce, Walk.length_tail, hp_len]
  have hC_tree : C.toSimpleGraph.IsTree :=
    (hT.isAcyclic.induce {c}ᶜ).isTree_connectedComponent C
  have hp'_mem_C : ∀ z ∈ p'.support, z ∈ C.supp := by
    intro z hz
    obtain ⟨q1, _, _, _, _⟩ := hp'.mem_support_iff_exists_append.mp hz
    have hreach : (T.induce {c}ᶜ).Reachable u z := ⟨q1⟩
    rw [ConnectedComponent.mem_supp_iff] at hu_mem ⊢
    exact (ConnectedComponent.sound hreach).symm.trans hu_mem
  let pC_ind : ((T.induce {c}ᶜ).induce C.supp).Walk uC xC := p'.induce C.supp hp'_mem_C
  have hpC_ind : pC_ind.IsPath := by
    refine Walk.IsPath.of_map (f := (SimpleGraph.Embedding.induce C.supp).toHom) ?_
    rw [Walk.map_induce]
    exact hp'
  have hpC_ind_len : pC_ind.length = r - 1 :=
    (length_walk_induce (T.induce {c}ᶜ) C.supp p' hp'_mem_C).trans hp'_len
  let pC : C.toSimpleGraph.Walk uC xC := pC_ind
  have hpC : pC.IsPath := hpC_ind
  have hpC_len : pC.length = r - 1 := hpC_ind_len
  have hdeg_uC : C.toSimpleGraph.degree uC = 1 := by
    rw [component_toSimpleGraph_degree T c C uC]
    dsimp only [uC]
    have h1 := degree_induce_compl_singleton_of_adj T u.2 hu_adj.symm
    rw [Subtype.coe_eta] at h1
    have hge1 : 1 ≤ (T.induce {c}ᶜ).degree u := by
      rw [← component_toSimpleGraph_degree T c C uC]
      have : Nontrivial C.supp := ⟨⟨uC, xC, hux_ne⟩⟩
      exact hC_tree.preconnected.degree_pos_of_nontrivial uC
    have hle2 : T.degree u.1 ≤ 2 := h_all_le2 uC
    omega
  have hdeg_xC : C.toSimpleGraph.degree xC = 1 := by
    rw [component_toSimpleGraph_degree T c C xC]
    have hx_nadj : ¬ T.Adj x_end.1 c := by
      intro hadj
      have hd : T.dist c x_end.1 = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hadj.symm
      rw [hx_dist] at hd
      omega
    rw [degree_induce_compl_singleton_of_not_adj T x_end.2 hx_nadj]
    have : Nontrivial C.supp := ⟨⟨uC, xC, hux_ne⟩⟩
    have hge1 : 1 ≤ T.degree x_end.1 := by
      rw [← degree_induce_compl_singleton_of_not_adj T x_end.2 hx_nadj,
        ← component_toSimpleGraph_degree T c C xC]
      exact hC_tree.preconnected.degree_pos_of_nontrivial xC
    have hle1 : ¬ 2 ≤ T.degree x_end.1 := by
      intro h2
      obtain ⟨hLC_eq, _⟩ := component_leaves_formula T hT c C
      let LC : Finset C.supp := Finset.univ.filter fun x : C.supp => T.degree x.1.1 = 1
      have hpos : 0 < LC.card := by dsimp [LC] at hLC_eq ⊢; omega
      obtain ⟨w, hw⟩ := Finset.card_pos.mp hpos
      simp only [LC, Finset.mem_filter, Finset.mem_univ, true_and] at hw
      have hwx : w.1 = x_end := h_uniq_leaf w hw
      rw [hwx] at hw
      omega
    omega
  have hdeg_int : ∀ y : C.supp, y ≠ uC → y ≠ xC → C.toSimpleGraph.degree y ≤ 2 := by
    intro y _ _
    rw [component_toSimpleGraph_degree T c C y]
    exact (degree_induce_compl_le T y.1.2).trans (h_all_le2 y)
  have hsupp_eq : ∀ y : C.supp, y ∈ pC.support := by
    intro y
    by_contra hy
    obtain ⟨q, hq, _⟩ := hC_tree.connected.exists_path_of_dist y uC
    obtain ⟨z, q₁, _, hz_mem, hq_eq, hq_first⟩ :=
      split_walk_first_mem C.toSimpleGraph {w | w ∈ pC.support} q pC.start_mem_support
    have hq1_nn : ¬ q₁.Nil := Walk.not_nil_of_ne (fun h => hy (h ▸ hz_mem))
    have hadj_z : C.toSimpleGraph.Adj z q₁.penultimate := (q₁.adj_penultimate hq1_nn).symm
    have hpen_not : q₁.penultimate ∉ pC.support := by
      intro hm
      have hmem1 : q₁.penultimate ∈ q₁.support := Walk.getVert_mem_support q₁ (q₁.length - 1)
      have heq : q₁.penultimate = z := hq_first q₁.penultimate hmem1 hm
      exact C.toSimpleGraph.ne_of_adj hadj_z heq.symm
    by_cases hzu : z = uC
    · subst hzu
      have hpC_nn : ¬ pC.Nil := Walk.not_nil_of_ne hux_ne
      have hadj_p : C.toSimpleGraph.Adj uC pC.snd := pC.adj_snd hpC_nn
      have hsnd_mem : pC.snd ∈ pC.support := List.mem_of_mem_tail (pC.snd_mem_tail_support hpC_nn)
      have hne : pC.snd ≠ q₁.penultimate := fun h => hpen_not (h ▸ hsnd_mem)
      have h2 : 2 ≤ C.toSimpleGraph.degree uC := by
        rw [← C.toSimpleGraph.card_neighborFinset_eq_degree]
        have hsub : {pC.snd, q₁.penultimate} ⊆ C.toSimpleGraph.neighborFinset uC := by
          intro a ha
          simp only [Finset.mem_insert, Finset.mem_singleton] at ha
          rw [SimpleGraph.mem_neighborFinset]
          rcases ha with rfl | rfl <;> assumption
        calc
          2 = ({pC.snd, q₁.penultimate} : Finset C.supp).card := (Finset.card_pair hne).symm
          _ ≤ (C.toSimpleGraph.neighborFinset uC).card := Finset.card_le_card hsub
      omega
    · by_cases hzx : z = xC
      · subst hzx
        have hpC_nn : ¬ pC.Nil := Walk.not_nil_of_ne hux_ne
        have hadj_p : C.toSimpleGraph.Adj xC pC.penultimate := (pC.adj_penultimate hpC_nn).symm
        have hpen_p_mem : pC.penultimate ∈ pC.support := Walk.getVert_mem_support pC (pC.length - 1)
        have hne : pC.penultimate ≠ q₁.penultimate := fun h => hpen_not (h ▸ hpen_p_mem)
        have h2 : 2 ≤ C.toSimpleGraph.degree xC := by
          rw [← C.toSimpleGraph.card_neighborFinset_eq_degree]
          have hsub : {pC.penultimate, q₁.penultimate} ⊆ C.toSimpleGraph.neighborFinset xC := by
            intro a ha
            simp only [Finset.mem_insert, Finset.mem_singleton] at ha
            rw [SimpleGraph.mem_neighborFinset]
            rcases ha with rfl | rfl <;> assumption
          calc
            2 = ({pC.penultimate, q₁.penultimate} : Finset C.supp).card := (Finset.card_pair hne).symm
            _ ≤ (C.toSimpleGraph.neighborFinset xC).card := Finset.card_le_card hsub
        omega
      · obtain ⟨a, b, ha, hb, hpC_eq⟩ := hpC.mem_support_iff_exists_append.mp hz_mem
        have ha_nn : ¬ a.Nil := Walk.not_nil_of_ne (fun h => hzu h.symm)
        have hb_nn : ¬ b.Nil := Walk.not_nil_of_ne hzx
        have hadj1 : C.toSimpleGraph.Adj z a.penultimate := (a.adj_penultimate ha_nn).symm
        have hadj2 : C.toSimpleGraph.Adj z b.snd := b.adj_snd hb_nn
        have ha_pen_mem : a.penultimate ∈ a.support := Walk.getVert_mem_support a (a.length - 1)
        have hm1 : a.penultimate ∈ pC.support := hpC_eq ▸ Walk.support_subset_support_append_left a b ha_pen_mem
        have hm2 : b.snd ∈ pC.support := hpC_eq ▸ Walk.support_subset_support_append_right a b (List.mem_of_mem_tail (b.snd_mem_tail_support hb_nn))
        have hne12 : a.penultimate ≠ b.snd := by
          have hdisj : a.support.Disjoint b.tail.support := by
            have h1 := (hpC_eq ▸ hpC).support_nodup
            rw [Walk.support_append, List.nodup_append', ← Walk.support_tail_of_not_nil b hb_nn] at h1
            exact h1.2.2
          have hb_snd : b.snd ∈ b.tail.support := by
            rw [Walk.support_tail_of_not_nil b hb_nn]
            exact b.snd_mem_tail_support hb_nn
          intro heq
          rw [heq] at ha_pen_mem
          exact hdisj ha_pen_mem hb_snd
        have hne13 : a.penultimate ≠ q₁.penultimate := fun h => hpen_not (h ▸ hm1)
        have hne23 : b.snd ≠ q₁.penultimate := fun h => hpen_not (h ▸ hm2)
        have h3 : 3 ≤ C.toSimpleGraph.degree z := by
          rw [← C.toSimpleGraph.card_neighborFinset_eq_degree]
          have hsub : {a.penultimate, b.snd, q₁.penultimate} ⊆ C.toSimpleGraph.neighborFinset z := by
            intro w hw
            simp only [Finset.mem_insert, Finset.mem_singleton] at hw
            rw [SimpleGraph.mem_neighborFinset]
            rcases hw with rfl | rfl | rfl <;> assumption
          have hc3 : ({a.penultimate, b.snd, q₁.penultimate} : Finset C.supp).card = 3 := by
            rw [Finset.card_insert_of_notMem, Finset.card_pair hne23]
            simp [hne12, hne13]
          exact hc3 ▸ Finset.card_le_card hsub
        have := hdeg_int z hzu hzx
        omega
  have hsupp_ind : ∀ y : C.supp, y ∈ pC_ind.support := hsupp_eq
  have hcard_eq : Fintype.card C.supp = pC_ind.support.toFinset.card := by
    have huniv : pC_ind.support.toFinset = Finset.univ :=
      Finset.eq_univ_iff_forall.mpr fun y => List.mem_toFinset.mpr (hsupp_ind y)
    rw [huniv, Finset.card_univ]
  rw [hcard_eq, List.toFinset_card_of_nodup hpC_ind.support_nodup, pC_ind.length_support, hpC_ind_len]
  omega

private lemma card_connectedComponent_eq_degree {U : Type} [Fintype U]
    (T : SimpleGraph U) (hT : T.IsTree) (c : U) :
    Fintype.card (T.induce {c}ᶜ).ConnectedComponent = T.degree c := by
  let f : (T.induce {c}ᶜ).ConnectedComponent → T.neighborFinset c := fun C =>
    let u := (existsUnique_root_of_component T hT c C).choose
    ⟨u.1, (T.mem_neighborFinset c u.1).mpr (existsUnique_root_of_component T hT c C).choose_spec.1.2⟩
  let g : T.neighborFinset c → (T.induce {c}ᶜ).ConnectedComponent := fun u =>
    (T.induce {c}ᶜ).connectedComponentMk ⟨u.1, Set.mem_compl_singleton_iff.mpr ((T.mem_neighborFinset c u.1).mp u.2).ne.symm⟩
  have hleft : Function.LeftInverse g f := by
    intro C
    dsimp only [f, g]
    have hu := (existsUnique_root_of_component T hT c C).choose_spec.1.1
    exact (ConnectedComponent.mem_supp_iff C _).mp hu
  have hright : Function.RightInverse g f := by
    intro u
    dsimp only [f, g]
    apply Subtype.ext
    have hadj : T.Adj c u.1 := (T.mem_neighborFinset c u.1).mp u.2
    have huc : u.1 ∈ ({c}ᶜ : Set U) := Set.mem_compl_singleton_iff.mpr hadj.ne.symm
    let u_sub : ({c}ᶜ : Set U) := ⟨u.1, huc⟩
    let C := (T.induce {c}ᶜ).connectedComponentMk u_sub
    have hu_mem : u_sub ∈ C.supp := rfl
    have h_eq := ((existsUnique_root_of_component T hT c C).choose_spec.2 u_sub ⟨hu_mem, hadj⟩).symm
    exact congrArg (fun z : ({c}ᶜ : Set U) => z.1) h_eq
  rw [Fintype.card_congr ⟨f, g, hleft, hright⟩, Fintype.card_coe, T.card_neighborFinset_eq_degree]

private lemma sum_card_connectedComponent_eq {U : Type} [Fintype U]
    (T : SimpleGraph U) (c : U) :
    (∑ C : (T.induce {c}ᶜ).ConnectedComponent, Fintype.card C.supp) + 1 = Fintype.card U := by
  have h1 : (∑ C : (T.induce {c}ᶜ).ConnectedComponent, Fintype.card C.supp) =
      Fintype.card ({c}ᶜ : Set U) := by
    rw [← Fintype.card_sigma]
    refine Fintype.card_congr
      ⟨fun ⟨_, ⟨x, _⟩⟩ => x, fun (x : ({c}ᶜ : Set U)) => ⟨(T.induce {c}ᶜ).connectedComponentMk x, ⟨x, rfl⟩⟩, ?_, ?_⟩
    · rintro ⟨C, ⟨x, hx⟩⟩
      have hCx : (T.induce {c}ᶜ).connectedComponentMk x = C := (ConnectedComponent.mem_supp_iff C x).mp hx
      subst hCx
      rfl
    · intro x
      rfl
  have h2 : Fintype.card ({c}ᶜ : Set U) + 1 = Fintype.card U := by
    have e : ({c}ᶜ : Set U) ≃ ↥(Finset.univ.erase c) :=
      ⟨fun x => ⟨x.1, Finset.mem_erase.mpr ⟨x.2, Finset.mem_univ _⟩⟩,
       fun x => ⟨x.1, (Finset.mem_erase.mp x.2).1⟩,
       fun _ => rfl, fun _ => rfl⟩
    rw [Fintype.card_congr e, Fintype.card_coe, Finset.card_erase_of_mem (Finset.mem_univ c),
      Finset.card_univ]
    have : 1 ≤ Fintype.card U := Fintype.card_pos_iff.mpr ⟨c⟩
    omega
  omega

private lemma degree_pathG_le_two (n : ℕ) (i : Fin n) : (pathG n).degree i ≤ 2 := by
  rw [← (pathG n).card_neighborFinset_eq_degree]
  have hsub : (pathG n).neighborFinset i ⊆
      (if h1 : i.val + 1 < n then {⟨i.val + 1, h1⟩} else ∅) ∪
      (if h2 : 0 < i.val then {⟨i.val - 1, by omega⟩} else ∅) := by
    intro j hj
    rw [SimpleGraph.mem_neighborFinset] at hj
    rcases hj with h | h
    · refine Finset.mem_union_left _ ?_
      have hj1 : i.val + 1 < n := by rw [h]; exact j.isLt
      rw [dif_pos hj1, Finset.mem_singleton]
      exact Fin.ext h.symm
    · refine Finset.mem_union_right _ ?_
      have hj2 : 0 < i.val := by omega
      rw [dif_pos hj2, Finset.mem_singleton]
      exact Fin.ext (by simp; omega)
  refine (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans ?_)
  split_ifs <;> simp

private lemma card_edgeFinset_pathG (n : ℕ) (hn : 1 ≤ n) :
    (pathG n).edgeFinset.card + 1 = n := by
  have hconn : (pathG n).Connected := by
    have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    refine Connected.mk fun i j => ?_
    suffices h0 : ∀ k : Fin n, (pathG n).Reachable ⟨0, hn⟩ k from
      (h0 i).symm.trans (h0 j)
    intro ⟨k, hk⟩
    induction k with
    | zero => exact Reachable.rfl
    | succ k ih =>
      have hk' : k < n := by omega
      have hadj : (pathG n).Adj ⟨k, hk'⟩ ⟨k + 1, hk⟩ := Or.inl rfl
      exact (ih hk').trans hadj.reachable
  have hacyc : (pathG n).IsAcyclic := by
    intro u c hc
    have hne : c.support.toFinset.Nonempty := ⟨u, List.mem_toFinset.mpr c.start_mem_support⟩
    let m := c.support.toFinset.max' hne
    have hm_mem : m ∈ c.support := List.mem_toFinset.mp (Finset.max'_mem _ hne)
    let c' := c.rotate m hm_mem
    have hc' : c'.IsCycle := hc.rotate hm_mem
    have hperm := (c.support_rotate m hm_mem).perm
    have hadj1 : (pathG n).Adj m c'.snd := c'.adj_snd hc'.not_nil
    have hadj2 : (pathG n).Adj m c'.penultimate := (c'.adj_penultimate hc'.not_nil).symm
    have hsnd_tail : c'.snd ∈ c'.support.tail := c'.snd_mem_tail_support hc'.not_nil
    have hsnd_mem : c'.snd ∈ c.support := List.mem_of_mem_tail (hperm.subset hsnd_tail)
    have hpen_ne : c'.penultimate ≠ m := hadj2.ne.symm
    have hpen_tail : c'.penultimate ∈ c'.support.tail :=
      mem_support_tail_of_ne c' (Walk.getVert_mem_support c' (c'.length - 1)) hpen_ne
    have hpen_mem : c'.penultimate ∈ c.support := List.mem_of_mem_tail (hperm.subset hpen_tail)
    have hsnd_le : c'.snd.val ≤ m.val :=
      Finset.le_max' c.support.toFinset c'.snd (List.mem_toFinset.mpr hsnd_mem)
    have hpen_le : c'.penultimate.val ≤ m.val :=
      Finset.le_max' c.support.toFinset c'.penultimate (List.mem_toFinset.mpr hpen_mem)
    have h1 : m.val + 1 = c'.snd.val ∨ c'.snd.val + 1 = m.val := hadj1
    have h2 : m.val + 1 = c'.penultimate.val ∨ c'.penultimate.val + 1 = m.val := hadj2
    have heq : c'.snd = c'.penultimate := Fin.ext (by omega)
    exact hc'.snd_ne_penultimate heq
  have htree := SimpleGraph.IsTree.card_edgeFinset ⟨hconn, hacyc⟩
  simpa [Fintype.card_fin] using htree

private lemma path_in_walk_support {U : Type} (T : SimpleGraph U) {a b z₁ z₂ : U}
    (p : T.Walk a b) (hp : p.IsPath) (hz1 : z₁ ∈ p.support) (hz2 : z₂ ∈ p.support) :
    ∃ q : T.Walk z₁ z₂, q.IsPath ∧ ∀ x ∈ q.support, x ∈ p.support := by
  obtain ⟨p1, p2, hp1, hp2, hp_eq⟩ := hp.mem_support_iff_exists_append.mp hz1
  have hz2' : z₂ ∈ p1.support ∨ z₂ ∈ p2.support :=
    (Walk.mem_support_append_iff p1 p2).mp (hp_eq ▸ hz2)
  rcases hz2' with hz2_1 | hz2_2
  · let q := (p1.dropUntil z₂ hz2_1).reverse
    refine ⟨q, (hp1.dropUntil hz2_1).reverse, fun x hx => ?_⟩
    rw [Walk.support_reverse, List.mem_reverse] at hx
    exact hp_eq ▸ Walk.support_subset_support_append_left p1 p2
      (p1.support_dropUntil_subset_support hz2_1 hx)
  · let q := p2.takeUntil z₂ hz2_2
    refine ⟨q, hp2.takeUntil hz2_2, fun x hx => ?_⟩
    exact hp_eq ▸ Walk.support_subset_support_append_right p1 p2
      (p2.support_takeUntil_subset_support hz2_2 hx)

private lemma contradict_of_deg_center_lt {V W : Type} [Fintype V] [Fintype W]
    (hV : 3 ≤ Fintype.card V)
    (G : SimpleGraph V) (H : SimpleGraph W) (σ : V ≃ W)
    (hTG : G.IsTree) (hTH : H.IsTree)
    (hσ : ∀ v : V, Nonempty (G.induce {v}ᶜ ≃g H.induce {σ v}ᶜ))
    (hdeg : ∀ v : V, (G.neighborSet v).ncard = (H.neighborSet (σ v)).ncard)
    (hnonpath : ∃ v : V, 3 ≤ (G.neighborSet v).ncard)
    {r : ℕ} (hr : 2 ≤ r) (hdiamG : G.diam = 2 * r) (hdiamH : H.diam = 2 * r)
    (cG : V) (cH : W)
    (heccG : G.eccent cG = r) (heccH : H.eccent cH = r)
    (huG : ∀ v : V, v ≠ cG → (r : ℕ∞) < G.eccent v)
    (huH : ∀ w : W, w ≠ cH → (r : ℕ∞) < H.eccent w)
    (hsub : ∀ (U : Type) [Fintype U] (Q : SimpleGraph U),
      Fintype.card U < Fintype.card V →
      {S : Finset V | Nonempty (G.induce (S : Set V) ≃g Q)}.ncard =
        {T : Finset W | Nonempty (H.induce (T : Set W) ≃g Q)}.ncard)
    (hlt : H.degree cH < G.degree cG) :
    False := by
  have hcard : Fintype.card V = Fintype.card W := Fintype.card_congr σ
  have hnonpath' : ∃ v : V, 3 ≤ G.degree v := by
    obtain ⟨v, hv⟩ := hnonpath
    exact ⟨v, by rw [← ncard_neighborSet_eq_degree]; exact hv⟩
  have hgood_adj : ∀ v : V, G.degree v = 1 → (G.induce {v}ᶜ).diam = 2 * r →
      G.Adj cG v ∧ G.degree cG = H.degree cH + 1 := by
    intro v hv1 hdiam'
    have hw1 : H.degree (σ v) = 1 := by
      rw [← ncard_neighborSet_eq_degree, ← hdeg v, ncard_neighborSet_eq_degree, hv1]
    obtain ⟨φ⟩ := hσ v
    obtain ⟨hcG, hcH, hφc⟩ :=
      iso_map_center_of_good_leaf G H hTG hTH (by omega) cG cH heccG huG heccH huH hv1 hw1 hdiam' φ
    have hdeg_ind : (G.induce {v}ᶜ).degree ⟨cG, hcG⟩ = (H.induce {σ v}ᶜ).degree ⟨cH, hcH⟩ := by
      rw [← hφc]
      exact (φ.degree_eq ⟨cG, hcG⟩).symm
    have hleH : (H.induce {σ v}ᶜ).degree ⟨cH, hcH⟩ ≤ H.degree cH :=
      degree_induce_compl_le H hcH
    have hadjG : G.Adj cG v := by
      by_contra hnadj
      rw [degree_induce_compl_singleton_of_not_adj G hcG hnadj] at hdeg_ind
      omega
    refine ⟨hadjG, ?_⟩
    have h_eq1 := degree_induce_compl_singleton_of_adj G hcG hadjG
    omega
  obtain ⟨v_good, hv_good1, hv_good_diam⟩ := exists_good_leaf G hTG hV hnonpath' hr hdiamG
  have hdeg_eq : G.degree cG = H.degree cH + 1 := (hgood_adj v_good hv_good1 hv_good_diam).2
  have : Nonempty V := hTG.connected.nonempty
  obtain ⟨x0, xd, hxd⟩ := G.exists_dist_eq_diam
  obtain ⟨p, hp, hplen⟩ := hTG.connected.exists_path_of_dist x0 xd
  have hplen_r : p.length = 2 * r := hplen.trans (hxd.trans hdiamG)
  have hxd_r : G.dist x0 xd = 2 * r := hxd.trans hdiamG
  obtain ⟨hcG_mem, hcG_x0, hcG_xd⟩ := diam_path_contains_center G hTG cG heccG p hp hplen_r
  have hx0_ne : x0 ≠ cG := fun h => by rw [← h, SimpleGraph.dist_self] at hcG_x0; omega
  have hxd_ne : xd ≠ cG := fun h => by rw [← h, SimpleGraph.dist_self] at hcG_xd; omega
  let x0' : ({cG}ᶜ : Set V) := ⟨x0, hx0_ne⟩
  let xd' : ({cG}ᶜ : Set V) := ⟨xd, hxd_ne⟩
  let C₁ := (G.induce {cG}ᶜ).connectedComponentMk x0'
  let C₂ := (G.induce {cG}ᶜ).connectedComponentMk xd'
  have hC12 : C₁ ≠ C₂ := by
    intro heq
    have hreach : (G.induce {cG}ᶜ).Reachable x0' xd' := ConnectedComponent.exact heq
    obtain ⟨q⟩ := hreach
    let q_path := q.toPath
    let g : G.induce {cG}ᶜ →g G := (SimpleGraph.Embedding.induce ({cG}ᶜ : Set V)).toHom
    have hqp : q_path.val.map g = p :=
      isTree_path_eq G hTG (q_path.isPath.map Subtype.val_injective) hp
    have hc_not : cG ∉ (q_path.val.map g).support := by
      rw [Walk.support_map, List.mem_map]
      rintro ⟨y, _, hyc⟩
      exact y.2 hyc
    rw [hqp] at hc_not
    exact hc_not hcG_mem
  have h_other_card : ∀ C : (G.induce {cG}ᶜ).ConnectedComponent,
      C ≠ C₁ → C ≠ C₂ → Fintype.card C.supp = 1 := by
    intro C hne1 hne2
    by_contra hcard1
    obtain ⟨z0, hz0⟩ := C.nonempty_supp
    have hC_pos : 1 ≤ Fintype.card C.supp := Fintype.card_pos_iff.mpr ⟨⟨z0, hz0⟩⟩
    have hC_ge2 : 2 ≤ Fintype.card C.supp := by omega
    have hx0_not : x0' ∉ C.supp := fun hm => hne1 ((ConnectedComponent.mem_supp_iff C x0').mp hm).symm
    have hxd_not : xd' ∉ C.supp := fun hm => hne2 ((ConnectedComponent.mem_supp_iff C xd').mp hm).symm
    obtain ⟨u, ⟨hu_mem, hu_adj⟩, hu_uniq⟩ := existsUnique_root_of_component G hTG cG C
    let uC : C.supp := ⟨u, hu_mem⟩
    have hC_tree : C.toSimpleGraph.IsTree := (hTG.isAcyclic.induce {cG}ᶜ).isTree_connectedComponent C
    have hC_nt : Nontrivial C.supp := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
    have hC_deg_u : 1 ≤ C.toSimpleGraph.degree uC := hC_tree.preconnected.degree_pos_of_nontrivial uC
    have hu_deg2 : 2 ≤ G.degree u.1 := by
      rw [component_toSimpleGraph_degree G cG C uC] at hC_deg_u
      dsimp only [uC] at hC_deg_u
      have h_eq := degree_induce_compl_singleton_of_adj G u.2 hu_adj.symm
      rw [Subtype.coe_eta] at h_eq
      omega
    obtain ⟨hLC_eq, _⟩ := component_leaves_formula G hTG cG C
    let LC : Finset C.supp := Finset.univ.filter fun x : C.supp => G.degree x.1.1 = 1
    have hLC_pos : 0 < LC.card := by dsimp [LC] at hLC_eq ⊢; omega
    obtain ⟨w, hw⟩ := Finset.card_pos.mp hLC_pos
    simp only [LC, Finset.mem_filter, Finset.mem_univ, true_and] at hw
    have hwx0 : w.1.1 ≠ x0 := fun h => hx0_not ((Subtype.ext h : w.1 = x0') ▸ w.2)
    have hwxd : w.1.1 ≠ xd := fun h => hxd_not ((Subtype.ext h : w.1 = xd') ▸ w.2)
    have hw_diam : (G.induce {w.1.1}ᶜ).diam = 2 * r :=
      good_leaf_of_ne_diam_ends G hTG hr hdiamG hxd_r hw hwx0 hwxd
    have hw_adj : G.Adj cG w.1.1 := (hgood_adj w.1.1 hw hw_diam).1
    have hwu : w.1 = u := hu_uniq w.1 ⟨w.2, hw_adj⟩
    rw [hwu] at hw
    omega
  have h_C1_props : (∀ x : C₁.supp, G.degree x.1.1 ≤ 2) ∧ Fintype.card C₁.supp = r := by
    have hxd_not : xd' ∉ C₁.supp := fun hm => hC12 ((ConnectedComponent.mem_supp_iff C₁ xd').mp hm).symm
    have huniq1 : ∀ x : C₁.supp, G.degree x.1.1 = 1 → x.1 = x0' := by
      intro x hx1
      by_contra hx_ne
      have hx_x0 : x.1.1 ≠ x0 := fun h => hx_ne (Subtype.ext h)
      have hx_xd : x.1.1 ≠ xd := fun h => hxd_not ((Subtype.ext h : x.1 = xd') ▸ x.2)
      have hxdiam : (G.induce {x.1.1}ᶜ).diam = 2 * r :=
        good_leaf_of_ne_diam_ends G hTG hr hdiamG hxd_r hx1 hx_x0 hx_xd
      have hx_adj : G.Adj cG x.1.1 := (hgood_adj x.1.1 hx1 hxdiam).1
      obtain ⟨u, ⟨hu_mem, hu_adj⟩, hu_uniq⟩ := existsUnique_root_of_component G hTG cG C₁
      have hxu : x.1 = u := hu_uniq x.1 ⟨x.2, hx_adj⟩
      have hC1_ge2 : 2 ≤ Fintype.card C₁.supp := by
        have hux_ne : (⟨u, hu_mem⟩ : C₁.supp) ≠ ⟨x0', rfl⟩ := by
          intro heq
          have hval : u.1 = x0 := congrArg (fun y : C₁.supp => y.1.1) heq
          have hd : G.dist cG u.1 = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hu_adj
          rw [hval, hcG_x0] at hd
          omega
        exact Fintype.one_lt_card_iff_nontrivial.mpr ⟨⟨_, _, hux_ne⟩⟩
      have hC1_tree : C₁.toSimpleGraph.IsTree := (hTG.isAcyclic.induce {cG}ᶜ).isTree_connectedComponent C₁
      have hC1_nt : Nontrivial C₁.supp := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
      have hdu : 1 ≤ C₁.toSimpleGraph.degree (⟨u, hu_mem⟩ : C₁.supp) :=
        hC1_tree.preconnected.degree_pos_of_nontrivial _
      rw [component_toSimpleGraph_degree] at hdu
      dsimp only at hdu
      have h_eq := degree_induce_compl_singleton_of_adj G u.2 hu_adj.symm
      rw [Subtype.coe_eta] at h_eq
      rw [hxu] at hx1
      omega
    obtain ⟨hLC_eq, hLC_ge2⟩ := component_leaves_formula G hTG cG C₁
    let LC : Finset C₁.supp := Finset.univ.filter fun x : C₁.supp => G.degree x.1.1 = 1
    have hLC_sub : LC ⊆ {⟨x0', rfl⟩} := by
      intro x hx
      simp only [LC, Finset.mem_filter, Finset.mem_univ, true_and] at hx
      rw [Finset.mem_singleton]
      exact Subtype.ext (huniq1 x hx)
    have hLC_le1 : LC.card ≤ 1 := (Finset.card_le_card hLC_sub).trans (by simp)
    have hsum_zero : ∑ x ∈ LCᶜ, (G.degree x.1.1 - 2) = 0 := by
      dsimp [LC] at hLC_eq hLC_le1 ⊢
      omega
    have hall_le2 : ∀ x : C₁.supp, G.degree x.1.1 ≤ 2 := by
      intro x
      by_cases hxL : x ∈ LC
      · simp only [LC, Finset.mem_filter, Finset.mem_univ, true_and] at hxL
        omega
      · have hxLc : x ∈ LCᶜ := Finset.mem_compl.mpr hxL
        have hle_sum : G.degree x.1.1 - 2 ≤ ∑ y ∈ LCᶜ, (G.degree y.1.1 - 2) :=
          Finset.single_le_sum (f := fun y : C₁.supp => G.degree y.1.1 - 2) (fun _ _ => Nat.zero_le _) hxLc
        rw [hsum_zero] at hle_sum
        have := hLC_ge2 x hxLc
        omega
    exact ⟨hall_le2, card_component_eq_radius_of_unique_leaf G hTG hr cG C₁ rfl hcG_x0 hall_le2 huniq1⟩
  have h_C2_props : (∀ x : C₂.supp, G.degree x.1.1 ≤ 2) ∧ Fintype.card C₂.supp = r := by
    have hx0_not : x0' ∉ C₂.supp := fun hm => hC12 ((ConnectedComponent.mem_supp_iff C₂ x0').mp hm)
    have huniq2 : ∀ x : C₂.supp, G.degree x.1.1 = 1 → x.1 = xd' := by
      intro x hx1
      by_contra hx_ne
      have hx_x0 : x.1.1 ≠ x0 := fun h => hx0_not ((Subtype.ext h : x.1 = x0') ▸ x.2)
      have hx_xd : x.1.1 ≠ xd := fun h => hx_ne (Subtype.ext h)
      have hxdiam : (G.induce {x.1.1}ᶜ).diam = 2 * r :=
        good_leaf_of_ne_diam_ends G hTG hr hdiamG hxd_r hx1 hx_x0 hx_xd
      have hx_adj : G.Adj cG x.1.1 := (hgood_adj x.1.1 hx1 hxdiam).1
      obtain ⟨u, ⟨hu_mem, hu_adj⟩, hu_uniq⟩ := existsUnique_root_of_component G hTG cG C₂
      have hxu : x.1 = u := hu_uniq x.1 ⟨x.2, hx_adj⟩
      have hC2_ge2 : 2 ≤ Fintype.card C₂.supp := by
        have hux_ne : (⟨u, hu_mem⟩ : C₂.supp) ≠ ⟨xd', rfl⟩ := by
          intro heq
          have hval : u.1 = xd := congrArg (fun y : C₂.supp => y.1.1) heq
          have hd : G.dist cG u.1 = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hu_adj
          rw [hval, hcG_xd] at hd
          omega
        exact Fintype.one_lt_card_iff_nontrivial.mpr ⟨⟨_, _, hux_ne⟩⟩
      have hC2_tree : C₂.toSimpleGraph.IsTree := (hTG.isAcyclic.induce {cG}ᶜ).isTree_connectedComponent C₂
      have hC2_nt : Nontrivial C₂.supp := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
      have hdu : 1 ≤ C₂.toSimpleGraph.degree (⟨u, hu_mem⟩ : C₂.supp) :=
        hC2_tree.preconnected.degree_pos_of_nontrivial _
      rw [component_toSimpleGraph_degree] at hdu
      dsimp only at hdu
      have h_eq := degree_induce_compl_singleton_of_adj G u.2 hu_adj.symm
      rw [Subtype.coe_eta] at h_eq
      rw [hxu] at hx1
      omega
    obtain ⟨hLC_eq, hLC_ge2⟩ := component_leaves_formula G hTG cG C₂
    let LC : Finset C₂.supp := Finset.univ.filter fun x : C₂.supp => G.degree x.1.1 = 1
    have hLC_sub : LC ⊆ {⟨xd', rfl⟩} := by
      intro x hx
      simp only [LC, Finset.mem_filter, Finset.mem_univ, true_and] at hx
      rw [Finset.mem_singleton]
      exact Subtype.ext (huniq2 x hx)
    have hLC_le1 : LC.card ≤ 1 := (Finset.card_le_card hLC_sub).trans (by simp)
    have hsum_zero : ∑ x ∈ LCᶜ, (G.degree x.1.1 - 2) = 0 := by
      dsimp [LC] at hLC_eq hLC_le1 ⊢
      omega
    have hall_le2 : ∀ x : C₂.supp, G.degree x.1.1 ≤ 2 := by
      intro x
      by_cases hxL : x ∈ LC
      · simp only [LC, Finset.mem_filter, Finset.mem_univ, true_and] at hxL
        omega
      · have hxLc : x ∈ LCᶜ := Finset.mem_compl.mpr hxL
        have hle_sum : G.degree x.1.1 - 2 ≤ ∑ y ∈ LCᶜ, (G.degree y.1.1 - 2) :=
          Finset.single_le_sum (f := fun y : C₂.supp => G.degree y.1.1 - 2) (fun _ _ => Nat.zero_le _) hxLc
        rw [hsum_zero] at hle_sum
        have := hLC_ge2 x hxLc
        omega
    exact ⟨hall_le2, card_component_eq_radius_of_unique_leaf G hTG hr cG C₂ rfl hcG_xd hall_le2 huniq2⟩
  have hG_other_le2 : ∀ v : V, v ≠ cG → G.degree v ≤ 2 := by
    intro v hvc
    let C := (G.induce {cG}ᶜ).connectedComponentMk ⟨v, hvc⟩
    by_cases h1 : C = C₁
    · exact h_C1_props.1 ⟨⟨v, hvc⟩, h1⟩
    · by_cases h2 : C = C₂
      · exact h_C2_props.1 ⟨⟨v, hvc⟩, h2⟩
      · have hC1 : Fintype.card C.supp = 1 := h_other_card C h1 h2
        have hC_tree : C.toSimpleGraph.IsTree := (hTG.isAcyclic.induce {cG}ᶜ).isTree_connectedComponent C
        have hss : Subsingleton C.supp := Fintype.card_le_one_iff_subsingleton.mp (by omega)
        have hdeg0 : C.toSimpleGraph.degree (⟨⟨v, hvc⟩, rfl⟩ : C.supp) = 0 := by
          rw [← C.toSimpleGraph.card_neighborFinset_eq_degree]
          have hemp : C.toSimpleGraph.neighborFinset (⟨⟨v, hvc⟩, rfl⟩ : C.supp) = ∅ := by
            ext y
            simp only [SimpleGraph.mem_neighborFinset, Finset.notMem_empty, iff_false]
            intro hadj
            exact C.toSimpleGraph.ne_of_adj hadj (Subsingleton.elim _ _)
          rw [hemp, Finset.card_empty]
        rw [component_toSimpleGraph_degree] at hdeg0
        dsimp only at hdeg0
        have := degree_induce_compl_le G (Set.mem_compl_singleton_iff.mpr hvc)
        by_cases hadj : G.Adj v cG
        · have h_eq := degree_induce_compl_singleton_of_adj G hvc hadj
          rw [hdeg0] at h_eq
          omega
        · have h_eq := degree_induce_compl_singleton_of_not_adj G hvc hadj
          rw [hdeg0] at h_eq
          omega
  have hH_c_ge2 : 2 ≤ H.degree cH := deg_center_ge_two H hTH hr hdiamH cH heccH
  by_cases hH_c_ge3 : 3 ≤ H.degree cH
  · have hσc_deg : H.degree (σ cG) = G.degree cG := by
      rw [← ncard_neighborSet_eq_degree, ← hdeg cG, ncard_neighborSet_eq_degree]
    have hσc_ne : σ cG ≠ cH := fun h => by rw [h] at hσc_deg; omega
    let v_bad := σ.symm cH
    have hv_bad_ne : v_bad ≠ cG := by
      intro h
      apply hσc_ne
      rw [← h]
      exact σ.apply_symm_apply cH
    have hv_bad_deg : 3 ≤ G.degree v_bad := by
      rw [← ncard_neighborSet_eq_degree, hdeg v_bad, Equiv.apply_symm_apply, ncard_neighborSet_eq_degree]
      exact hH_c_ge3
    have := hG_other_le2 v_bad hv_bad_ne
    omega
  · have hH_c_eq2 : H.degree cH = 2 := by omega
    have hG_c_eq3 : G.degree cG = 3 := by omega
    have hcc_card : Fintype.card (G.induce {cG}ᶜ).ConnectedComponent = 3 := by
      rw [card_connectedComponent_eq_degree G hTG cG, hG_c_eq3]
    have hcomp_rem : 0 < (Finset.univ \ ({C₁, C₂} : Finset (G.induce {cG}ᶜ).ConnectedComponent)).card := by
      have hsub2 : ({C₁, C₂} : Finset (G.induce {cG}ᶜ).ConnectedComponent).card = 2 := Finset.card_pair hC12
      have hcard_sdiff := Finset.card_sdiff_add_card_inter (Finset.univ : Finset (G.induce {cG}ᶜ).ConnectedComponent) {C₁, C₂}
      have : (Finset.univ ∩ ({C₁, C₂} : Finset (G.induce {cG}ᶜ).ConnectedComponent)).card = 2 := by
        simpa using hsub2
      rw [Finset.card_univ, hcc_card] at hcard_sdiff
      omega
    obtain ⟨C₃, hC3⟩ := Finset.card_pos.mp hcomp_rem
    rw [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at hC3
    have hC31 : C₃ ≠ C₁ := hC3.2.1
    have hC32 : C₃ ≠ C₂ := hC3.2.2
    have huniv3 : (Finset.univ : Finset (G.induce {cG}ᶜ).ConnectedComponent) = {C₁, C₂, C₃} := by
      refine (Finset.eq_of_subset_of_card_le (Finset.subset_univ _) ?_).symm
      have hc3 : ({C₁, C₂, C₃} : Finset (G.induce {cG}ᶜ).ConnectedComponent).card = 3 := by
        rw [Finset.card_insert_of_notMem, Finset.card_pair hC32.symm]
        simp [hC12, hC31.symm]
      rw [hc3, Finset.card_univ, hcc_card]
    have hC3_card : Fintype.card C₃.supp = 1 := h_other_card C₃ hC31 hC32
    have hsum_V : Fintype.card V = 2 * r + 2 := by
      have hs := sum_card_connectedComponent_eq G cG
      have hsum3 : (∑ C : (G.induce {cG}ᶜ).ConnectedComponent, Fintype.card C.supp) =
          Fintype.card C₁.supp + Fintype.card C₂.supp + Fintype.card C₃.supp := by
        have h_eq : (∑ C : (G.induce {cG}ᶜ).ConnectedComponent, Fintype.card C.supp) =
            ∑ C ∈ ({C₁, C₂, C₃} : Finset (G.induce {cG}ᶜ).ConnectedComponent), Fintype.card C.supp := by
          rw [← huniv3]
        rw [h_eq, Finset.sum_insert, Finset.sum_insert, Finset.sum_singleton]
        · omega
        · simp [hC32.symm]
        · simp [hC12, hC31.symm]
      omega
    have hcardW : Fintype.card W = 2 * r + 2 := hcard.symm.trans hsum_V
    have hG_edges : G.edgeFinset.card = 2 * r + 1 := by
      have := hTG.card_edgeFinset
      omega
    obtain ⟨v₀_sub, ⟨hv0_mem, hv0_adj⟩, hv0_uniq⟩ := existsUnique_root_of_component G hTG cG C₃
    let v₀ : V := v₀_sub.1
    have hv0_ne : v₀ ≠ cG := hv0_adj.ne.symm
    have hv0_deg1 : G.degree v₀ = 1 := by
      have hss : Subsingleton C₃.supp := Fintype.card_le_one_iff_subsingleton.mp (by omega)
      have hdeg0 : C₃.toSimpleGraph.degree (⟨v₀_sub, hv0_mem⟩ : C₃.supp) = 0 := by
        rw [← C₃.toSimpleGraph.card_neighborFinset_eq_degree]
        have hemp : C₃.toSimpleGraph.neighborFinset (⟨v₀_sub, hv0_mem⟩ : C₃.supp) = ∅ := by
          ext y
          simp only [SimpleGraph.mem_neighborFinset, Finset.notMem_empty, iff_false]
          intro hadj
          exact C₃.toSimpleGraph.ne_of_adj hadj (Subsingleton.elim _ _)
        rw [hemp, Finset.card_empty]
      rw [component_toSimpleGraph_degree] at hdeg0
      dsimp only at hdeg0
      have h_eq := degree_induce_compl_singleton_of_adj G v₀_sub.2 hv0_adj.symm
      rw [Subtype.coe_eta] at h_eq
      dsimp only [v₀]
      omega
    -- Now analyze H on 2 * r + 2 vertices
    have : Nonempty W := hTH.connected.nonempty
    obtain ⟨y0, yd, hyd⟩ := H.exists_dist_eq_diam
    obtain ⟨pH, hpH, hpH_len⟩ := hTH.connected.exists_path_of_dist y0 yd
    have hpH_len_r : pH.length = 2 * r := hpH_len.trans (hyd.trans hdiamH)
    obtain ⟨hcH_mem, hcH_y0, hcH_yd⟩ := diam_path_contains_center H hTH cH heccH pH hpH hpH_len_r
    have hpH_card : pH.support.toFinset.card = 2 * r + 1 := by
      rw [List.toFinset_card_of_nodup hpH.support_nodup, pH.length_support, hpH_len_r]
    have hcomp_card : pH.support.toFinsetᶜ.card = 1 := by
      rw [Finset.card_compl, hpH_card, hcardW]
      omega
    obtain ⟨w₀, hw₀_eq⟩ := Finset.card_eq_one.mp hcomp_card
    have hw₀_not : w₀ ∉ pH.support := by
      have : w₀ ∈ pH.support.toFinsetᶜ := by rw [hw₀_eq]; exact Finset.mem_singleton_self w₀
      simpa using this
    have hall_mem_pH : ∀ w : W, w ≠ w₀ → w ∈ pH.support := by
      intro w hne
      by_contra hnot
      have hw_mem : w ∈ pH.support.toFinsetᶜ := by simpa using hnot
      rw [hw₀_eq, Finset.mem_singleton] at hw_mem
      exact hne hw_mem
    have hw0_pos : 1 ≤ H.degree w₀ := by
      have : Nontrivial W := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
      exact hTH.preconnected.degree_pos_of_nontrivial w₀
    have hw0_deg1 : H.degree w₀ = 1 := by
      by_contra hne1
      have hge2 : 1 < (H.neighborFinset w₀).card := by
        rw [H.card_neighborFinset_eq_degree]
        omega
      obtain ⟨z₁, hz1, z₂, hz2, hz12⟩ := Finset.one_lt_card.mp hge2
      rw [SimpleGraph.mem_neighborFinset] at hz1 hz2
      have hz1_mem : z₁ ∈ pH.support := hall_mem_pH z₁ hz1.ne.symm
      have hz2_mem : z₂ ∈ pH.support := hall_mem_pH z₂ hz2.ne.symm
      obtain ⟨q, hq, hq_sub⟩ := path_in_walk_support H pH hpH hz1_mem hz2_mem
      have hw0_not_q : w₀ ∉ q.support := fun hm => hw₀_not (hq_sub w₀ hm)
      let q2 : H.Walk z₁ z₂ := Walk.cons hz1.symm (Walk.cons hz2 Walk.nil)
      have hq2 : q2.IsPath := by
        simp [q2, Walk.cons_isPath_iff, hz12, hz1.ne.symm, hz2.ne]
      have hq_eq : q = q2 := isTree_path_eq H hTH hq hq2
      have hw0_in : w₀ ∈ q2.support := by simp [q2]
      rw [← hq_eq] at hw0_in
      exact hw0_not_q hw0_in
    obtain ⟨z, hz_adj, hz_uniq⟩ := SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp hw0_deg1
    have hz_mem : z ∈ pH.support := hall_mem_pH z hz_adj.ne.symm
    have hpH_finset_eq : pH.support.toFinset = Finset.univ.erase w₀ := by
      ext w
      simp only [List.mem_toFinset, Finset.mem_erase, Finset.mem_univ, and_true]
      exact ⟨fun hm hweq => hw₀_not (hweq ▸ hm), hall_mem_pH w⟩
    have h_ind_w0 : Nonempty (H.induce {w₀}ᶜ ≃g pathG (2 * r + 1)) := by
      have h1 := induce_support_iso_pathG H hTH pH hpH
      rw [hpH_len_r, hpH_finset_eq] at h1
      have hset : (({w₀}ᶜ : Set W)) = ((Finset.univ.erase w₀ : Finset W) : Set W) := by
        ext w; simp
      rw [hset]
      exact h1
    obtain ⟨φ₀⟩ := h_ind_w0
    have hH_le2_ne_z : ∀ w : W, w ≠ z → H.degree w ≤ 2 := by
      intro w hwz
      by_cases hww0 : w = w₀
      · subst hww0; omega
      · have hww0' : w ∈ ({w₀}ᶜ : Set W) := Set.mem_compl_singleton_iff.mpr hww0
        have hnadj : ¬ H.Adj w w₀ := fun hadj => hwz (hz_uniq w hadj.symm)
        rw [← degree_induce_compl_singleton_of_not_adj H hww0' hnadj, ← φ₀.degree_eq ⟨w, hww0'⟩]
        exact degree_pathG_le_two (2 * r + 1) (φ₀ ⟨w, hww0'⟩)
    have hσc_deg : H.degree (σ cG) = 3 := by
      rw [← ncard_neighborSet_eq_degree, ← hdeg cG, ncard_neighborSet_eq_degree, hG_c_eq3]
    have hz_eq_σc : z = σ cG := by
      by_contra hne
      have := hH_le2_ne_z (σ cG) (Ne.symm hne)
      omega
    have hz_deg3 : H.degree z = 3 := hz_eq_σc ▸ hσc_deg
    have hz_ne_cH : z ≠ cH := fun h => by rw [h, hH_c_eq2] at hz_deg3; omega
    have hy0_deg1 : H.degree y0 = 1 := by
      have hy0_ne_w0 : y0 ≠ w₀ := fun h => hw₀_not (h ▸ pH.start_mem_support)
      have hpH_nn : ¬ pH.Nil := Walk.not_nil_of_ne (fun h => by rw [← h, SimpleGraph.dist_self] at hyd; omega)
      have hall_y0 : ∀ a : W, H.Adj y0 a → a = w₀ ∨ a = pH.snd := by
        intro a hadj
        by_cases haw0 : a = w₀
        · exact Or.inl haw0
        · exact Or.inr (hTH.isAcyclic.eq_snd_of_adj_start hpH hadj (hall_mem_pH a haw0))
      have hne_y0_z : y0 ≠ z := by
        intro heq
        have hsub_y0 : H.neighborFinset y0 ⊆ {w₀, pH.snd} := by
          intro a ha
          rw [SimpleGraph.mem_neighborFinset] at ha
          simp only [Finset.mem_insert, Finset.mem_singleton]
          exact hall_y0 a ha
        have hle2 : H.degree y0 ≤ 2 := by
          rw [← H.card_neighborFinset_eq_degree]
          exact (Finset.card_le_card hsub_y0).trans ((Finset.card_insert_le _ _).trans (by simp))
        rw [heq, hz_deg3] at hle2
        omega
      have hsub_y0 : H.neighborFinset y0 ⊆ {pH.snd} := by
        intro a ha
        rw [SimpleGraph.mem_neighborFinset] at ha
        rw [Finset.mem_singleton]
        rcases hall_y0 a ha with rfl | h
        · exact False.elim (hne_y0_z (hz_uniq y0 ha.symm))
        · exact h
      have hpos : 1 ≤ H.degree y0 := by
        have : Nontrivial W := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
        exact hTH.preconnected.degree_pos_of_nontrivial y0
      have hle1 : H.degree y0 ≤ 1 := by
        rw [← H.card_neighborFinset_eq_degree]
        exact (Finset.card_le_card hsub_y0).trans (by simp)
      omega
    have hyd_deg1 : H.degree yd = 1 := by
      have hyd_ne_w0 : yd ≠ w₀ := fun h => hw₀_not (h ▸ pH.end_mem_support)
      have hpH_nn : ¬ pH.Nil := Walk.not_nil_of_ne (fun h => by rw [← h, SimpleGraph.dist_self] at hyd; omega)
      have hall_yd : ∀ a : W, H.Adj yd a → a = w₀ ∨ a = pH.penultimate := by
        intro a hadj
        by_cases haw0 : a = w₀
        · exact Or.inl haw0
        · exact Or.inr (hTH.isAcyclic.eq_penultimate_of_adj_end hpH hadj (hall_mem_pH a haw0))
      have hne_yd_z : yd ≠ z := by
        intro heq
        have hsub_yd : H.neighborFinset yd ⊆ {w₀, pH.penultimate} := by
          intro a ha
          rw [SimpleGraph.mem_neighborFinset] at ha
          simp only [Finset.mem_insert, Finset.mem_singleton]
          exact hall_yd a ha
        have hle2 : H.degree yd ≤ 2 := by
          rw [← H.card_neighborFinset_eq_degree]
          exact (Finset.card_le_card hsub_yd).trans ((Finset.card_insert_le _ _).trans (by simp))
        rw [heq, hz_deg3] at hle2
        omega
      have hsub_yd : H.neighborFinset yd ⊆ {pH.penultimate} := by
        intro a ha
        rw [SimpleGraph.mem_neighborFinset] at ha
        rw [Finset.mem_singleton]
        rcases hall_yd a ha with rfl | h
        · exact False.elim (hne_yd_z (hz_uniq yd ha.symm))
        · exact h
      have hpos : 1 ≤ H.degree yd := by
        have : Nontrivial W := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
        exact hTH.preconnected.degree_pos_of_nontrivial yd
      have hle1 : H.degree yd ≤ 1 := by
        rw [← H.card_neighborFinset_eq_degree]
        exact (Finset.card_le_card hsub_yd).trans (by simp)
      omega
    by_cases hadj_end : H.Adj z y0 ∨ H.Adj z yd
    · -- Subcase A: H has >= 2 induced copies of pathG (2 * r + 1), G has <= 1
      have h_two_copies : ∃ y_alt : W, y_alt ≠ w₀ ∧
          Nonempty (H.induce ({y_alt}ᶜ : Set W) ≃g pathG (2 * r + 1)) := by
        rcases hadj_end with hadj_z_y0 | hadj_z_yd
        · have hsnd_eq : z = pH.snd :=
            hTH.isAcyclic.eq_snd_of_adj_start hpH hadj_z_y0.symm hz_mem
          have hpH_nn : ¬ pH.Nil := Walk.not_nil_of_ne (fun h => by rw [← h, SimpleGraph.dist_self] at hyd; omega)
          let q : H.Walk w₀ yd := Walk.cons (hsnd_eq ▸ hz_adj) pH.tail
          have hq_path : q.IsPath := by
            rw [Walk.cons_isPath_iff]
            refine ⟨hpH.tail, fun hm => ?_⟩
            rw [Walk.support_tail_of_not_nil pH hpH_nn] at hm
            exact hw₀_not (List.mem_of_mem_tail hm)
          have hq_len : q.length = 2 * r := by
            rw [Walk.length_cons, Walk.length_tail, hpH_len_r]
            omega
          have hy0_not_q : y0 ∉ q.support := by
            rw [Walk.support_cons, List.mem_cons, Walk.support_tail_of_not_nil pH hpH_nn]
            rintro (rfl | hm)
            · exact hw₀_not pH.start_mem_support
            · exact start_notMem_tail_support_of_isPath hpH hm
          have hq_finset : q.support.toFinset = Finset.univ.erase y0 := by
            apply Finset.eq_of_subset_of_card_le
            · intro w hw
              rw [List.mem_toFinset] at hw
              exact Finset.mem_erase.mpr ⟨fun heq => hy0_not_q (heq ▸ hw), Finset.mem_univ _⟩
            · rw [List.toFinset_card_of_nodup hq_path.support_nodup, q.length_support, hq_len,
                Finset.card_erase_of_mem (Finset.mem_univ y0), Finset.card_univ, hcardW]
              omega
          have h1 := induce_support_iso_pathG H hTH q hq_path
          rw [hq_len, hq_finset] at h1
          have hset : (({y0}ᶜ : Set W)) = ((Finset.univ.erase y0 : Finset W) : Set W) := by
            ext w; simp
          rw [← hset] at h1
          exact ⟨y0, fun h => hw₀_not (h ▸ pH.start_mem_support), h1⟩
        · have hrev := hpH.reverse
          have hsnd_eq : z = pH.reverse.snd :=
            hTH.isAcyclic.eq_snd_of_adj_start hrev hadj_z_yd.symm (by simpa using hz_mem)
          have hrev_nn : ¬ pH.reverse.Nil := Walk.not_nil_of_ne (fun h => by rw [h, SimpleGraph.dist_self] at hyd; omega)
          let q : H.Walk w₀ y0 := Walk.cons (hsnd_eq ▸ hz_adj) pH.reverse.tail
          have hq_path : q.IsPath := by
            rw [Walk.cons_isPath_iff]
            refine ⟨hrev.tail, fun hm => ?_⟩
            rw [Walk.support_tail_of_not_nil pH.reverse hrev_nn, Walk.support_reverse] at hm
            exact hw₀_not (List.mem_reverse.mp (List.mem_of_mem_tail hm))
          have hq_len : q.length = 2 * r := by
            rw [Walk.length_cons, Walk.length_tail, Walk.length_reverse, hpH_len_r]
            omega
          have hyd_not_q : yd ∉ q.support := by
            rw [Walk.support_cons, List.mem_cons, Walk.support_tail_of_not_nil pH.reverse hrev_nn]
            rintro (rfl | hm)
            · exact hw₀_not pH.end_mem_support
            · exact start_notMem_tail_support_of_isPath hrev hm
          have hq_finset : q.support.toFinset = Finset.univ.erase yd := by
            apply Finset.eq_of_subset_of_card_le
            · intro w hw
              rw [List.mem_toFinset] at hw
              exact Finset.mem_erase.mpr ⟨fun heq => hyd_not_q (heq ▸ hw), Finset.mem_univ _⟩
            · rw [List.toFinset_card_of_nodup hq_path.support_nodup, q.length_support, hq_len,
                Finset.card_erase_of_mem (Finset.mem_univ yd), Finset.card_univ, hcardW]
              omega
          have h1 := induce_support_iso_pathG H hTH q hq_path
          rw [hq_len, hq_finset] at h1
          have hset : (({yd}ᶜ : Set W)) = ((Finset.univ.erase yd : Finset W) : Set W) := by
            ext w; simp
          rw [← hset] at h1
          exact ⟨yd, fun h => hw₀_not (h ▸ pH.end_mem_support), h1⟩
      obtain ⟨y_alt, hy_alt_ne, hy_alt_iso⟩ := h_two_copies
      let Af : Finset (Finset V) :=
        Finset.univ.filter fun S : Finset V => Nonempty (G.induce (S : Set V) ≃g pathG (2 * r + 1))
      let Bf : Finset (Finset W) :=
        Finset.univ.filter fun T : Finset W => Nonempty (H.induce (T : Set W) ≃g pathG (2 * r + 1))
      have hB_ge2 : 2 ≤ Bf.card := by
        let Tw0 : Finset W := Finset.univ.erase w₀
        let Talt : Finset W := Finset.univ.erase y_alt
        have hneT : Tw0 ≠ Talt := by
          intro h
          have h1 : w₀ ∈ Talt := by simp [Talt, hy_alt_ne.symm]
          rw [← h] at h1
          simp [Tw0] at h1
        have hm1 : Tw0 ∈ Bf := by
          rw [Finset.mem_filter]
          refine ⟨Finset.mem_univ _, ?_⟩
          have hset : (({w₀}ᶜ : Set W)) = (Tw0 : Set W) := by ext w; simp [Tw0]
          rw [← hset]
          exact ⟨φ₀⟩
        have hm2 : Talt ∈ Bf := by
          rw [Finset.mem_filter]
          refine ⟨Finset.mem_univ _, ?_⟩
          have hset : (({y_alt}ᶜ : Set W)) = (Talt : Set W) := by ext w; simp [Talt]
          rw [← hset]
          exact hy_alt_iso
        calc
          2 = ({Tw0, Talt} : Finset (Finset W)).card := (Finset.card_pair hneT).symm
          _ ≤ Bf.card := Finset.card_le_card (Finset.insert_subset_iff.mpr ⟨hm1, Finset.singleton_subset_iff.mpr hm2⟩)
      have hA_le1 : Af.card ≤ 1 := by
        have hsubA : Af ⊆ {Finset.univ.erase v₀} := by
          intro S hS
          simp only [Af, Finset.mem_filter, Finset.mem_univ, true_and] at hS
          obtain ⟨ψ⟩ := hS
          have hScard : S.card = 2 * r + 1 := by
            rw [← Fintype.card_coe]
            exact (Fintype.card_congr ψ.toEquiv).trans (Fintype.card_fin (2 * r + 1))
          have hSc_card : Sᶜ.card = 1 := by
            rw [Finset.card_compl, hScard, hsum_V]
            omega
          obtain ⟨u, hu_eq⟩ := Finset.card_eq_one.mp hSc_card
          have hS_eq : S = Finset.univ.erase u := by
            ext x
            simp only [Finset.mem_erase, Finset.mem_univ, and_true]
            have hx : x ∉ Sᶜ ↔ x ∉ ({u} : Finset V) := by rw [hu_eq]
            simpa using hx
          have hset : (S : Set V) = ({u}ᶜ : Set V) := by
            rw [hS_eq]; ext x; simp
          rw [hset] at ψ
          have hE_eq : (G.induce {u}ᶜ).edgeFinset.card = 2 * r := by
            rw [Iso.card_edgeFinset_eq ψ]
            have := card_edgeFinset_pathG (2 * r + 1) (by omega)
            omega
          have hG_deg_u : G.degree u = 1 := by
            have h1 : (G.induce {u}ᶜ).edgeFinset.card + G.degree u = G.edgeFinset.card := by
              rw [G.card_edgeFinset_induce_compl_singleton u, G.card_edgeFinset_deleteIncidenceSet u]
              have := G.degree_le_card_edgeFinset u
              omega
            omega
          have huc : u ∈ ({cG}ᶜ : Set V) := Set.mem_compl_singleton_iff.mpr (fun h => by rw [h, hG_c_eq3] at hG_deg_u; omega)
          have hcGu : cG ∈ ({u}ᶜ : Set V) := Set.mem_compl_singleton_iff.mpr (Ne.symm huc)
          have hdeg_ind_cG : (G.induce {u}ᶜ).degree ⟨cG, hcGu⟩ ≤ 2 := by
            rw [← ψ.degree_eq ⟨cG, hcGu⟩]
            exact degree_pathG_le_two (2 * r + 1) (ψ ⟨cG, hcGu⟩)
          have hadj_cG_u : G.Adj cG u := by
            by_contra hnadj
            rw [degree_induce_compl_singleton_of_not_adj G hcGu hnadj, hG_c_eq3] at hdeg_ind_cG
            omega
          have hu_v0 : u = v₀ := by
            let u' : ({cG}ᶜ : Set V) := ⟨u, huc⟩
            let Cu := (G.induce {cG}ᶜ).connectedComponentMk u'
            by_cases h1 : Cu = C₁
            · exfalso
              obtain ⟨u1, ⟨hu1_mem, hu1_adj⟩, hu1_uniq⟩ := existsUnique_root_of_component G hTG cG C₁
              have hu_eq_u1 : u' = u1 :=
                (hu1_uniq u' ⟨h1, hadj_cG_u⟩).trans (hu1_uniq u1 ⟨hu1_mem, hu1_adj⟩).symm
              have hC1_nt : Nontrivial C₁.supp := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
              have hdu1 : 1 ≤ C₁.toSimpleGraph.degree (⟨u1, hu1_mem⟩ : C₁.supp) :=
                (hTG.isAcyclic.induce {cG}ᶜ).isTree_connectedComponent C₁ |>.preconnected.degree_pos_of_nontrivial _
              rw [component_toSimpleGraph_degree] at hdu1
              change 1 ≤ (G.induce {cG}ᶜ).degree u1 at hdu1
              rw [← hu_eq_u1] at hdu1
              have h_eq := degree_induce_compl_singleton_of_adj G u'.2 hadj_cG_u.symm
              rw [Subtype.coe_eta] at h_eq
              dsimp only [u'] at hdu1 h_eq
              omega
            · by_cases h2 : Cu = C₂
              · exfalso
                obtain ⟨u2, ⟨hu2_mem, hu2_adj⟩, hu2_uniq⟩ := existsUnique_root_of_component G hTG cG C₂
                have hu_eq_u2 : u' = u2 :=
                  (hu2_uniq u' ⟨h2, hadj_cG_u⟩).trans (hu2_uniq u2 ⟨hu2_mem, hu2_adj⟩).symm
                have hC2_nt : Nontrivial C₂.supp := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
                have hdu2 : 1 ≤ C₂.toSimpleGraph.degree (⟨u2, hu2_mem⟩ : C₂.supp) :=
                  (hTG.isAcyclic.induce {cG}ᶜ).isTree_connectedComponent C₂ |>.preconnected.degree_pos_of_nontrivial _
                rw [component_toSimpleGraph_degree] at hdu2
                change 1 ≤ (G.induce {cG}ᶜ).degree u2 at hdu2
                rw [← hu_eq_u2] at hdu2
                have h_eq := degree_induce_compl_singleton_of_adj G u'.2 hadj_cG_u.symm
                rw [Subtype.coe_eta] at h_eq
                dsimp only [u'] at hdu2 h_eq
                omega
              · have hCu_mem : Cu ∈ ({C₁, C₂, C₃} : Finset _) := by rw [← huniv3]; exact Finset.mem_univ _
                simp only [Finset.mem_insert, Finset.mem_singleton] at hCu_mem
                have hCu3 : Cu = C₃ := by tauto
                have hu_in_C3 : u' ∈ C₃.supp := hCu3
                exact congrArg Subtype.val (hv0_uniq u' ⟨hu_in_C3, hadj_cG_u⟩)
          rw [Finset.mem_singleton, hS_eq, hu_v0]
        exact (Finset.card_le_card hsubA).trans (by simp)
      have hAB : Af.card = Bf.card := by
        have hA_eq : {S : Finset V | Nonempty (G.induce (S : Set V) ≃g pathG (2 * r + 1))} = (Af : Set (Finset V)) := by
          ext S; simp [Af]
        have hB_eq : {T : Finset W | Nonempty (H.induce (T : Set W) ≃g pathG (2 * r + 1))} = (Bf : Set (Finset W)) := by
          ext T; simp [Bf]
        rw [← Set.ncard_coe_finset Af, ← Set.ncard_coe_finset Bf, ← hA_eq, ← hB_eq]
        exact hsub (Fin (2 * r + 1)) (pathG (2 * r + 1)) (by simp [hsum_V])
      omega
    · -- Subcase B: ¬ H.Adj z y0 ∧ ¬ H.Adj z yd
      push Not at hadj_end
      rcases hadj_end with ⟨hnadj_y0, hnadj_yd⟩
      let pH1 : H.Walk y0 (pH.getVert r) := pH.take r
      let pH2 : H.Walk (pH.getVert r) yd := pH.drop r
      have hpH1 : pH1.IsPath := hpH.take r
      have hpH2 : pH2.IsPath := hpH.drop r
      have hpH1_len : pH1.length = r := by rw [Walk.take_length]; omega
      have hpH2_len : pH2.length = r := by rw [Walk.drop_length]; omega
      have hcH_get : cH = pH.getVert r := by
        obtain ⟨q1, q2, hq1, hq2, hpH_eq⟩ := hpH.mem_support_iff_exists_append.mp hcH_mem
        have hq1_dist : q1.length = H.dist y0 cH := isTree_dist_eq_length_of_isPath H hTH q1 hq1
        have hq1_len : q1.length = r := by rw [hq1_dist, SimpleGraph.dist_comm, hcH_y0]
        have hget : pH.getVert q1.length = cH := by
          rw [hpH_eq, Walk.getVert_append]
          simp
        rw [hq1_len] at hget
        exact hget.symm
      have hpH_app : pH1.append pH2 = pH := pH.append_take_drop_eq r
      have hz12 : z ∈ pH1.support ∨ z ∈ pH2.support :=
        (Walk.mem_support_append_iff pH1 pH2).mp (hpH_app.symm ▸ hz_mem)
      have hcontra_leaf : ∀ (y_del y_opp : W) (hy_deg1 : H.degree y_del = 1)
          (hy_nadj : ¬ H.Adj z y_del) (hy_ne : z ∈ ({y_del}ᶜ : Set W)) (hy_opp_ne : y_opp ∈ ({y_del}ᶜ : Set W))
          (q : H.Walk z y_opp), q.IsPath → r + 1 ≤ q.length → y_del ∉ q.support → False := by
        intro y_del y_opp hy_deg1 hy_nadj hy_ne hy_opp_ne q hq hq_len hy_not
        have hHy_tree : (H.induce {y_del}ᶜ).IsTree := induce_compl_singleton_isTree_of_deg_one H hTH hy_deg1
        have hdeg_z_ind : (H.induce {y_del}ᶜ).degree ⟨z, hy_ne⟩ = 3 := by
          rw [degree_induce_compl_singleton_of_not_adj H hy_ne hy_nadj, hz_deg3]
        have hq_supp : ∀ w ∈ q.support, w ∈ ({y_del}ᶜ : Set W) := fun w hw =>
          Set.mem_compl_singleton_iff.mpr fun h => hy_not (h ▸ hw)
        let q' := q.induce ({y_del}ᶜ : Set W) hq_supp
        have hq' : q'.IsPath := by
          refine Walk.IsPath.of_map (f := (SimpleGraph.Embedding.induce ({y_del}ᶜ : Set W)).toHom) ?_
          rw [Walk.map_induce]
          exact hq
        have hdist_z : (H.induce {y_del}ᶜ).dist ⟨z, hy_ne⟩ ⟨y_opp, hy_opp_ne⟩ = q.length := by
          have h1 := isTree_dist_eq_length_of_isPath (H.induce {y_del}ᶜ) hHy_tree q' hq'
          rw [← h1, length_walk_induce]
        have hecc_z_gt : (r : ℕ∞) < (H.induce {y_del}ᶜ).eccent ⟨z, hy_ne⟩ := by
          have hlt : (r : ℕ∞) < ((H.induce {y_del}ᶜ).dist ⟨z, hy_ne⟩ ⟨y_opp, hy_opp_ne⟩ : ℕ∞) :=
            Nat.cast_lt.mpr (by omega)
          rw [(hHy_tree.connected _ _).coe_dist_eq_edist] at hlt
          exact lt_of_lt_of_le hlt SimpleGraph.edist_le_eccent
        let u := σ.symm y_del
        have hσu : σ u = y_del := σ.apply_symm_apply y_del
        have hu_deg1 : G.degree u = 1 := by
          rw [← ncard_neighborSet_eq_degree, hdeg u, hσu, ncard_neighborSet_eq_degree, hy_deg1]
        obtain ⟨φ⟩ := hσ u
        rw [hσu] at φ
        let c' : ({u}ᶜ : Set V) := φ.symm ⟨z, hy_ne⟩
        have hdeg_c' : (G.induce {u}ᶜ).degree c' = 3 := by
          dsimp [c']
          rw [φ.symm.degree_eq ⟨z, hy_ne⟩]
          exact hdeg_z_ind
        have hG_deg_c' : 3 ≤ G.degree c'.1 := hdeg_c'.symm.le.trans (degree_induce_compl_le G c'.2)
        have hc'_eq : c'.1 = cG := by
          by_contra hne
          have := hG_other_le2 c'.1 hne
          omega
        have hecc_c'_gt : (r : ℕ∞) < (G.induce {u}ᶜ).eccent c' := by
          dsimp [c']
          rw [iso_eccent_eq _ _ φ.symm ⟨z, hy_ne⟩]
          exact hecc_z_gt
        have hGu_tree : (G.induce {u}ᶜ).IsTree := induce_compl_singleton_isTree_of_deg_one G hTG hu_deg1
        have hecc_c'_le : (G.induce {u}ᶜ).eccent c' ≤ r := by
          rw [SimpleGraph.eccent_le_iff]
          intro x'
          rw [← (hGu_tree.connected c' x').coe_dist_eq_edist,
            induce_compl_singleton_dist_eq G hTG hGu_tree, hc'_eq]
          rw [(hTG.connected cG x'.1).coe_dist_eq_edist, ← heccG]
          exact SimpleGraph.edist_le_eccent
        exact absurd (lt_of_lt_of_le hecc_c'_gt hecc_c'_le) (lt_irrefl _)
      rcases hz12 with hz1 | hz2
      · obtain ⟨a, b, ha, hb, hpH1_eq⟩ := hpH1.mem_support_iff_exists_append.mp hz1
        let q : H.Walk z yd := b.append pH2
        have hpH_decomp : pH = a.append q := by
          rw [← hpH_app, hpH1_eq, Walk.append_assoc]
        have hq : q.IsPath := (hpH_decomp ▸ hpH).of_append_right
        have hb_nn : ¬ b.Nil := Walk.not_nil_of_ne (fun h => hz_ne_cH (h.trans hcH_get.symm))
        have hq_len : r + 1 ≤ q.length := by
          rw [Walk.length_append, hpH2_len]
          have : 1 ≤ b.length := Walk.not_nil_iff_lt_length.mp hb_nn
          omega
        have hz_ne_y0 : z ≠ y0 := fun h => by
          rw [h, hy0_deg1] at hz_deg3
          omega
        have ha_nn : ¬ a.Nil := Walk.not_nil_of_ne hz_ne_y0.symm
        have hy0_not : y0 ∉ q.support := by
          intro hm
          have hq_nn : ¬ q.Nil := Walk.not_nil_iff_lt_length.mpr ((Nat.zero_lt_succ r).trans_le hq_len)
          have hdisj : a.support.Disjoint q.tail.support := by
            have h1 := (hpH_decomp ▸ hpH).support_nodup
            rw [Walk.support_append, List.nodup_append', ← Walk.support_tail_of_not_nil q hq_nn] at h1
            exact h1.2.2
          have hy0_a : y0 ∈ a.support := a.start_mem_support
          have hy0_qtail : y0 ∈ q.tail.support := by
            rw [Walk.support_tail_of_not_nil q hq_nn]
            exact mem_support_tail_of_ne q hm hz_ne_y0.symm
          exact hdisj hy0_a hy0_qtail
        exact hcontra_leaf y0 yd hy0_deg1 hnadj_y0 hz_ne_y0 (fun h => by rw [h, SimpleGraph.dist_self] at hyd; omega)
          q hq hq_len hy0_not
      · obtain ⟨a, b, ha, hb, hpH2_eq⟩ := hpH2.mem_support_iff_exists_append.mp hz2
        let q : H.Walk z y0 := a.reverse.append pH1.reverse
        have hpH_rev : pH.reverse = b.reverse.append q := by
          rw [← hpH_app, hpH2_eq, Walk.reverse_append, Walk.reverse_append, Walk.append_assoc]
        have hq : q.IsPath := (hpH_rev ▸ hpH.reverse).of_append_right
        have ha_nn : ¬ a.Nil := Walk.not_nil_of_ne (fun h => hz_ne_cH (hcH_get.trans h).symm)
        have hq_len : r + 1 ≤ q.length := by
          rw [Walk.length_append, Walk.length_reverse, Walk.length_reverse, hpH1_len]
          have : 1 ≤ a.length := Walk.not_nil_iff_lt_length.mp ha_nn
          omega
        have hz_ne_yd : z ≠ yd := fun h => by
          rw [h, hyd_deg1] at hz_deg3
          omega
        have hyd_not : yd ∉ q.support := by
          intro hm
          have hq_nn : ¬ q.Nil := Walk.not_nil_iff_lt_length.mpr ((Nat.zero_lt_succ r).trans_le hq_len)
          have hdisj : b.reverse.support.Disjoint q.tail.support := by
            have h1 := (hpH_rev ▸ hpH.reverse).support_nodup
            rw [Walk.support_append, List.nodup_append', ← Walk.support_tail_of_not_nil q hq_nn] at h1
            exact h1.2.2
          have hyd_b : yd ∈ b.reverse.support := by
            rw [Walk.support_reverse, List.mem_reverse]
            exact Walk.end_mem_support _
          have hyd_qtail : yd ∈ q.tail.support := by
            rw [Walk.support_tail_of_not_nil q hq_nn]
            exact mem_support_tail_of_ne q hm hz_ne_yd.symm
          exact hdisj hyd_b hyd_qtail
        exact hcontra_leaf yd y0 hyd_deg1 hnadj_yd hz_ne_yd (fun h => by rw [h, SimpleGraph.dist_self] at hyd; omega)
          q hq hq_len hyd_not

private lemma tree_R1_H3_R1_H2 :
    OMA.R_ReconstructionConjecture_reconstruction_conjecture_variants_tree_R1_H3_R1.H2 := by
  intro V W _ _ hV G H σ hTG hTH hσ hdeg hnonpath r cG cH hr hdiamG hdiamH heccG heccH huG huH hsub
  have hcard : Fintype.card V = Fintype.card W := Fintype.card_congr σ
  have hW : 3 ≤ Fintype.card W := hcard ▸ hV
  have hσ_rev : ∀ w : W, Nonempty (H.induce {w}ᶜ ≃g G.induce {σ.symm w}ᶜ) := by
    intro w
    obtain ⟨φ⟩ := hσ (σ.symm w)
    rw [σ.apply_symm_apply w] at φ
    exact ⟨φ.symm⟩
  have hdeg_rev : ∀ w : W, (H.neighborSet w).ncard = (G.neighborSet (σ.symm w)).ncard := by
    intro w
    have h := hdeg (σ.symm w)
    rw [σ.apply_symm_apply w] at h
    exact h.symm
  have hnonpath_rev : ∃ w : W, 3 ≤ (H.neighborSet w).ncard := by
    obtain ⟨v₀, hv₀⟩ := hnonpath
    exact ⟨σ v₀, by rw [← hdeg v₀]; exact hv₀⟩
  have hsub_rev : ∀ (U : Type) [Fintype U] (Q : SimpleGraph U),
      Fintype.card U < Fintype.card W →
      {T : Finset W | Nonempty (H.induce (T : Set W) ≃g Q)}.ncard =
        {S : Finset V | Nonempty (G.induce (S : Set V) ≃g Q)}.ncard :=
    fun U _ Q hU => (hsub U Q (hcard ▸ hU)).symm
  by_cases hdegc : G.degree cG = H.degree cH
  · by_cases hleafG : ∃ v : V, G.Adj cG v ∧ (G.neighborSet v).ncard < 2
    · obtain ⟨v, hadj, hv_lt⟩ := hleafG
      have : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
      have hv_pos : 1 ≤ G.degree v := hTG.preconnected.degree_pos_of_nontrivial v
      rw [ncard_neighborSet_eq_degree] at hv_lt
      have hv1 : G.degree v = 1 := by omega
      exact Or.inl (iso_of_deg_center_eq_and_leaf_adj G H σ hTG hTH hdeg hr hdiamG
        cG cH heccG huG heccH huH hdegc hadj hv1 (hσ v))
    · by_cases hleafH : ∃ w : W, H.Adj cH w ∧ (H.neighborSet w).ncard < 2
      · obtain ⟨w, hadj, hw_lt⟩ := hleafH
        have : Nontrivial W := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
        have hw_pos : 1 ≤ H.degree w := hTH.preconnected.degree_pos_of_nontrivial w
        rw [ncard_neighborSet_eq_degree] at hw_lt
        have hw1 : H.degree w = 1 := by omega
        obtain ⟨ψ⟩ := iso_of_deg_center_eq_and_leaf_adj H G σ.symm hTH hTG hdeg_rev hr hdiamH
          cH cG heccH huH heccG huG hdegc.symm hadj hw1 (hσ_rev w)
        exact Or.inl ⟨ψ.symm⟩
      · push Not at hleafG hleafH
        refine Or.inr ⟨?_, hleafG, hleafH⟩
        rw [ncard_neighborSet_eq_degree, ncard_neighborSet_eq_degree, hdegc]
  · exfalso
    rcases Nat.lt_or_gt_of_ne hdegc with hlt | hgt
    · exact contradict_of_deg_center_lt hW H G σ.symm hTH hTG hσ_rev hdeg_rev hnonpath_rev
        hr hdiamH hdiamG cH cG heccH heccG huH huG hsub_rev hlt
    · exact contradict_of_deg_center_lt hV G H σ hTG hTH hσ hdeg hnonpath
        hr hdiamG hdiamH cG cH heccG heccH huG huH hsub hgt

end TreeR1H3R1H2

theorem result : OMA.R_ReconstructionConjecture_reconstruction_conjecture_variants_tree_R1_H3_R1.H2 := by
  exact tree_R1_H3_R1_H2

end KellyStep4

namespace KellyStep5

/-
# Small center components in the reconstruction of a tree

A diameter path supplies two pendant arms of full radius. After deleting a
leaf, the center is the unique vertex of degree at least three within the
radius bound of every remaining vertex. Comparing the two outer levels in
the leaf cards identifies corresponding arm tips. Their shortened arms can
be exchanged by a card automorphism before the deleted tips are restored.

Credit: @Deldor14. The tree deletion and distance lemmas are adapted from
@green-notes' proof of the preceding step.
-/
end KellyStep5
namespace OMA
namespace TreeArms
open SimpleGraph
open Classical
variable {V : Type*} {G : SimpleGraph V} {c : V} {n : Nat}

structure Arm (G : SimpleGraph V) (c : V) (n : Nat) where
  vertex : Fin n ↪ V
  away : ∀ i, vertex i ≠ c
  internal : ∀ i j, G.Adj (vertex i) (vertex j) ↔ i.val+1=j.val ∨ j.val+1=i.val
  external : ∀ i x, x ∉ Set.range vertex →
    (G.Adj (vertex i) x ↔ i.val=0 ∧ x=c)

-- Tree deletion and distance lemmas adapted from @green-notes, tree.R1.H3.R1.H2.
private lemma isTree_dist_eq_length_of_isPath {U : Type} (T : SimpleGraph U) (hT : T.IsTree)
    {x y : U} (p : T.Walk x y) (hp : p.IsPath) :
    p.length = T.dist x y := by
  obtain ⟨q, hq, hqlen⟩ := hT.connected.exists_path_of_dist x y
  have hsub : (⟨p, hp⟩ : T.Path x y) = ⟨q, hq⟩ := (hT.isAcyclic.subsingleton_path x y).elim _ _
  have hpq : p = q := congrArg Subtype.val hsub
  rw [hpq, hqlen]

private lemma ncard_neighborSet_eq_degree {U : Type} [Fintype U] (T : SimpleGraph U) (u : U) :
    (T.neighborSet u).ncard = T.degree u := by
  rw [← T.card_neighborSet_eq_degree, Set.ncard_eq_toFinset_card' (T.neighborSet u)]
  simp [Set.toFinset_card]

private lemma iso_edist_eq {A B : Type*} (GA : SimpleGraph A) (GB : SimpleGraph B)
    (φ : GA ≃g GB) (a₁ a₂ : A) : GB.edist (φ a₁) (φ a₂) = GA.edist a₁ a₂ := by
  apply le_antisymm
  · dsimp only [SimpleGraph.edist]
    rw [le_iInf_iff]
    intro w
    exact (SimpleGraph.edist_le (w.map φ.toHom)).trans (by simp)
  · dsimp only [SimpleGraph.edist]
    rw [le_iInf_iff]
    intro w
    exact (SimpleGraph.edist_le ((w.map φ.symm.toHom).copy (φ.symm_apply_apply a₁) (φ.symm_apply_apply a₂))).trans
      (by rw [Nat.cast_le, Walk.length_copy, Walk.length_map])

private lemma degree_induce_compl_singleton_of_adj {U : Type} [Fintype U]
    (T : SimpleGraph U) {a v : U} (hav : a ∈ ({v}ᶜ : Set U)) (hadj : T.Adj a v) :
    (T.induce {v}ᶜ).degree ⟨a, hav⟩ + 1 = T.degree a := by
  let f : ({v}ᶜ : Set U) ↪ U := ⟨Subtype.val, Subtype.val_injective⟩
  have hmap_not : v ∉ ((T.induce {v}ᶜ).neighborFinset ⟨a, hav⟩).map f := by
    intro h
    rw [Finset.mem_map] at h
    obtain ⟨x, _, hxv⟩ := h
    exact x.2 hxv
  have heq : insert v (((T.induce {v}ᶜ).neighborFinset ⟨a, hav⟩).map f) = T.neighborFinset a := by
    ext y
    rw [Finset.mem_insert, Finset.mem_map, SimpleGraph.mem_neighborFinset]
    constructor
    · rintro (rfl | ⟨x, hx, rfl⟩)
      · exact hadj
      · rw [SimpleGraph.mem_neighborFinset] at hx
        exact hx
    · intro hay
      by_cases hyv : y = v
      · exact Or.inl hyv
      · refine Or.inr ⟨⟨y, hyv⟩, ?_, rfl⟩
        rw [SimpleGraph.mem_neighborFinset]
        exact hay
  have hcard := congrArg Finset.card heq
  rw [Finset.card_insert_of_notMem hmap_not, Finset.card_map,
    (T.induce {v}ᶜ).card_neighborFinset_eq_degree, T.card_neighborFinset_eq_degree] at hcard
  omega

private lemma degree_induce_compl_singleton_of_not_adj {U : Type} [Fintype U]
    (T : SimpleGraph U) {a v : U} (hav : a ∈ ({v}ᶜ : Set U)) (hnadj : ¬ T.Adj a v) :
    (T.induce {v}ᶜ).degree ⟨a, hav⟩ = T.degree a := by
  let f : ({v}ᶜ : Set U) ↪ U := ⟨Subtype.val, Subtype.val_injective⟩
  have heq : ((T.induce {v}ᶜ).neighborFinset ⟨a, hav⟩).map f = T.neighborFinset a := by
    ext y
    rw [Finset.mem_map, SimpleGraph.mem_neighborFinset]
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [SimpleGraph.mem_neighborFinset] at hx
      exact hx
    · intro hay
      have hyv : y ≠ v := fun h => hnadj (h ▸ hay)
      refine ⟨⟨y, hyv⟩, ?_, rfl⟩
      rw [SimpleGraph.mem_neighborFinset]
      exact hay
  have hcard := congrArg Finset.card heq
  rw [Finset.card_map, (T.induce {v}ᶜ).card_neighborFinset_eq_degree,
    T.card_neighborFinset_eq_degree] at hcard
  exact hcard

private lemma degree_induce_compl_le {U : Type} [Fintype U]
    (T : SimpleGraph U) {a v : U} (hav : a ∈ ({v}ᶜ : Set U)) :
    (T.induce {v}ᶜ).degree ⟨a, hav⟩ ≤ T.degree a := by
  by_cases hadj : T.Adj a v
  · have := degree_induce_compl_singleton_of_adj T hav hadj
    omega
  · rw [degree_induce_compl_singleton_of_not_adj T hav hadj]

private lemma induce_compl_singleton_isTree_of_deg_one {U : Type} [Fintype U]
    (T : SimpleGraph U) (hT : T.IsTree) {v : U} (hdeg1 : T.degree v = 1) :
    (T.induce {v}ᶜ).IsTree :=
  ⟨hT.connected.induce_compl_singleton_of_degree_eq_one hdeg1, hT.isAcyclic.induce {v}ᶜ⟩

private lemma induce_compl_singleton_dist_eq {U : Type} [Fintype U]
    (T : SimpleGraph U) (hT : T.IsTree) {v : U} (hT' : (T.induce {v}ᶜ).IsTree)
    (a b : ({v}ᶜ : Set U)) :
    (T.induce {v}ᶜ).dist a b = T.dist a.1 b.1 := by
  obtain ⟨p, hp, hplen⟩ := hT'.connected.exists_path_of_dist a b
  let g : T.induce {v}ᶜ →g T := (SimpleGraph.Embedding.induce ({v}ᶜ : Set U)).toHom
  have hmap : (p.map g).IsPath := hp.map Subtype.val_injective
  have hdist := isTree_dist_eq_length_of_isPath T hT (p.map g) hmap
  rw [Walk.length_map, hplen] at hdist
  exact hdist


private lemma shortest_induced {V : Type*} {G : SimpleGraph V} {u v : V}
    (p : G.Walk u v) (short : p.length = G.dist u v) :
    G.isInducedPath p.support := by
  refine ⟨(p.isPath_of_length_eq_dist short).support_nodup,?_⟩
  intro i j
  have bi : i.val ≤ p.length := by have h := i.isLt; have := p.length_support; omega
  have bj : j.val ≤ p.length := by have h := j.isLt; have := p.length_support; omega
  change G.Adj p.support[i.val] p.support[j.val] ↔ _
  rw [p.support_getElem_eq_getVert i.isLt,p.support_getElem_eq_getVert j.isLt]
  have near {a b : ℕ} (ha : a ≤ p.length) (hb : b ≤ p.length)
      (ad : G.Adj (p.getVert a) (p.getVert b)) : b ≤ a+1 := by
    have d := G.dist_le ((p.take a).append ((p.drop b).cons ad))
    rw [← short,Walk.length_append,Walk.length_cons,Walk.take_length,Walk.drop_length] at d
    omega
  constructor
  · intro h
    have ij : i.val ≠ j.val := fun eq => h.ne (congrArg p.getVert eq)
    have := near bi bj h
    have := near bj bi h.symm
    omega
  · rintro (e|e)
    · rw [← e]
      exact p.adj_getVert_succ (by omega)
    · rw [← e]
      exact (p.adj_getVert_succ (by omega)).symm


private theorem swap_arms (a b : Arm G c n)
    (apart : ∀ i j, a.vertex i ≠ b.vertex j) :
    ∃ e : G ≃g G, e c = c ∧ (∀ i, e (a.vertex i) = b.vertex i) := by
  classical
  let swap (x : V) := if h : x ∈ Set.range a.vertex then b.vertex h.choose
    else if k : x ∈ Set.range b.vertex then a.vertex k.choose else x
  have ab (i) : a.vertex i ∉ Set.range b.vertex := fun ⟨j,e⟩ => apart i j e.symm
  have ba (i) : b.vertex i ∉ Set.range a.vertex := fun ⟨j,e⟩ => apart j i e
  have left (i) : swap (a.vertex i) = b.vertex i := by
    let h : a.vertex i ∈ Set.range a.vertex := ⟨i,rfl⟩
    simp only [swap,dif_pos h]
    exact congrArg b.vertex (a.vertex.injective h.choose_spec)
  have right (i) : swap (b.vertex i) = a.vertex i := by
    let k : b.vertex i ∈ Set.range b.vertex := ⟨i,rfl⟩
    simp only [swap,dif_neg (ba i),dif_pos k]
    exact congrArg a.vertex (b.vertex.injective k.choose_spec)
  have fixed {x} (hx : x ∉ Set.range a.vertex) (hy : x ∉ Set.range b.vertex) : swap x = x := by
    simp only [swap,dif_neg hx,dif_neg hy]
  have cases (x : V) : (∃ i, a.vertex i = x) ∨ (∃ i, b.vertex i = x) ∨
      (x ∉ Set.range a.vertex ∧ x ∉ Set.range b.vertex) := by
    by_cases h : x ∈ Set.range a.vertex
    · exact Or.inl h
    · by_cases k : x ∈ Set.range b.vertex
      · exact Or.inr (Or.inl k)
      · exact Or.inr (Or.inr ⟨h,k⟩)
  have undo (x : V) : swap (swap x) = x := by
    rcases cases x with ⟨i,rfl⟩ | ⟨i,rfl⟩ | ⟨ha,hb⟩
    · rw [left,right]
    · rw [right,left]
    · rw [fixed ha hb,fixed ha hb]
  have cross (i j) : ¬ G.Adj (a.vertex i) (b.vertex j) := by
    intro h
    exact b.away j ((a.external i _ (ba j)).mp h).2
  have respects (x y) : G.Adj (swap x) (swap y) ↔ G.Adj x y := by
    rcases cases x with ⟨i,rfl⟩ | ⟨i,rfl⟩ | ⟨xa,xb⟩ <;>
      rcases cases y with ⟨j,rfl⟩ | ⟨j,rfl⟩ | ⟨ya,yb⟩
    · rw [left,left,a.internal,b.internal]
    · rw [left,right]; exact iff_of_false (fun h => cross j i h.symm) (cross i j)
    · rw [left,fixed ya yb,a.external i y ya,b.external i y yb]
    · rw [right,left]; exact iff_of_false (cross i j) (fun h => cross j i h.symm)
    · rw [right,right,a.internal,b.internal]
    · rw [right,fixed ya yb,a.external i y ya,b.external i y yb]
    · rw [fixed xa xb,left,G.adj_comm x (b.vertex j),G.adj_comm x (a.vertex j),
        a.external j x xa,b.external j x xb]
    · rw [fixed xa xb,right,G.adj_comm x (a.vertex j),G.adj_comm x (b.vertex j),
        a.external j x xa,b.external j x xb]
    · rw [fixed xa xb,fixed ya yb]
  have ac : c ∉ Set.range a.vertex := fun ⟨i,h⟩ => a.away i h
  have bc : c ∉ Set.range b.vertex := fun ⟨i,h⟩ => b.away i h
  let e : G ≃g G :=
    {toFun := swap
     invFun := swap
     left_inv := undo
     right_inv := undo
     map_rel_iff' := fun {x y} => respects x y}
  exact ⟨e,fixed ac bc,left⟩

private lemma Arm.degree_bound [Fintype V] (a : Arm G c n) (i : Fin n) :
    (G.neighborSet (a.vertex i)).ncard ≤ 2 := by
  classical
  let prev := if hi : 0 < i.val then a.vertex ⟨i.val-1,by omega⟩ else c
  let next := if hi : i.val+1 < n then a.vertex ⟨i.val+1,hi⟩ else c
  have sub : G.neighborSet (a.vertex i) ⊆ ({prev,next} : Set V) := by
    intro x hx
    change G.Adj (a.vertex i) x at hx
    by_cases h : x ∈ Set.range a.vertex
    · obtain ⟨j,rfl⟩ := h
      rcases (a.internal i j).mp hx with ij|ji
      · have hi : i.val+1 < n := by omega
        right
        simp only [Set.mem_singleton_iff,next,dif_pos hi]
        exact congrArg a.vertex (Fin.ext ij.symm)
      · have hi : 0 < i.val := by omega
        left
        simp only [prev,dif_pos hi]
        exact congrArg a.vertex (Fin.ext (by change j.val = i.val-1; omega))
    · obtain ⟨zero,rfl⟩ := (a.external i x h).mp hx
      left
      simp [prev,zero]
  apply (Set.ncard_le_ncard sub).trans
  by_cases h : prev=next
  · simp [h]
  · exact (Set.ncard_pair h).le

private lemma Arm.tip_only (a : Arm G c (n+2)) (x : V) :
    G.Adj (a.vertex (Fin.last (n+1))) x ↔ x = a.vertex (Fin.last n).castSucc := by
  constructor
  · intro ad
    by_cases h : x ∈ Set.range a.vertex
    · obtain ⟨j,rfl⟩ := h
      have := (a.internal _ j).mp ad
      apply congrArg a.vertex
      apply Fin.ext
      simp only [Fin.val_last,Fin.val_castSucc] at *
      omega
    · have := ((a.external _ x h).mp ad).1
      simp at this
  · rintro rfl
    exact (a.internal _ _).mpr (Or.inr rfl)

private def Arm.map {W : Type*} {H : SimpleGraph W} (a : Arm G c n) (f : G ≃g H) :
    Arm H (f c) n where
  vertex := a.vertex.trans f.toEquiv.toEmbedding
  away i := fun h => a.away i (f.injective h)
  internal i j := f.map_adj_iff.trans (a.internal i j)
  external i y hy := by
    have pre : f.symm y ∉ Set.range a.vertex := by
      rintro ⟨j,h⟩
      exact hy ⟨j,by simp [h]⟩
    have eq : G.Adj (a.vertex i) (f.symm y) ↔ H.Adj (f (a.vertex i)) y := by
      rw [← f.map_adj_iff]; simp
    change H.Adj (f (a.vertex i)) y ↔ _
    rw [← eq,a.external i _ pre]
    exact and_congr_right fun _ => f.toEquiv.symm_apply_eq

private def Arm.shorten (a : Arm G c (n+1)) :
    Arm (G.induce {a.vertex (Fin.last n)}ᶜ)
      (⟨c,(a.away (Fin.last n)).symm⟩ : ({a.vertex (Fin.last n)}ᶜ : Set V)) n where
  vertex := ⟨fun i => ⟨a.vertex i.castSucc,fun h => Fin.castSucc_ne_last i (a.vertex.injective h)⟩,
    fun _ _ h => Fin.castSucc_injective _ (a.vertex.injective (congrArg Subtype.val h))⟩
  away i := fun h => a.away i.castSucc (congrArg Subtype.val h)
  internal i j := a.internal i.castSucc j.castSucc
  external i y hy := by
    have pre : y.val ∉ Set.range a.vertex := by
      rintro ⟨j,h⟩
      refine Fin.lastCases (motive := fun j => a.vertex j = y.val → False) ?_ ?_ j h
      · exact fun e => y.property e.symm
      · intro k e
        exact hy ⟨k,Subtype.ext e⟩
    change G.Adj (a.vertex i.castSucc) y.val ↔ _
    rw [a.external _ _ pre]
    simp [Subtype.ext_iff]

private theorem Arm.cross {x z : V} (a : Arm G c n)
    (hx : x ∈ Set.range a.vertex) (hz : z ∉ Set.range a.vertex)
    (p : G.Walk x z) : c ∈ p.support := by
  induction p with
  | nil => exact (hz hx).elim
  | @cons u v w h q ih =>
    by_cases vmem : v ∈ Set.range a.vertex
    · exact List.mem_cons_of_mem _ (ih vmem hz)
    · obtain ⟨i,rfl⟩ := hx
      have e := ((a.external i v vmem).mp h).2
      exact List.mem_cons_of_mem _ (e ▸ q.start_mem_support)

private theorem Arm.dist_outside [Fintype V] (a : Arm G c n) (conn : G.Connected)
    {x y : V} (hx : x ∈ Set.range a.vertex) (hy : y ∉ Set.range a.vertex) :
    G.dist x y = G.dist x c + G.dist c y := by
  classical
  obtain ⟨p,_,len⟩ := conn.exists_path_of_dist x y
  have hc := a.cross hx hy p
  let l := p.takeUntil c hc
  let r := p.dropUntil c hc
  have le := G.dist_le l
  have re := G.dist_le r
  have sz := congrArg Walk.length (p.take_spec hc)
  rw [Walk.length_append] at sz
  change l.length + r.length = p.length at sz
  have tr := (conn x c).dist_triangle_left y
  omega

private lemma Arm.internalNear (a : Arm G c n) (i j : Fin n) :
    G.dist (a.vertex i) (a.vertex j) < n := by
  classical
  let f : pathGraph n →g G :=
    { toFun := a.vertex
      map_rel' := fun {i j} h => (a.internal i j).mpr (pathGraph_adj.mp h) }
  obtain ⟨p,hp,_⟩ := ((pathGraph_preconnected n) i j).exists_path_of_dist
  have l := G.dist_le (p.map f)
  simp only [Walk.length_map] at l
  have q := hp.length_lt
  simp only [Fintype.card_fin] at q
  exact lt_of_le_of_lt l q

private lemma arms_disjoint_of_far (a b : Arm G c n) (conn : G.Connected) {i j : Fin n}
    (far : 2*n ≤ G.dist (a.vertex i) (b.vertex j)) :
    ∀ p q, a.vertex p ≠ b.vertex q := by
  intro p q e
  have l := a.internalNear i p
  have k := b.internalNear q j
  have tr := (conn (a.vertex i) (a.vertex p)).dist_triangle_left (b.vertex j)
  rw [e] at l tr
  omega

private lemma degree_center [Fintype V] (conn : G.Connected) (a b : Arm G c (n+1))
    (apart : ∀ i j, a.vertex i ≠ b.vertex j)
    (branch : ∃ u : V, 3 ≤ (G.neighborSet u).ncard) :
    3 ≤ (G.neighborSet c).ncard := by
  classical
  by_contra! d
  have edge (a : Arm G c (n+1)) : G.Adj c (a.vertex 0) := by
    have only := a.external 0 c (fun ⟨j,h⟩ => a.away j h)
    exact (only.mpr ⟨rfl,rfl⟩).symm
  have first {y} (h : G.Adj c y) : y=a.vertex 0 ∨ y=b.vertex 0 := by
    by_contra! ne
    exact (Nat.not_lt_of_ge (show (G.neighborSet c).ncard ≤ 2 by omega))
      ((Set.two_lt_ncard_iff (Set.toFinite _)).mpr ⟨a.vertex 0,b.vertex 0,y,edge a,edge b,h,
        apart 0 0,ne.1.symm,ne.2.symm⟩)
  let S (u : V) : Prop := u=c ∨ u∈Set.range a.vertex ∨ u∈Set.range b.vertex
  have closed {x y} (hx : S x) (ad : G.Adj x y) : S y := by
    rcases hx with rfl | ⟨i,rfl⟩ | ⟨j,rfl⟩
    · rcases first ad with rfl|rfl
      · exact Or.inr (Or.inl ⟨0,rfl⟩)
      · exact Or.inr (Or.inr ⟨0,rfl⟩)
    · by_cases h : y∈Set.range a.vertex
      · exact Or.inr (Or.inl h)
      · exact Or.inl ((a.external _ _ h).mp ad).2
    · by_cases h : y∈Set.range b.vertex
      · exact Or.inr (Or.inr h)
      · exact Or.inl ((b.external _ _ h).mp ad).2
  have propagate {u v} (p : G.Walk u v) (h : S u) : S v := by
    induction p with
    | nil => exact h
    | cons ad p ih => exact ih (closed h ad)
  obtain ⟨u,hu⟩ := branch
  rcases propagate (conn c u).some (Or.inl rfl) with rfl|⟨i,rfl⟩|⟨j,rfl⟩
  · omega
  · have := a.degree_bound i; omega
  · have := b.degree_bound j; omega

private lemma arm_from_component {V : Type*} [Fintype V] (G : SimpleGraph V) (c : V)
    {n : Nat} (hn : 0<n) (f : Fin (n+1) ↪ V) (start : f 0 = c)
    (induced : ∀ i j, G.Adj (f i) (f j) ↔ i.val+1=j.val ∨ j.val+1=i.val)
    (small : ∀ C : (G.induce {c}ᶜ).ConnectedComponent, C.supp.ncard ≤ n) :
    ∃ a : Arm G c n, ∀ i, a.vertex i = f i.succ := by
  classical
  have away (i : Fin n) : f i.succ ≠ c := by
    rw [← start]; exact fun h => Fin.succ_ne_zero _ (f.injective h)
  let g (i : Fin n) : ({c}ᶜ : Set V) := ⟨f i.succ,away i⟩
  let u : Fin n := ⟨0,hn⟩
  let graph := G.induce {c}ᶜ
  let hom : pathGraph n →g graph :=
    { toFun := g
      map_rel' := fun {i j} h => (induced i.succ j.succ).mpr (by
        have := pathGraph_adj.mp h
        simp only [Fin.val_succ]
        omega) }
  let C := graph.connectedComponentMk (g u)
  have mem (i : Fin n) : g i ∈ C.supp :=
    ConnectedComponent.sound (((pathGraph_preconnected n) i u).map hom)
  let emb (i : Fin n) : C.supp := ⟨g i,mem i⟩
  have inj : Function.Injective emb := by
    intro i j e
    exact Fin.succ_injective n (f.injective (congrArg (fun z : C.supp => z.1.1) e))
  have box : Fintype.card C.supp ≤ n := by rw [Set.fintypeCard_eq_ncard]; exact small C
  have counter := Fintype.card_le_of_injective emb inj
  have onto : Function.Surjective emb :=
    ((Fintype.bijective_iff_injective_and_card emb).mpr ⟨inj,by simpa using le_antisymm counter (by simpa using box)⟩).2
  let tail : Fin n ↪ V := ⟨fun i => f i.succ,fun _ _ h => Fin.succ_injective n (f.injective h)⟩
  refine ⟨⟨tail,away,?_,?_⟩,fun _ => rfl⟩
  · intro i j
    change G.Adj (f i.succ) (f j.succ) ↔ _
    rw [induced]
    simp only [Fin.val_succ]
    omega
  · intro i y out
    by_cases eq : y=c
    · subst y
      change G.Adj (f i.succ) c ↔ _
      rw [← start,induced]
      simp [Fin.val_succ]
    · suffices ¬ G.Adj (tail i) y by simp [this,eq]
      intro ad
      let z : ({c}ᶜ : Set V) := ⟨y,eq⟩
      have adj : graph.Adj (g i) z := ad
      have zz := (C.mem_supp_congr_adj adj).mp (mem i)
      obtain ⟨j,hj⟩ := onto ⟨z,zz⟩
      exact out ⟨j,congrArg (fun z : C.supp => z.1.1) hj⟩

private lemma max_arm {V : Type*} [Fintype V] (G : SimpleGraph V) (conn : G.Connected)
    (c x : V) (k : ℕ) (hx : G.dist c x = k+1)
    (small : ∀ C : (G.induce {c}ᶜ).ConnectedComponent, C.supp.ncard ≤ k+1) :
    ∃ a : Arm G c (k+1), a.vertex (Fin.last k) = x := by
  classical
  obtain ⟨p,path,hlen⟩ := conn.exists_path_of_dist c x
  have len : p.length = k+1 := hlen.trans hx
  let f : Fin (k+1+1) ↪ V :=
    ⟨fun i => p.getVert i.val,fun i j h => Fin.ext (path.getVert_injOn (show i.val ≤ p.length by omega) (show j.val ≤ p.length by omega) h)⟩
  have ad (i j : Fin (k+1+1)) :
      G.Adj (f i) (f j) ↔ i.val+1=j.val ∨ j.val+1=i.val := by
    let cv (i : Fin (k+1+1)) : Fin p.support.length :=
      ⟨i.val,by rw [p.length_support,len];exact i.isLt⟩
    have eq (i : Fin (k+1+1)) : p.support.get (cv i) = f i :=
      p.support_getElem_eq_getVert (cv i).isLt
    simpa only [eq,cv] using (shortest_induced p hlen).2 (cv i) (cv j)
  obtain ⟨a,ha⟩ := arm_from_component G c (by omega) f (by change p.getVert 0 = c; exact p.getVert_zero) ad small
  refine ⟨a,?_⟩
  rw [ha]
  change p.getVert (k+1) = x
  rw [←len,p.getVert_length]

private lemma hub_and_tips {V : Type} [Fintype V] (G : SimpleGraph V) (tree : G.IsTree)
    (c : V) (k : Nat) (hd : G.diam = 2*(k+2)) (he : G.eccent c = k+2)
    (small : ∀ C : (G.induce {c}ᶜ).ConnectedComponent, C.supp.ncard ≤ k+2)
    (br : ∃ x, 3 ≤ (G.neighborSet x).ncard) :
    3 ≤ G.degree c ∧ (∀ x, G.dist c x ≤ k+2) ∧
      ∀ v, ∃ a : Arm G c (k+2), a.vertex (Fin.last (k+1)) ≠ v ∧
        G.dist c (a.vertex (Fin.last (k+1))) = k+2 := by
  classical
  have : Nonempty V := tree.connected.nonempty
  have upper (x : V) : G.dist c x ≤ k+2 := by
    apply (Nat.cast_le (α := ℕ∞)).mp
    rw [(tree.connected c x).coe_dist_eq_edist]
    have h := @edist_le_eccent _ G c x
    simpa [he] using h
  obtain ⟨u,w,e⟩ := G.exists_dist_eq_diam
  have far := e.trans hd
  have tr := (tree.connected u c).dist_triangle_left w
  rw [(G.dist_comm (u:=u) (v:=c))] at tr
  have uc : G.dist c u = k+2 := by have := upper u; have := upper w; omega
  have wc : G.dist c w = k+2 := by have := upper w; omega
  obtain ⟨a,au⟩ := max_arm G tree.connected c u (k+1) uc small
  obtain ⟨b,bw⟩ := max_arm G tree.connected c w (k+1) wc small
  have far' : 2*(k+2) ≤ G.dist (a.vertex (Fin.last (k+1))) (b.vertex (Fin.last (k+1))) := by
    rw [au,bw,far]
  have dg := degree_center tree.connected a b (arms_disjoint_of_far a b tree.connected far') br
  rw [ncard_neighborSet_eq_degree] at dg
  refine ⟨dg,upper,?_⟩
  intro v
  by_cases eq : u=v
  · refine ⟨b,?_,by rwa [bw]⟩
    rw [bw,←eq]
    intro h
    rw [h,G.dist_self] at far
    omega
  · exact ⟨a,by rwa [au],by rwa [au]⟩

private lemma hub_card {V : Type} [Fintype V] (G : SimpleGraph V) (tree : G.IsTree)
    (c v : V) (k : Nat) (dc : 3 ≤ G.degree c) (dv : G.degree v = 1)
    (noLeaf : ∀ x, G.Adj c x → 2 ≤ (G.neighborSet x).ncard)
    (upper : ∀ x, G.dist c x ≤ k+2)
    (surv : ∃ a : Arm G c (k+2), a.vertex (Fin.last (k+1)) ≠ v ∧
        G.dist c (a.vertex (Fin.last (k+1))) = k+2) :
    ∀ z : ({v}ᶜ : Set V), (3 ≤ (G.induce {v}ᶜ).degree z ∧
      ∀ x, (G.induce {v}ᶜ).dist z x ≤ k+2) ↔ z.val=c := by
  classical
  have cardTree := induce_compl_singleton_isTree_of_deg_one G tree dv
  have distances := induce_compl_singleton_dist_eq G tree cardTree
  intro z
  constructor
  · rintro ⟨branch,ecc⟩
    obtain ⟨a,ne,dist⟩ := surv
    let tip := a.vertex (Fin.last (k+1))
    have high : 3 ≤ G.degree z.val := branch.trans (degree_induce_compl_le G z.property)
    have notIn : z.val ∉ Set.range a.vertex := by
      rintro ⟨i,eq⟩
      have b := a.degree_bound i
      rw [ncard_neighborSet_eq_degree,eq] at b
      omega
    have split := a.dist_outside tree.connected (Set.mem_range_self _) notIn (x := tip)
    have low := ecc ⟨tip,ne⟩
    rw [distances,(G.dist_comm (u:=z.val) (v:=tip)),split,(G.dist_comm (u:=tip) (v:=c))] at low
    change G.dist c tip = k+2 at dist
    have zero : G.dist c z.val = 0 := by omega
    exact ((tree.connected c z.val).dist_eq_zero_iff.mp zero).symm
  · intro eq
    have no : ¬G.Adj c v := by
      intro cv
      have q := noLeaf v cv
      rw [ncard_neighborSet_eq_degree,dv] at q
      omega
    refine ⟨?_,?_⟩
    · rw [degree_induce_compl_singleton_of_not_adj G z.property (eq ▸ no),eq]
      exact dc
    · intro x
      rw [distances,eq]
      exact upper _

private lemma swap_or_same (a b : Arm G c (n+1)) :
    ∃ e : G ≃g G, e c = c ∧ ∀ i, e (a.vertex i) = b.vertex i := by
  by_cases apart : ∀ i j, a.vertex i ≠ b.vertex j
  · exact swap_arms a b apart
  push Not at apart
  obtain ⟨s,t,m⟩ := apart
  have propagate {i j : Fin (n+1)} (w : (pathGraph (n+1)).Walk i j)
      (hi : a.vertex i ∈ Set.range b.vertex) : a.vertex j ∈ Set.range b.vertex := by
    induction w with
    | nil => exact hi
    | @cons i j k ad p ih =>
      apply ih
      by_contra out
      obtain ⟨l,e⟩ := hi
      have h := (a.internal i j).mpr (pathGraph_adj.mp ad)
      rw [←e] at h
      exact a.away j ((b.external l _ out).mp h).2
  have incl (i) : a.vertex i ∈ Set.range b.vertex :=
    propagate ((pathGraph_preconnected _ s i).some) ⟨t,m.symm⟩
  choose f eq using incl
  have inj : Function.Injective f := fun i j h =>
    a.vertex.injective (by rw [←eq i,←eq j,h])
  have edge (a : Arm G c (n+1)) : G.Adj (a.vertex 0) c :=
    (a.external 0 c (fun ⟨j,h⟩ => a.away j h)).mpr ⟨rfl,rfl⟩
  have f0 : f 0 = 0 := by
    apply Fin.ext
    apply ((b.external (f 0) c (fun ⟨j,h⟩ => b.away j h)).mp _).1
    rw [eq]; exact edge a
  have all (i : Fin (n+1)) : f i = i := by
    induction i using WellFoundedLT.induction with
    | _ i ih =>
      by_cases z : i.val=0
      · have : i=0 := Fin.ext z
        simpa [this] using f0
      · let j : Fin (n+1) := ⟨i.val-1,by omega⟩
        have ji : j < i := by change i.val-1 < i.val;omega
        have sj : j.val+1=i.val := by dsimp [j];omega
        have adj := (a.internal j i).mpr (Or.inl sj)
        rw [←eq j,←eq i,ih j ji] at adj
        rcases (b.internal j (f i)).mp adj with h|h
        · exact Fin.ext (h.symm.trans sj)
        · have lt : f i < i := by change (f i).val < i.val;omega
          have rep := ih (f i) lt
          have same := inj rep
          exact (Fin.ne_of_lt lt same).elim
  exact ⟨SimpleGraph.Iso.refl,rfl,fun i => by change a.vertex i=b.vertex i;rw [←eq i,all]⟩

private lemma extend_card {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    {v : V} {w : W} (f : G.induce {v}ᶜ ≃g H.induce {w}ᶜ)
    (ad : ∀ x : ({v}ᶜ : Set V), G.Adj v x.val ↔ H.Adj w (f x).val) :
    Nonempty (G ≃g H) := by
  classical
  let map (x : V) : W := if h : x=v then w else (f ⟨x,h⟩).val
  let inv (y : W) : V := if h : y=w then v else (f.symm ⟨y,h⟩).val
  have mv : map v = w := by simp [map]
  have iw : inv w = v := by simp [inv]
  have mc (x : ({v}ᶜ : Set V)) : map x.val = (f x).val := by simp [map,show x.val ≠ v from x.property]
  have ic (y : ({w}ᶜ : Set W)) : inv y.val = (f.symm y).val := by simp [inv,show y.val ≠ w from y.property]
  refine ⟨{toFun := map, invFun := inv, left_inv := ?_, right_inv := ?_, map_rel_iff' := ?_}⟩
  · intro x
    by_cases h : x=v
    · simp [h,mv,iw]
    · change inv (map (⟨x,h⟩ : ({v}ᶜ : Set V)).val) = x
      rw [mc,ic]; simp
  · intro y
    by_cases h : y=w
    · simp [h,mv,iw]
    · change map (inv (⟨y,h⟩ : ({w}ᶜ : Set W)).val) = y
      rw [ic,mc]; simp
  · intro x y
    change H.Adj (map x) (map y) ↔ G.Adj x y
    by_cases hx : x=v <;> by_cases hy : y=v
    · simp [hx,hy]
    · subst x
      rw [mv,show map y = _ from mc ⟨y,hy⟩]
      exact (ad ⟨y,hy⟩).symm
    · subst y
      rw [mv,show map x = _ from mc ⟨x,hx⟩,H.adj_comm _ w,G.adj_comm _ v]
      exact (ad ⟨x,hx⟩).symm
    · rw [show map x = _ from mc ⟨x,hx⟩,show map y = _ from mc ⟨y,hy⟩]
      exact f.map_adj_iff

private def Arm.recenter {d : V} (a : Arm G c n) (e : c=d) : Arm G d n where
  vertex := a.vertex
  away i := by rw [←e];exact a.away i
  internal := a.internal
  external i x h := by rw [←e];exact a.external i x h

private lemma Arm.tip_deg [Fintype V] (a : Arm G c (n+2)) :
    G.degree (a.vertex (Fin.last (n+1))) = 1 := by
  apply degree_eq_one_iff_existsUnique_adj.mpr
  exact ⟨_,(a.tip_only _).mpr rfl,fun x h => (a.tip_only x).mp h⟩

private lemma match_radial_cards {V W : Type} [Fintype V] [Fintype W] {G : SimpleGraph V}
    {H : SimpleGraph W} {c : V} {d : W} {n : Nat} (a : Arm G c (n+2)) (b : Arm H d (n+2))
    (f : G.induce {a.vertex (Fin.last (n+1))}ᶜ ≃g H.induce {b.vertex (Fin.last (n+1))}ᶜ)
    (hub : f ⟨c,(a.away _).symm⟩ = ⟨d,(b.away _).symm⟩) : Nonempty (G ≃g H) := by
  let A := (a.shorten.map f).recenter hub
  let B := b.shorten
  obtain ⟨g,_,all⟩ := swap_or_same A B
  let e := f.trans g
  apply extend_card e
  intro x
  rw [a.tip_only,b.tip_only]
  let s := a.shorten.vertex (Fin.last n)
  let t := b.shorten.vertex (Fin.last n)
  have eq : e s=t := all (Fin.last n)
  change x.val = s.val ↔ (e x).val = t.val
  rw [←Subtype.ext_iff,←Subtype.ext_iff,←eq]
  exact e.injective.eq_iff.symm

private lemma match_radial {V W : Type} [Fintype V] [Fintype W] {G : SimpleGraph V}
    {H : SimpleGraph W} {c v : V} {d w : W} {k : Nat} (a : Arm G c (k+2)) (b : Arm H d (k+2))
    (av : a.vertex (Fin.last (k+1)) = v) (bw : b.vertex (Fin.last (k+1)) = w)
    (f : G.induce {v}ᶜ ≃g H.induce {w}ᶜ) {cv : c≠v} {dw : d≠w}
    (hub : f ⟨c,cv⟩ = ⟨d,dw⟩) : Nonempty (G ≃g H) := by
  subst v w
  exact match_radial_cards a b f hub

private noncomputable def level [Fintype V] (G : SimpleGraph V) (c : V) (r : Nat) : Finset V :=
  Finset.univ.filter (fun x => G.dist c x = r)

private lemma level_card_delete {V : Type} [Fintype V] (G : SimpleGraph V)
    (tr : G.IsTree) {c v : V} (dv : G.degree v = 1) (ne : c ≠ v) (r : Nat) :
    (level G c r).card =
      (level (G.induce {v}ᶜ) (⟨c,ne⟩ : ({v}ᶜ : Set V)) r).card +
        if G.dist c v = r then 1 else 0 := by
  classical
  let f : ({v}ᶜ : Set V) ↪ V := ⟨Subtype.val,Subtype.val_injective⟩
  have eq : (level (G.induce {v}ᶜ) (⟨c,ne⟩ : ({v}ᶜ : Set V)) r).map f = (level G c r).erase v := by
    ext x
    rw [Finset.mem_map,Finset.mem_erase]
    have dist := induce_compl_singleton_dist_eq G tr (induce_compl_singleton_isTree_of_deg_one G tr dv)
    constructor
    · rintro ⟨y,hy,rfl⟩
      refine ⟨y.property,?_⟩
      simpa [level,dist,f] using hy
    · rintro ⟨nx,hx⟩
      refine ⟨⟨x,nx⟩,?_,rfl⟩
      simpa [level,dist] using hx
  have card := congrArg Finset.card eq
  rw [Finset.card_map] at card
  rw [card]
  by_cases d : G.dist c v = r
  · have mem : v ∈ level G c r := by simpa [level] using d
    simp [d,Finset.card_erase_add_one mem]
  · have no : v ∉ level G c r := by simpa [level] using d
    simp [d,Finset.erase_eq_of_notMem no]

private lemma iso_dist {A B : Type*} {S : SimpleGraph A} {T : SimpleGraph B}
    (f : S ≃g T) (x y) : T.dist (f x) (f y) = S.dist x y :=
  congrArg ENat.toNat (iso_edist_eq _ _ _ x y)

private lemma size_level_iso {W : Type*} {H : SimpleGraph W} [Fintype V] [Fintype W]
    (f : G ≃g H) (c : V) (r : Nat) : (level G c r).card = (level H (f c) r).card := by
  classical
  apply Finset.card_bij' (fun x _ => f x) (fun y _ => f.symm y)
  · intro x hx
    simpa [level,iso_dist] using hx
  · intro y hy
    have z := iso_dist f c (f.symm y)
    simp at z
    simpa [level,z] using hy
  · simp
  · simp

private lemma iso_hubs {V W : Type} [Fintype V] [Fintype W] {G : SimpleGraph V}
    {H : SimpleGraph W} {c d v w} {r : Nat} (cv : c ≠ v) (dw : d ≠ w)
    (f : G.induce {v}ᶜ ≃g H.induce {w}ᶜ)
    (left : ∀ z : ({v}ᶜ : Set V), (3 ≤ (G.induce {v}ᶜ).degree z ∧
      ∀ x, (G.induce {v}ᶜ).dist z x ≤ r) ↔ z.val = c)
    (right : ∀ z : ({w}ᶜ : Set W), (3 ≤ (H.induce {w}ᶜ).degree z ∧
      ∀ x, (H.induce {w}ᶜ).dist z x ≤ r) ↔ z.val = d) :
    f ⟨c,cv⟩ = ⟨d,dw⟩ := by
  let z : ({v}ᶜ : Set V) := ⟨c,cv⟩
  have L := (left z).mpr rfl
  apply Subtype.ext
  apply (right (f z)).mp
  refine ⟨?_,?_⟩
  · rw [f.degree_eq]
    exact L.1
  · intro y
    obtain ⟨x,rfl⟩ := f.surjective y
    rw [iso_dist]
    exact L.2 x


end TreeArms
end OMA
namespace KellyStep5

section Solution
open SimpleGraph OMA.TreeArms Classical

theorem result : OMA.R_ReconstructionConjecture_reconstruction_conjecture_variants_tree_R1_H3_R1.H3 := by
  intro V W _ _ _ G H σ tg th cards deg bg r c d hr dg dh eg eh _ _ _ _ nlG nlH smallG smallH
  obtain ⟨k,rfl⟩ : ∃ k, r=k+2 := ⟨r-2,by omega⟩
  have bh : ∃ w, 3 ≤ (H.neighborSet w).ncard := by
    obtain ⟨v,bv⟩ := bg
    exact ⟨σ v,by rwa [←deg]⟩
  obtain ⟨dc,upG,tipG⟩ := hub_and_tips G tg c k dg eg smallG bg
  obtain ⟨dd,upH,tipH⟩ := hub_and_tips H th d k dh eh smallH bh
  have deg' (v) : G.degree v = H.degree (σ v) := by
    simpa only [ncard_neighborSet_eq_degree] using deg v
  let f (v) := (cards v).some
  have neqG (v) (leaf : G.degree v=1) : c ≠ v := by rintro rfl;omega
  have neqH (v) (leaf : G.degree v=1) : d ≠ σ v := by
    have := deg' v
    intro eq
    rw [eq] at dd
    omega
  have rooted (v) (leaf : G.degree v=1) :
      f v ⟨c,neqG v leaf⟩ = ⟨d,neqH v leaf⟩ := by
    apply iso_hubs _ _ (f v)
    · exact hub_card G tg c v k dc leaf nlG upG (tipG v)
    · exact hub_card H th d (σ v) k dd ((deg' v).symm.trans leaf) nlH upH (tipH (σ v))
  have bal (v) (leaf : G.degree v=1) :
      (level G c (k+2)).card + (if H.dist d (σ v)=k+2 then 1 else 0)
      = (level H d (k+2)).card + (if G.dist c v=k+2 then 1 else 0) := by
    have l := level_card_delete G tg leaf (neqG v leaf) (k+2)
    have r := level_card_delete H th ((deg' v).symm.trans leaf) (neqH v leaf) (k+2)
    have s := size_level_iso (f v) (⟨c,neqG v leaf⟩ : ({v}ᶜ : Set V)) (k+2)
    rw [rooted v leaf] at s
    omega
  obtain ⟨a,_,far⟩ := tipG c
  let v := a.vertex (Fin.last (k+1))
  change G.dist c v=k+2 at far
  obtain ⟨b,_,far'⟩ := tipH d
  let u := σ.symm (b.vertex (Fin.last (k+1)))
  have eu : σ u = b.vertex (Fin.last (k+1)) := σ.apply_symm_apply _
  have ul : G.degree u=1 := by rw [deg',eu,b.tip_deg]
  have balG := bal v a.tip_deg
  have balH := bal u ul
  rw [if_pos far] at balG
  rw [eu,if_pos far'] at balH
  have radial : H.dist d (σ v) = k+2 := by
    by_contra bad
    rw [if_neg bad] at balG
    split at balH <;> omega
  obtain ⟨arm,endpt⟩ := max_arm H th.connected d (σ v) (k+1) radial smallH
  exact match_radial a arm rfl endpt (f v) (rooted v a.tip_deg)

end Solution

end KellyStep5

namespace KellyStep6

-- Step ReconstructionConjecture.reconstruction_conjecture.variants.tree.R1.H4.R1.H1
-- Credit: @jared-jasinski

namespace ReconTreeH4R1H1

open SimpleGraph

private abbrev pathG (m : ℕ) : SimpleGraph (Fin m) where
  Adj i j := i.val + 1 = j.val ∨ j.val + 1 = i.val
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨fun _ h => by omega⟩

private lemma pathG_neighborSet_ncard_le_two (m : ℕ) (i : Fin m) :
    ((pathG m).neighborSet i).ncard ≤ 2 := by
  have hsub : (pathG m).neighborSet i ⊆
      ({j : Fin m | j.val = i.val + 1} ∪ {j : Fin m | j.val + 1 = i.val}) := by
    intro j hj
    rcases hj with h | h
    · exact Or.inl h.symm
    · exact Or.inr h
  have h1 : ({j : Fin m | j.val = i.val + 1}).ncard ≤ 1 :=
    (Set.ncard_le_one (Set.toFinite _)).mpr fun a ha b hb => by
      change a.val = i.val + 1 at ha
      change b.val = i.val + 1 at hb
      exact Fin.ext (ha.trans hb.symm)
  have h2 : ({j : Fin m | j.val + 1 = i.val}).ncard ≤ 1 :=
    (Set.ncard_le_one (Set.toFinite _)).mpr fun a ha b hb => by
      change a.val + 1 = i.val at ha
      change b.val + 1 = i.val at hb
      exact Fin.ext (by omega)
  calc
    ((pathG m).neighborSet i).ncard
        ≤ ({j : Fin m | j.val = i.val + 1} ∪ {j : Fin m | j.val + 1 = i.val}).ncard :=
          Set.ncard_le_ncard hsub
    _ ≤ ({j : Fin m | j.val = i.val + 1}).ncard + ({j : Fin m | j.val + 1 = i.val}).ncard :=
          Set.ncard_union_le _ _
    _ ≤ 2 := by omega

-- Walk of length k in G along an induced pathG m, for k < m.
private lemma walk_of_pathG_iso {V : Type} {G : SimpleGraph V} {S : Finset V} {m : ℕ}
    (e : G.induce (S : Set V) ≃g pathG m) :
    ∀ (k : ℕ) (hk : k < m),
      ∃ p : G.Walk (e.symm ⟨0, by omega⟩).val (e.symm ⟨k, hk⟩).val,
        p.length = k ∧ p.IsPath ∧
        ∀ x ∈ p.support, ∃ i : Fin m, i.val ≤ k ∧ x = (e.symm i).val := by
  intro k
  induction k with
  | zero =>
    intro hk
    refine ⟨Walk.nil, rfl, Walk.IsPath.nil, ?_⟩
    intro x hx
    simp only [Walk.support_nil, List.mem_singleton] at hx
    exact ⟨⟨0, hk⟩, le_rfl, hx⟩
  | succ k ih =>
    intro hk
    obtain ⟨p, hlen, hpath, hsupp⟩ := ih (by omega)
    have hadj_path : (pathG m).Adj ⟨k, by omega⟩ ⟨k + 1, hk⟩ := Or.inl rfl
    have hadj_G : G.Adj (e.symm ⟨k, by omega⟩).val (e.symm ⟨k + 1, hk⟩).val :=
      (e.symm.map_rel_iff).mpr hadj_path
    have hnotmem : (e.symm ⟨k + 1, hk⟩).val ∉ p.support := by
      intro hmem
      obtain ⟨i, hi, heq⟩ := hsupp _ hmem
      have hsub : e.symm ⟨k + 1, hk⟩ = e.symm i := Subtype.ext heq
      have hfin : (⟨k + 1, hk⟩ : Fin m) = i := e.symm.injective hsub
      have : k + 1 = i.val := congrArg Fin.val hfin
      omega
    let q := p.concat hadj_G
    refine ⟨q, by simp [q, hlen], ?_, ?_⟩
    · rw [Walk.isPath_def, Walk.support_concat, List.nodup_append]
      refine ⟨hpath.support_nodup, List.nodup_singleton _, ?_⟩
      intro x hx y hy
      simp only [List.mem_singleton] at hy
      subst hy
      exact fun heq => hnotmem (heq ▸ hx)
    · intro x hx
      rw [Walk.support_concat, List.mem_append, List.mem_singleton] at hx
      rcases hx with hx | rfl
      · obtain ⟨i, hi, rfl⟩ := hsupp x hx
        exact ⟨i, by omega, rfl⟩
      · exact ⟨⟨k + 1, hk⟩, le_rfl, rfl⟩

private lemma le_diam_of_induced_pathG {V : Type} [Fintype V] {G : SimpleGraph V}
    (hT : G.IsTree) {S : Finset V} {d : ℕ}
    (e : G.induce (S : Set V) ≃g pathG (d + 1)) :
    d ≤ G.diam := by
  classical
  obtain ⟨p, hlen, hpath, -⟩ := walk_of_pathG_iso e d (Nat.lt_succ_self d)
  let u := (e.symm ⟨0, Nat.zero_lt_succ d⟩).val
  let v := (e.symm ⟨d, Nat.lt_succ_self d⟩).val
  have : Nonempty V := ⟨u⟩
  obtain ⟨q, hqlen⟩ := hT.connected.exists_walk_length_eq_dist u v
  have : Subsingleton (G.Path u v) :=
    (SimpleGraph.isAcyclic_iff_subsingleton_path.mp hT.isAcyclic) u v
  have huniq : (⟨q.bypass, q.bypass_isPath⟩ : G.Path u v) = ⟨p, hpath⟩ :=
    Subsingleton.elim _ _
  have hle : p.length ≤ q.length := by
    have h1 : q.bypass.length ≤ q.length := q.length_bypass_le_length
    have h2 : q.bypass = p := congrArg Subtype.val huniq
    rw [h2] at h1
    exact h1
  have hdist : d ≤ G.dist u v := by omega
  have hediam : G.ediam ≠ ⊤ := G.connected_iff_ediam_ne_top.mp hT.connected
  exact hdist.trans (G.dist_le_diam hediam)

private lemma exists_induced_pathG_diam {V : Type} [Fintype V] [Nonempty V]
    {G : SimpleGraph V} (hT : G.IsTree) :
    ∃ S : Finset V, S.card = G.diam + 1 ∧ Nonempty (G.induce (S : Set V) ≃g pathG (G.diam + 1)) := by
  classical
  obtain ⟨u, v, huv⟩ := G.exists_dist_eq_diam
  obtain ⟨p0, hp0len⟩ := hT.connected.exists_walk_length_eq_dist u v
  let p : G.Walk u v := p0.bypass
  have hp_path : p.IsPath := p0.bypass_isPath
  have hp_dist : p.length = G.dist u v := by
    have hle : p.length ≤ p0.length := p0.length_bypass_le_length
    have hge : G.dist u v ≤ p.length := G.dist_le p
    omega
  have hp_len : p.length = G.diam := hp_dist.trans huv
  let f : Fin (G.diam + 1) → V := fun i => p.getVert i.val
  have hf_inj : Function.Injective f := by
    intro i j hij
    have hi : i.val ≤ p.length := by omega
    have hj : j.val ≤ p.length := by omega
    have hi' : i.val < p.support.length := by rw [Walk.length_support]; omega
    have hj' : j.val < p.support.length := by rw [Walk.length_support]; omega
    change p.getVert i.val = p.getVert j.val at hij
    rw [Walk.getVert_eq_support_getElem p hi, Walk.getVert_eq_support_getElem p hj] at hij
    exact Fin.ext ((List.Nodup.getElem_inj_iff hp_path.support_nodup).mp hij)
  let S : Finset V := Finset.univ.image f
  have hScard : S.card = G.diam + 1 := by
    rw [Finset.card_image_of_injective _ hf_inj, Finset.card_univ, Fintype.card_fin]
  have hf_mem : ∀ i : Fin (G.diam + 1), f i ∈ (S : Set V) := fun i =>
    Finset.mem_coe.mpr (Finset.mem_image_of_mem f (Finset.mem_univ i))
  let toFun : Fin (G.diam + 1) → (S : Set V) := fun i => ⟨f i, hf_mem i⟩
  have hbij : Function.Bijective toFun := by
    constructor
    · intro i j hij
      exact hf_inj (congrArg Subtype.val hij)
    · rintro ⟨x, hx⟩
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hx)
      exact ⟨i, rfl⟩
  let eqv : Fin (G.diam + 1) ≃ (S : Set V) := Equiv.ofBijective toFun hbij
  have hrel : ∀ i j : Fin (G.diam + 1), (pathG (G.diam + 1)).Adj i j ↔ G.Adj (f i) (f j) := by
    intro i j
    constructor
    · intro h
      rcases h with h | h
      · have hi : i.val < p.length := by omega
        have := p.adj_getVert_succ hi
        simpa [f, h] using this
      · have hj : j.val < p.length := by omega
        have := p.adj_getVert_succ hj
        exact (by simpa [f, h] using this : G.Adj (f j) (f i)).symm
    · intro hadj
      by_contra hnot
      have hnot1 : i.val + 1 ≠ j.val := fun h => hnot (Or.inl h)
      have hnot2 : j.val + 1 ≠ i.val := fun h => hnot (Or.inr h)
      have hne : i.val ≠ j.val := fun he => G.ne_of_adj hadj (congrArg f (Fin.ext he))
      have hlt_or : i.val + 1 < j.val ∨ j.val + 1 < i.val := by omega
      have shortcut : ∀ a b : Fin (G.diam + 1), a.val + 1 < b.val → G.Adj (f a) (f b) → False := by
        intro a b hab hAB
        have ha_le : a.val ≤ p.length := by omega
        have hb_le : b.val ≤ p.length := by omega
        have ha_lt : a.val < p.support.length := by rw [Walk.length_support]; omega
        have hb_lt : b.val < p.support.length := by rw [Walk.length_support]; omega
        let p1 := p.takeUntil (p.getVert a.val) (p.getVert_mem_support a.val)
        let p2 := p.dropUntil (p.getVert b.val) (p.getVert_mem_support b.val)
        have hidx_a : p.support.idxOf (p.getVert a.val) = a.val := by
          rw [Walk.getVert_eq_support_getElem p ha_le]
          exact hp_path.support_nodup.idxOf_getElem a.val ha_lt
        have hidx_b : p.support.idxOf (p.getVert b.val) = b.val := by
          rw [Walk.getVert_eq_support_getElem p hb_le]
          exact hp_path.support_nodup.idxOf_getElem b.val hb_lt
        have hp1_len : p1.length = a.val := by
          rw [Walk.length_takeUntil, hidx_a]
        have hp2_len : p2.length = p.length - b.val := by
          have hspec := p.take_spec (p.getVert_mem_support b.val)
          have hsum := congrArg Walk.length hspec
          rw [Walk.length_append, Walk.length_takeUntil, hidx_b] at hsum
          change b.val + p2.length = p.length at hsum
          omega
        let q : G.Walk u v := p1.append (Walk.cons hAB p2)
        have hqlen : q.length < p.length := by
          simp only [q, Walk.length_append, Walk.length_cons]
          omega
        have hdist_le : G.dist u v ≤ q.length := G.dist_le q
        omega
      rcases hlt_or with h | h
      · exact shortcut i j h hadj
      · exact shortcut j i h hadj.symm
  refine ⟨S, hScard, ⟨(RelIso.mk eqv (fun {i j} => (hrel i j).symm)).symm⟩⟩

private lemma diam_add_one_lt_card {V : Type} [Fintype V] {G : SimpleGraph V}
    (hT : G.IsTree) (hdeg3 : ∃ v : V, 3 ≤ (G.neighborSet v).ncard) :
    G.diam + 1 < Fintype.card V := by
  classical
  obtain ⟨v₀, hv₀⟩ := hdeg3
  have : Nonempty V := ⟨v₀⟩
  obtain ⟨S, hScard, ⟨e⟩⟩ := exists_induced_pathG_diam hT
  have hle : S.card ≤ Fintype.card V := Finset.card_le_univ S
  by_contra hnot
  have heq : S.card = Fintype.card V := by omega
  have hSuniv : S = Finset.univ := Finset.eq_univ_of_card S heq
  have hv₀S : v₀ ∈ (S : Set V) := by simp [hSuniv]
  let i0 : Fin (G.diam + 1) := e ⟨v₀, hv₀S⟩
  have hnb_le : (G.neighborSet v₀).ncard ≤ ((pathG (G.diam + 1)).neighborSet i0).ncard := by
    let g : G.neighborSet v₀ → (pathG (G.diam + 1)).neighborSet i0 := fun ⟨w, hw⟩ =>
      ⟨e ⟨w, by simp [hSuniv]⟩, by
        change (pathG (G.diam + 1)).Adj (e ⟨v₀, hv₀S⟩) (e ⟨w, by simp [hSuniv]⟩)
        exact e.map_rel_iff.mpr hw⟩
    have hginj : Function.Injective g := by
      intro ⟨w1, hw1⟩ ⟨w2, hw2⟩ h
      have h1 : e ⟨w1, by simp [hSuniv]⟩ = e ⟨w2, by simp [hSuniv]⟩ := congrArg Subtype.val h
      have hw : w1 = w2 := congrArg Subtype.val (e.injective h1)
      exact Subtype.ext hw
    have hcard := Fintype.card_le_of_injective g hginj
    simpa [Set.ncard_eq_toFinset_card'] using hcard
  have hle2 := pathG_neighborSet_ncard_le_two (G.diam + 1) i0
  omega

private lemma two_le_diam_of_deg3 {V : Type} [Fintype V] {G : SimpleGraph V}
    (hT : G.IsTree) (hdeg3 : ∃ v : V, 3 ≤ (G.neighborSet v).ncard) :
    2 ≤ G.diam := by
  obtain ⟨v₀, hv₀⟩ := hdeg3
  have : Nonempty V := ⟨v₀⟩
  have h1lt : 1 < (G.neighborSet v₀).ncard := by omega
  obtain ⟨a, ha, b, hb, hab⟩ := (Set.one_lt_ncard (Set.toFinite _)).mp h1lt
  have hnotadj : ¬ G.Adj a b := by
    intro hAB
    have ha' : G.Adj v₀ a := ha
    have hb' : G.Adj v₀ b := hb
    have ha_ne : a ≠ v₀ := (G.ne_of_adj ha').symm
    have hb_ne : b ≠ v₀ := (G.ne_of_adj hb').symm
    let p1 : G.Walk a b := Walk.cons hAB Walk.nil
    let p2 : G.Walk a b := Walk.cons ha'.symm (Walk.cons hb' Walk.nil)
    have hp1 : p1.IsPath := by
      rw [Walk.isPath_def]
      simp [p1, hab]
    have hp2 : p2.IsPath := by
      dsimp only [p2]
      rw [Walk.cons_isPath_iff, Walk.cons_isPath_iff]
      simp [ha_ne, hb_ne.symm, hab]
    have hsub : Subsingleton (G.Path a b) :=
      (SimpleGraph.isAcyclic_iff_subsingleton_path.mp hT.isAcyclic) a b
    have heq : (⟨p1, hp1⟩ : G.Path a b) = ⟨p2, hp2⟩ := Subsingleton.elim _ _
    have hlen : p1.length = p2.length := congrArg (fun x : G.Path a b => x.1.length) heq
    simp [p1, p2] at hlen
  have hdist_ne0 : G.dist a b ≠ 0 := by
    intro h0
    exact hab ((hT.connected.dist_eq_zero_iff).mp h0)
  have hdist_ne1 : G.dist a b ≠ 1 := by
    intro h1
    exact hnotadj (G.dist_eq_one_iff_adj.mp h1)
  have hdist_ge2 : 2 ≤ G.dist a b := by omega
  have hediam : G.ediam ≠ ⊤ := G.connected_iff_ediam_ne_top.mp hT.connected
  exact hdist_ge2.trans (G.dist_le_diam hediam)

end ReconTreeH4R1H1

theorem result : OMA.R_ReconstructionConjecture_reconstruction_conjecture_variants_tree_R1_H4_R1.H1 := by
  intro V W _ _ hV G H σ hTG hTH hdeg hnonpath hodd hkelly
  have hcardVW : Fintype.card V = Fintype.card W := Fintype.card_congr σ
  have hnonpathH : ∃ w : W, 3 ≤ (H.neighborSet w).ncard := by
    obtain ⟨v₀, hv₀⟩ := hnonpath
    exact ⟨σ v₀, by rw [← hdeg v₀]; exact hv₀⟩
  have hG2 : 2 ≤ G.diam := ReconTreeH4R1H1.two_le_diam_of_deg3 hTG hnonpath
  have hG3 : 3 ≤ G.diam := by
    obtain ⟨k, hk⟩ := hodd
    omega
  have hGlt : G.diam + 1 < Fintype.card V := ReconTreeH4R1H1.diam_add_one_lt_card hTG hnonpath
  have hHlt : H.diam + 1 < Fintype.card V := by
    rw [hcardVW]
    exact ReconTreeH4R1H1.diam_add_one_lt_card hTH hnonpathH
  have : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  have : Nonempty W := ⟨σ (Classical.arbitrary V)⟩
  have hGH : G.diam ≤ H.diam := by
    obtain ⟨S, -, hSiso⟩ := ReconTreeH4R1H1.exists_induced_pathG_diam hTG
    have hpos : 0 < {S : Finset V | Nonempty (G.induce (S : Set V) ≃g ReconTreeH4R1H1.pathG (G.diam + 1))}.ncard :=
      (Set.ncard_pos (Set.toFinite _)).mpr ⟨S, hSiso⟩
    rw [hkelly (Fin (G.diam + 1)) (ReconTreeH4R1H1.pathG (G.diam + 1)) (by simpa using hGlt)] at hpos
    obtain ⟨T, ⟨eT⟩⟩ := (Set.ncard_pos (Set.toFinite _)).mp hpos
    exact ReconTreeH4R1H1.le_diam_of_induced_pathG hTH eT
  have hHG : H.diam ≤ G.diam := by
    obtain ⟨T, -, hTiso⟩ := ReconTreeH4R1H1.exists_induced_pathG_diam hTH
    have hpos : 0 < {T : Finset W | Nonempty (H.induce (T : Set W) ≃g ReconTreeH4R1H1.pathG (H.diam + 1))}.ncard :=
      (Set.ncard_pos (Set.toFinite _)).mpr ⟨T, hTiso⟩
    rw [← hkelly (Fin (H.diam + 1)) (ReconTreeH4R1H1.pathG (H.diam + 1)) (by simpa using hHlt)] at hpos
    obtain ⟨S, ⟨eS⟩⟩ := (Set.ncard_pos (Set.toFinite _)).mp hpos
    exact ReconTreeH4R1H1.le_diam_of_induced_pathG hTG eS
  exact ⟨hG3, le_antisymm hGH hHG⟩

end KellyStep6

namespace KellyStep7
/- The central edge of an odd-diameter tree separates two rooted subtrees. -/
namespace TreeDiam
open SimpleGraph
lemma path_dist {V : Type} {G : SimpleGraph V} (hG : G.IsTree)
    {u v : V} {p : G.Walk u v} (hp : p.IsPath) : p.length = G.dist u v := by
  obtain ⟨q, hq⟩ := hG.connected.exists_walk_length_eq_dist u v
  have he := (hG.isAcyclic.subsingleton_path u v).elim (⟨p,hp⟩ : G.Path u v) ⟨q,q.isPath_of_length_eq_dist hq⟩
  exact (congrArg (fun w : G.Path u v => w.1.length) he).trans hq


lemma split_dist {V : Type} {G : SimpleGraph V} (ht : G.IsTree)
    {u v c : V} {p : G.Walk u v} (hp : p.IsPath) (hc : c ∈ p.support) :
    G.dist u v = G.dist u c + G.dist c v := by
  classical
  have h := congrArg Walk.length (p.take_spec hc)
  rw [Walk.length_append, path_dist ht (hp.takeUntil hc), path_dist ht (hp.dropUntil hc), path_dist ht hp] at h
  exact h.symm

lemma split_side {V : Type} {G : SimpleGraph V} (ht : G.IsTree)
    {a b c : V} {p : G.Walk a b} (hp : p.IsPath) (hc : c ∈ p.support) (x : V) :
    G.dist a x = G.dist a c + G.dist c x ∨ G.dist x b = G.dist x c + G.dist c b := by
  classical
  obtain ⟨q,hq,_⟩ := ht.existsUnique_path a x
  obtain ⟨s,hs,_⟩ := ht.existsUnique_path x b
  let w := q.append s
  have he := (ht.isAcyclic.subsingleton_path a b).elim (⟨p,hp⟩ : G.Path a b) w.toPath
  have hw : c ∈ w.support := w.support_toPath_subset_support (he ▸ hc)
  rcases (Walk.mem_support_append_iff q s).mp hw with h | h
  · exact Or.inl (split_dist ht hq h)
  · exact Or.inr (split_dist ht hs h)


lemma cross_edge {V : Type} {G : SimpleGraph V} (ht : G.IsTree) {c d : V}
    (hcd : G.Adj c d) {x y : V} (hx : G.dist x c < G.dist x d)
    (hy : G.dist y d < G.dist y c) :
    G.dist x y = G.dist x c + 1 + G.dist d y := by
  classical
  obtain ⟨p,hp,_⟩ := ht.existsUnique_path x c
  have hd : d ∉ p.support := by
    intro hd
    have := split_dist ht hp hd
    omega
  have hc := p.support_subset_support_concat hcd p.end_mem_support
  have hs := split_side ht (hp.concat hd hcd) hc y
  have step := ht.dist_eq_dist_add_one_of_adj y hcd
  have co := G.dist_comm (u := c) (v := y)
  have do' := G.dist_comm (u := d) (v := y)
  omega

lemma side_tree {V : Type} {G : SimpleGraph V} (ht : G.IsTree) {c d : V} (hcd : G.Adj c d) :
    (G.induce {x | G.dist x c < G.dist x d}).IsTree := by
  classical
  let S := {x | G.dist x c < G.dist x d}
  have hc : c ∈ S := by simp [S, dist_eq_one_iff_adj.2 hcd]
  refine ⟨(?_ : (G.induce S).Connected), ht.isAcyclic.induce _⟩
  apply (G.induce S).connected_iff_exists_forall_reachable.2
  refine ⟨⟨c,hc⟩, ?_⟩
  intro x
  obtain ⟨p,hp,_⟩ := ht.existsUnique_path (x : V) c
  have hsup (y : V) (hy : y ∈ p.support) : y ∈ S := by
    have hsplit := split_dist ht hp hy
    have htr := ht.connected.dist_triangle (u := (x : V)) (v := y) (w := d)
    have hx : G.dist x c < G.dist x d := x.property
    change G.dist y c < G.dist y d
    omega
  exact ⟨(p.induce S hsup).reverse⟩

theorem odd_edge {V : Type} [Fintype V] (G : SimpleGraph V) (ht : G.IsTree)
    (hthree : 3 ≤ G.diam) (ho : Odd G.diam) :
    ∃ c d : V, G.Adj c d ∧ G.center = {c,d} ∧
      (∀ x, G.dist x c ≠ G.dist x d) ∧
      (∀ x, G.dist x c < G.dist x d → G.dist x c ≤ (G.diam-1)/2) ∧
      (∀ x, G.dist x d < G.dist x c → G.dist x d ≤ (G.diam-1)/2) ∧
      (G.induce {x | G.dist x c < G.dist x d}).IsTree ∧
      (G.induce {x | G.dist x d < G.dist x c}).IsTree ∧
      ∀ x y, G.dist x c < G.dist x d → G.dist y d < G.dist y c →
        G.dist x y = G.dist x c + 1 + G.dist d y := by
  have := ht.connected.nonempty
  obtain ⟨r,hr⟩ := ho
  obtain ⟨a,b,hab⟩ := G.exists_dist_eq_diam
  obtain ⟨p,hp,_⟩ := ht.existsUnique_path a b
  have hl : p.length = 2*r+1 := (path_dist ht hp).trans (hab.trans hr)
  let c := p.getVert r
  let d := p.getVert (r+1)
  have hcd : G.Adj c d := p.adj_getVert_succ (by omega)
  have left (i : ℕ) (hi : i ≤ p.length) : G.dist a (p.getVert i) = i := by
    rw [← path_dist ht (hp.take i), Walk.take_length, min_eq_left hi]
  have right (i : ℕ) : G.dist (p.getVert i) b = p.length - i := by
    rw [← path_dist ht (hp.drop i), Walk.drop_length]
  have ac : G.dist a c = r := left _ (by omega)
  have ad : G.dist a d = r+1 := left _ (by omega)
  have cb : G.dist c b = r+1 := by change G.dist (p.getVert r) b = _; rw [right]; omega
  have db : G.dist d b = r := by change G.dist (p.getVert (r+1)) b = _; rw [right]; omega
  have bd : G.dist b d = r := G.dist_comm.trans db
  have bc : G.dist b c = r+1 := G.dist_comm.trans cb
  have al : G.dist a c < G.dist a d := by omega
  have br : G.dist b d < G.dist b c := by omega
  have bound (v w : V) : G.dist v w ≤ G.diam := G.dist_le_diam (G.connected_iff_ediam_ne_top.mp ht.connected)
  have lo (x : V) (hx : G.dist x c < G.dist x d) : G.dist x c ≤ r := by
    have := cross_edge ht hcd hx br
    have := bound x b
    omega
  have ro (x : V) (hx : G.dist x d < G.dist x c) : G.dist x d ≤ r := by
    have := cross_edge ht hcd al hx
    have := bound a x
    have := G.dist_comm (u := d) (v := x)
    omega
  have ne (x : V) : G.dist x c ≠ G.dist x d := ht.dist_ne_of_adj x hcd
  have eb (v w : V) : (G.dist v w : ℕ∞) ≤ G.eccent v :=
    (ht.connected v w).coe_dist_eq_edist.trans_le G.edist_le_eccent
  have high (v : V) : (↑(r+1) : ℕ∞) ≤ G.eccent v := by
    rcases (ne v).lt_or_gt with h | h
    · have := cross_edge ht hcd h br
      exact le_trans (by exact_mod_cast (show r+1 ≤ G.dist v b by omega)) (eb v b)
    · have := cross_edge ht hcd al h
      have := G.dist_comm (u := a) (v := v)
      exact le_trans (by exact_mod_cast (show r+1 ≤ G.dist v a by omega)) (eb v a)
  have both (v : V) : G.dist v c ≤ r+1 ∧ G.dist v d ≤ r+1 := by
    have step := ht.dist_eq_dist_add_one_of_adj v hcd
    rcases (ne v).lt_or_gt with h | h
    · have := lo v h
      omega
    · have := ro v h
      omega
  have cen (v : V) (h : ∀ x, G.dist x v ≤ r+1) : G.eccent v = ↑(r+1) := by
    apply le_antisymm _ (high v)
    apply (G.eccent_le_iff _ _).2
    intro x
    rw [G.edist_comm, ← (ht.connected x v).coe_dist_eq_edist]
    exact_mod_cast h x
  have ce := cen c (fun x => (both x).1)
  have de := cen d (fun x => (both x).2)
  have rad : G.radius = ↑(r+1) :=
    le_antisymm (ce ▸ G.radius_le_eccent (u := c)) (le_iInf high)
  have unique (x : V) (hc : x ≠ c) (hd : x ≠ d) : (↑(r+1) : ℕ∞) < G.eccent x := by
    rcases (ne x).lt_or_gt with h | h
    · have := ht.connected.pos_dist_of_ne hc
      have := cross_edge ht hcd h br
      exact lt_of_lt_of_le (by exact_mod_cast (show r+1 < G.dist x b by omega)) (eb x b)
    · have := ht.connected.pos_dist_of_ne hd
      have := cross_edge ht hcd al h
      have := G.dist_comm (u := a) (v := x)
      have := G.dist_comm (u := d) (v := x)
      exact lt_of_lt_of_le (by exact_mod_cast (show r+1 < G.dist x a by omega)) (eb x a)
  have eqcenter : G.center = {c,d} := by
    ext x
    rw [G.mem_center_iff, rad]
    change _ ↔ x = c ∨ x = d
    constructor
    · intro he
      by_contra! h
      exact (unique x h.1 h.2).ne' he
    · rintro (rfl | rfl)
      · exact ce
      · exact de
  have hr' : (G.diam-1)/2 = r := by omega
  exact ⟨c,d,hcd,eqcenter,ne,hr' ▸ lo,hr' ▸ ro,side_tree ht hcd,side_tree ht hcd.symm,
    fun _ _ hx hy => cross_edge ht hcd hx hy⟩
end TreeDiam

theorem result : OMA.R_ReconstructionConjecture_reconstruction_conjecture_variants_tree_R1_H4_R1.H2 := by
  intro V _ G ht hmin ho
  exact TreeDiam.odd_edge G ht hmin ho

end KellyStep7

namespace KellyStep8

section Tree3485H3

open SimpleGraph Classical

private structure BicenterData {V : Type} [Fintype V] (T : SimpleGraph V) (r : ℕ) where
  c₁ : V
  c₂ : V
  hr : 1 ≤ r
  hT : T.IsTree
  hdiam : T.diam = 2 * r + 1
  hadj : T.Adj c₁ c₂
  hne : ∀ x : V, T.dist x c₁ ≠ T.dist x c₂
  hle₁ : ∀ x : V, T.dist x c₁ < T.dist x c₂ → T.dist x c₁ ≤ r
  hle₂ : ∀ x : V, T.dist x c₂ < T.dist x c₁ → T.dist x c₂ ≤ r
  ht₁ : (T.induce {x : V | T.dist x c₁ < T.dist x c₂}).IsTree
  ht₂ : (T.induce {x : V | T.dist x c₂ < T.dist x c₁}).IsTree
  hdist : ∀ x y : V, T.dist x c₁ < T.dist x c₂ → T.dist y c₂ < T.dist y c₁ →
    T.dist x y = T.dist x c₁ + 1 + T.dist c₂ y
  hbig₁ : r + 2 ≤ {x : V | T.dist x c₁ < T.dist x c₂}.ncard
  hbig₂ : r + 2 ≤ {x : V | T.dist x c₂ < T.dist x c₁}.ncard

private def BicenterData.swap {V : Type} [Fintype V] {T : SimpleGraph V} {r : ℕ}
    (D : BicenterData T r) : BicenterData T r where
  c₁ := D.c₂
  c₂ := D.c₁
  hr := D.hr
  hT := D.hT
  hdiam := D.hdiam
  hadj := D.hadj.symm
  hne := fun x => (D.hne x).symm
  hle₁ := D.hle₂
  hle₂ := D.hle₁
  ht₁ := D.ht₂
  ht₂ := D.ht₁
  hdist := fun x y hx hy => by
    rw [SimpleGraph.dist_comm (u := x) (v := y), D.hdist y x hy hx,
      SimpleGraph.dist_comm (u := D.c₂) (v := x), SimpleGraph.dist_comm (u := y) (v := D.c₁)]
    ring
  hbig₁ := D.hbig₂
  hbig₂ := D.hbig₁

private def BicenterData.side₁ {V : Type} [Fintype V] {T : SimpleGraph V} {r : ℕ}
    (D : BicenterData T r) : Set V :=
  {x : V | T.dist x D.c₁ < T.dist x D.c₂}

private noncomputable def BicenterData.A₁ {V : Type} [Fintype V] {T : SimpleGraph V} {r : ℕ}
    (D : BicenterData T r) : Finset V :=
  Finset.univ.filter (fun x => T.dist x D.c₁ < T.dist x D.c₂)

private lemma mem_A₁_iff {V : Type} [Fintype V] {T : SimpleGraph V} {r : ℕ}
    (D : BicenterData T r) {x : V} : x ∈ D.A₁ ↔ x ∈ D.side₁ := by
  simp [BicenterData.A₁, BicenterData.side₁]

private lemma A₁_card_eq_ncard {V : Type} [Fintype V] {T : SimpleGraph V} {r : ℕ}
    (D : BicenterData T r) : D.A₁.card = D.side₁.ncard := by
  have h : D.side₁ = (D.A₁ : Set V) := by
    ext x
    exact (mem_A₁_iff D).symm
  rw [h, Set.ncard_coe_finset]

private lemma card_side₁_eq_A₁_card {V : Type} [Fintype V] {T : SimpleGraph V} {r : ℕ}
    (D : BicenterData T r) : Fintype.card D.side₁ = D.A₁.card :=
  Fintype.card_of_finset' D.A₁ (fun _ => mem_A₁_iff D)

private lemma mem_side₁_self {V : Type} [Fintype V] {T : SimpleGraph V} {r : ℕ}
    (D : BicenterData T r) : D.c₁ ∈ D.side₁ := by
  simp only [BicenterData.side₁, Set.mem_ofPred_eq, dist_self, dist_eq_one_iff_adj.mpr D.hadj]
  omega

private lemma mem_A₁_self {V : Type} [Fintype V] {T : SimpleGraph V} {r : ℕ}
    (D : BicenterData T r) : D.c₁ ∈ D.A₁ :=
  (mem_A₁_iff D).mpr (mem_side₁_self D)

private lemma disjoint_A₁_swap {V : Type} [Fintype V] {T : SimpleGraph V} {r : ℕ}
    (D : BicenterData T r) : Disjoint D.A₁ D.swap.A₁ := by
  rw [Finset.disjoint_left]
  intro x hx₁ hx₂
  rw [mem_A₁_iff] at hx₁ hx₂
  change T.dist x D.c₁ < T.dist x D.c₂ at hx₁
  change T.dist x D.c₂ < T.dist x D.c₁ at hx₂
  omega

private lemma union_A₁_swap {V : Type} [Fintype V] {T : SimpleGraph V} {r : ℕ}
    (D : BicenterData T r) : D.A₁ ∪ D.swap.A₁ = Finset.univ := by
  ext x
  simp only [Finset.mem_union, Finset.mem_univ, iff_true]
  rw [mem_A₁_iff, mem_A₁_iff]
  exact lt_or_gt_of_ne (D.hne x)

private lemma card_A₁_add_swap {V : Type} [Fintype V] {T : SimpleGraph V} {r : ℕ}
    (D : BicenterData T r) : D.A₁.card + D.swap.A₁.card = Fintype.card V := by
  rw [← Finset.card_union_of_disjoint (disjoint_A₁_swap D), union_A₁_swap, Finset.card_univ]

private noncomputable def BicenterData.T₁ {V : Type} [Fintype V] {T : SimpleGraph V} {r : ℕ}
    (D : BicenterData T r) : SimpleGraph D.side₁ :=
  T.induce D.side₁

private noncomputable def BicenterData.root₁ {V : Type} [Fintype V] {T : SimpleGraph V} {r : ℕ}
    (D : BicenterData T r) : D.side₁ :=
  ⟨D.c₁, mem_side₁_self D⟩

private lemma BicenterData.ht_side₁ {V : Type} [Fintype V] {T : SimpleGraph V} {r : ℕ}
    (D : BicenterData T r) : D.T₁.IsTree :=
  D.ht₁

private lemma mem_swap_side₁_of_not_mem {V : Type} [Fintype V] {T : SimpleGraph V} {r : ℕ}
    (D : BicenterData T r) {x : V} (hx : x ∉ D.side₁) : x ∈ D.swap.side₁ :=
  (lt_or_gt_of_ne (D.hne x)).resolve_left (by simpa [BicenterData.side₁] using hx)

private lemma induce_dist_eq {V : Type} {T : SimpleGraph V} (hT : T.IsTree) {S : Set V}
    (hS : (T.induce S).IsTree) (x y : S) : (T.induce S).dist x y = T.dist x.1 y.1 := by
  obtain ⟨p, hp_path, hp_len⟩ := hS.connected.exists_path_of_dist x y
  let f : T.induce S →g T := (SimpleGraph.Embedding.induce S).toHom
  have hf : Function.Injective f := Subtype.val_injective
  have hp'_path : (p.map f).IsPath :=
    (Walk.isPath_def _).mpr (by rw [Walk.support_map]; exact hp_path.support_nodup.map hf)
  obtain ⟨q, hq_path, hq_len⟩ := hT.connected.exists_path_of_dist x.1 y.1
  have huniq := (hT.existsUnique_path x.1 y.1).unique hp'_path hq_path
  rw [← hp_len, ← hq_len]
  exact (Walk.length_map f p).symm.trans (congrArg Walk.length huniq)

private lemma exists_far_vertex {V : Type} [Fintype V] {T : SimpleGraph V} {r : ℕ}
    (D : BicenterData T r) : ∃ a : D.side₁, D.T₁.dist a D.root₁ = r := by
  have hneV : Nonempty V := D.hT.connected.nonempty
  obtain ⟨x, y, hxy⟩ := T.exists_dist_eq_diam
  have hxy_r : T.dist x y = 2 * r + 1 := hxy.trans D.hdiam
  have htri : ∀ u v : V, u ∈ D.side₁ → v ∈ D.side₁ → T.dist u v ≤ 2 * r := by
    intro u v hu hv
    have h1 := D.hle₁ u hu
    have h2 := D.hle₁ v hv
    have h3 : T.dist u v ≤ T.dist u D.c₁ + T.dist D.c₁ v := D.hT.connected.dist_triangle
    rw [SimpleGraph.dist_comm (u := D.c₁) (v := v)] at h3
    omega
  have htri₂ : ∀ u v : V, u ∈ D.swap.side₁ → v ∈ D.swap.side₁ → T.dist u v ≤ 2 * r := by
    intro u v hu hv
    have h1 := D.hle₂ u hu
    have h2 := D.hle₂ v hv
    have h3 : T.dist u v ≤ T.dist u D.c₂ + T.dist D.c₂ v := D.hT.connected.dist_triangle
    rw [SimpleGraph.dist_comm (u := D.c₂) (v := v)] at h3
    omega
  rcases lt_or_gt_of_ne (D.hne x) with hx | hx <;> rcases lt_or_gt_of_ne (D.hne y) with hy | hy
  · exfalso; have := htri x y hx hy; omega
  · have hdeq := D.hdist x y hx hy
    have h1 := D.hle₁ x hx
    have h2 := D.hle₂ y hy
    rw [SimpleGraph.dist_comm (u := D.c₂) (v := y)] at hdeq
    refine ⟨⟨x, (show x ∈ D.side₁ from hx)⟩, ?_⟩
    dsimp [BicenterData.T₁]
    rw [induce_dist_eq D.hT D.ht_side₁]
    dsimp only [BicenterData.root₁]
    omega
  · have hdeq := D.hdist y x hy hx
    have h1 := D.hle₁ y hy
    have h2 := D.hle₂ x hx
    rw [SimpleGraph.dist_comm (u := x) (v := y)] at hxy_r
    rw [SimpleGraph.dist_comm (u := D.c₂) (v := x)] at hdeq
    refine ⟨⟨y, (show y ∈ D.side₁ from hy)⟩, ?_⟩
    dsimp [BicenterData.T₁]
    rw [induce_dist_eq D.hT D.ht_side₁]
    dsimp only [BicenterData.root₁]
    omega
  · exfalso; have := htri₂ x y hx hy; omega

private lemma eq_center_of_adj_across {V : Type} [Fintype V] {T : SimpleGraph V} {r : ℕ}
    (D : BicenterData T r) {x y : V} (hx : x ∈ D.side₁) (hy : y ∈ D.swap.side₁)
    (hadj : T.Adj x y) : x = D.c₁ ∧ y = D.c₂ := by
  have h1 : T.dist x y = 1 := dist_eq_one_iff_adj.mpr hadj
  have h2 := D.hdist x y hx hy
  have hx0 : T.dist x D.c₁ = 0 := by omega
  have hy0 : T.dist D.c₂ y = 0 := by omega
  exact ⟨(D.hT.connected.dist_eq_zero_iff).mp hx0,
    ((D.hT.connected.dist_eq_zero_iff).mp hy0).symm⟩

private def RootedIso {A B : Type} (R₁ : SimpleGraph A) (a : A) (R₂ : SimpleGraph B) (b : B) : Prop :=
  ∃ φ : R₁ ≃g R₂, φ a = b

private lemma RootedIso.refl {A : Type} (R : SimpleGraph A) (a : A) : RootedIso R a R a :=
  ⟨{ toFun := id, invFun := id, left_inv := fun _ => rfl, right_inv := fun _ => rfl,
     map_rel_iff' := fun {_ _} => Iff.rfl }, rfl⟩

private lemma RootedIso.symm {A B : Type} {R₁ : SimpleGraph A} {a : A} {R₂ : SimpleGraph B} {b : B}
    (h : RootedIso R₁ a R₂ b) : RootedIso R₂ b R₁ a := by
  obtain ⟨φ, hφ⟩ := h
  exact ⟨φ.symm, by rw [← hφ, φ.symm_apply_apply]⟩

private lemma RootedIso.trans {A B C : Type} {R₁ : SimpleGraph A} {a : A}
    {R₂ : SimpleGraph B} {b : B} {R₃ : SimpleGraph C} {c : C}
    (h1 : RootedIso R₁ a R₂ b) (h2 : RootedIso R₂ b R₃ c) : RootedIso R₁ a R₃ c := by
  obtain ⟨φ₁, hφ₁⟩ := h1
  obtain ⟨φ₂, hφ₂⟩ := h2
  exact ⟨φ₁.trans φ₂, by simp [hφ₁, hφ₂]⟩

private lemma RootedIso.card_eq {A B : Type} [Fintype A] [Fintype B]
    {R₁ : SimpleGraph A} {a : A} {R₂ : SimpleGraph B} {b : B}
    (h : RootedIso R₁ a R₂ b) : Fintype.card A = Fintype.card B := by
  obtain ⟨φ, _⟩ := h
  exact Fintype.card_congr φ.toEquiv

private def attachPath {A : Type} (R : SimpleGraph A) (root : A) (r : ℕ) :
    SimpleGraph (A ⊕ Fin (r + 1)) where
  Adj u v := match u, v with
    | .inl a, .inl b => R.Adj a b
    | .inr i, .inr j => (pathGraph (r + 1)).Adj i j
    | .inl a, .inr i => a = root ∧ i.1 = 0
    | .inr i, .inl a => a = root ∧ i.1 = 0
  symm := ⟨fun u v h => by
    rcases u with a | i <;> rcases v with b | j
    · exact (R.adj_comm a b).mp h
    · exact h
    · exact h
    · exact ((pathGraph (r + 1)).adj_comm i j).mp h⟩
  loopless := ⟨fun u h => by
    rcases u with a | i
    · exact R.ne_of_adj h rfl
    · exact (pathGraph (r + 1)).ne_of_adj h rfl⟩

private lemma exists_path_pathGraph_h3 (d : ℕ) :
    ∀ k (hk : k ≤ d), ∃ q : (pathGraph (d + 1)).Walk 0 ⟨k, Nat.lt_succ_of_le hk⟩,
      q.IsPath ∧ q.length = k ∧ ∀ x ∈ q.support, x.1 ≤ k
  | 0, _ => ⟨Walk.nil, Walk.IsPath.nil, rfl, fun x hx => by
      change x ∈ [(0 : Fin (d + 1))] at hx
      rcases List.mem_singleton.mp hx with rfl
      exact Nat.zero_le 0⟩
  | k + 1, hk => by
    obtain ⟨q, hq_path, hq_len, hq_le⟩ := exists_path_pathGraph_h3 d k (by omega)
    have hadj : (pathGraph (d + 1)).Adj ⟨k, by omega⟩ ⟨k + 1, Nat.lt_succ_of_le hk⟩ := by
      simp [pathGraph_adj]
    have hnot : (⟨k + 1, Nat.lt_succ_of_le hk⟩ : Fin (d + 1)) ∉ q.support := by
      intro hmem
      have h := hq_le _ hmem
      dsimp at h
      omega
    refine ⟨q.concat hadj, hq_path.concat hnot hadj, by rw [Walk.length_concat, hq_len], fun x hx => ?_⟩
    rw [Walk.support_concat, List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | rfl
    · have := hq_le x hx; omega
    · simp

private lemma attachPath_diam_walk {A : Type} (R : SimpleGraph A) (root a₀ : A) (r : ℕ)
    (hR : R.IsTree) (ha₀ : R.dist a₀ root = r) :
    ∃ q : (attachPath R root r).Walk (Sum.inl a₀) (Sum.inr ⟨r, Nat.lt_succ_self r⟩),
      q.IsPath ∧ q.length = 2 * r + 1 ∧
      q.getVert r = Sum.inl root ∧ q.getVert (r + 1) = Sum.inr 0 := by
  obtain ⟨p₁, hp₁_path, hp₁_len⟩ := hR.connected.exists_path_of_dist a₀ root
  obtain ⟨p₂, hp₂_path, hp₂_len, _⟩ := exists_path_pathGraph_h3 r r le_rfl
  let f₁ : R →g attachPath R root r := ⟨Sum.inl, fun h => by dsimp only [attachPath]; exact h⟩
  let f₂ : pathGraph (r + 1) →g attachPath R root r :=
    ⟨Sum.inr, fun h => by dsimp only [attachPath]; exact h⟩
  have hf₁ : Function.Injective f₁ := Sum.inl_injective
  have hf₂ : Function.Injective f₂ := Sum.inr_injective
  let q₁ := p₁.map f₁
  let q₂ := p₂.map f₂
  have hq₁_path : q₁.IsPath :=
    (Walk.isPath_def _).mpr (by rw [Walk.support_map]; exact hp₁_path.support_nodup.map hf₁)
  have hq₂_path : q₂.IsPath :=
    (Walk.isPath_def _).mpr (by rw [Walk.support_map]; exact hp₂_path.support_nodup.map hf₂)
  have hadj : (attachPath R root r).Adj (Sum.inl root) (Sum.inr (0 : Fin (r + 1))) := by
    simp [attachPath]
  have hdisj : ∀ x ∈ q₁.support, ∀ y ∈ q₂.support, x ≠ y := by
    intro x hx y hy
    rw [Walk.support_map, List.mem_map] at hx hy
    obtain ⟨_, _, rfl⟩ := hx
    obtain ⟨_, _, rfl⟩ := hy
    exact Sum.inl_ne_inr
  let q := q₁.append (Walk.cons hadj q₂)
  have hq_supp : q.support = q₁.support ++ q₂.support := by
    dsimp [q]
    rw [Walk.support_append, Walk.support_cons, List.tail_cons]
  have hq_path : q.IsPath := by
    rw [Walk.isPath_def, hq_supp]
    exact List.nodup_append.mpr ⟨hq₁_path.support_nodup, hq₂_path.support_nodup, hdisj⟩
  have hq₁_len : q₁.length = r := by dsimp [q₁]; rw [Walk.length_map, hp₁_len, ha₀]
  have hq₂_len : q₂.length = r := by dsimp [q₂]; rw [Walk.length_map, hp₂_len]
  have hq_len : q.length = 2 * r + 1 := by
    dsimp [q]
    rw [Walk.length_append, Walk.length_cons, hq₁_len, hq₂_len]
    omega
  have hgv₁ : q.getVert r = Sum.inl root := by
    dsimp [q]
    rw [Walk.getVert_append]
    split_ifs with h
    · exfalso; omega
    · have h0 : r - q₁.length = 0 := by omega
      rw [h0, Walk.getVert_zero]
      rfl
  have hgv₂ : q.getVert (r + 1) = Sum.inr 0 := by
    dsimp [q]
    rw [Walk.getVert_append]
    split_ifs with h
    · exfalso; omega
    · have hsub : r + 1 - q₁.length = 1 := by omega
      rw [hsub, Walk.getVert_cons_succ, Walk.getVert_zero]
  exact ⟨q, hq_path, hq_len, hgv₁, hgv₂⟩

private lemma bicenter_path_mid_of_len {V : Type} [Fintype V] {T : SimpleGraph V} {r : ℕ}
    (D : BicenterData T r) {x₀ y₀ : V} {q : T.Walk x₀ y₀} (hq_path : q.IsPath)
    (hq_len : q.length = 2 * r + 1) :
    (x₀ ∈ D.side₁ ∧ y₀ ∈ D.swap.side₁ ∧ q.getVert r = D.c₁ ∧ q.getVert (r + 1) = D.c₂) ∨
    (x₀ ∈ D.swap.side₁ ∧ y₀ ∈ D.side₁ ∧ q.getVert r = D.c₂ ∧ q.getVert (r + 1) = D.c₁) := by
  obtain ⟨r₀, hr₀_path, hr₀_len⟩ := D.hT.connected.exists_path_of_dist x₀ y₀
  have huniq_q := (D.hT.existsUnique_path x₀ y₀).unique hq_path hr₀_path
  have hdist_xy : T.dist x₀ y₀ = 2 * r + 1 := by rw [← hr₀_len, ← huniq_q, hq_len]
  have htri₁ : ∀ u v : V, u ∈ D.side₁ → v ∈ D.side₁ → T.dist u v ≤ 2 * r := by
    intro u v hu hv
    have h1 := D.hle₁ u hu
    have h2 := D.hle₁ v hv
    have h3 : T.dist u v ≤ T.dist u D.c₁ + T.dist D.c₁ v := D.hT.connected.dist_triangle
    rw [SimpleGraph.dist_comm (u := D.c₁) (v := v)] at h3
    omega
  have htri₂ : ∀ u v : V, u ∈ D.swap.side₁ → v ∈ D.swap.side₁ → T.dist u v ≤ 2 * r := by
    intro u v hu hv
    have h1 := D.hle₂ u hu
    have h2 := D.hle₂ v hv
    have h3 : T.dist u v ≤ T.dist u D.c₂ + T.dist D.c₂ v := D.hT.connected.dist_triangle
    rw [SimpleGraph.dist_comm (u := D.c₂) (v := v)] at h3
    omega
  have side_path : ∀ (Dc : BicenterData T r),
      ∀ u ∈ Dc.side₁, ∀ v ∈ Dc.swap.side₁, T.dist u v = 2 * r + 1 →
      ∀ w : T.Walk u v, w.IsPath → w.length = 2 * r + 1 →
      w.getVert r = Dc.c₁ ∧ w.getVert (r + 1) = Dc.c₂ := by
    intro Dc u hu v hv huv_d w hw_path hw_len
    obtain ⟨w₁, hw₁_path, hw₁_len⟩ := Dc.hT.connected.exists_path_of_dist u Dc.c₁
    obtain ⟨w₂, hw₂_path, hw₂_len⟩ := Dc.hT.connected.exists_path_of_dist Dc.c₂ v
    have hc₁_side : Dc.c₁ ∈ Dc.side₁ := mem_side₁_self Dc
    have hc₂_side : Dc.c₂ ∈ Dc.swap.side₁ := mem_side₁_self Dc.swap
    have h_no_c₂ : ∀ z ∈ w₁.support, z ∈ Dc.side₁ := by
      intro z hz
      obtain ⟨p_uz, p_zc, hp_uz, hp_zc, hw₁_app⟩ := hw₁_path.mem_support_iff_exists_append.mp hz
      by_contra hnot
      have hz₂ : z ∈ Dc.swap.side₁ := (lt_or_gt_of_ne (Dc.hne z)).resolve_left hnot
      have hdz : T.dist z Dc.c₁ = T.dist z Dc.c₂ + 1 := by
        have h_eq := Dc.hT.dist_eq_dist_add_one_of_adj z Dc.hadj
        change T.dist z Dc.c₂ < T.dist z Dc.c₁ at hz₂
        omega
      obtain ⟨p_zu, _⟩ := Dc.hT.connected.exists_path_of_dist z Dc.c₂
      have hlen_zc : T.dist z Dc.c₁ ≤ p_zc.length := dist_le p_zc
      have hlen_uz : T.dist u z ≤ p_uz.length := dist_le p_uz
      have hlen_sum : p_uz.length + p_zc.length = w₁.length := by rw [hw₁_app, Walk.length_append]
      have huc₂ : T.dist u Dc.c₂ = T.dist u Dc.c₁ + 1 := by
        have := Dc.hT.dist_eq_dist_add_one_of_adj u Dc.hadj
        change T.dist u Dc.c₁ < T.dist u Dc.c₂ at hu
        omega
      have htri_u : T.dist u Dc.c₂ ≤ T.dist u z + T.dist z Dc.c₂ := Dc.hT.connected.dist_triangle
      omega
    have h_no_c₁ : ∀ z ∈ w₂.support, z ∈ Dc.swap.side₁ := by
      intro z hz
      obtain ⟨p_cz, p_zv, hp_cz, hp_zv, hw₂_app⟩ := hw₂_path.mem_support_iff_exists_append.mp hz
      by_contra hnot
      have hz₁ : z ∈ Dc.side₁ := (lt_or_gt_of_ne (Dc.hne z)).resolve_right hnot
      have hdz : T.dist z Dc.c₂ = T.dist z Dc.c₁ + 1 := by
        have := Dc.hT.dist_eq_dist_add_one_of_adj z Dc.hadj
        change T.dist z Dc.c₁ < T.dist z Dc.c₂ at hz₁
        omega
      have hlen_cz : T.dist Dc.c₂ z ≤ p_cz.length := dist_le p_cz
      have hlen_zv : T.dist z v ≤ p_zv.length := dist_le p_zv
      have hlen_sum : p_cz.length + p_zv.length = w₂.length := by rw [hw₂_app, Walk.length_append]
      have hvc₁ : T.dist Dc.c₁ v = T.dist Dc.c₂ v + 1 := by
        have := Dc.hT.dist_eq_dist_add_one_of_adj v Dc.hadj
        change T.dist v Dc.c₂ < T.dist v Dc.c₁ at hv
        rw [SimpleGraph.dist_comm (u := Dc.c₁) (v := v), SimpleGraph.dist_comm (u := Dc.c₂) (v := v)]
        omega
      have htri_v : T.dist Dc.c₁ v ≤ T.dist Dc.c₁ z + T.dist z v := Dc.hT.connected.dist_triangle
      rw [SimpleGraph.dist_comm (u := Dc.c₁) (v := z)] at htri_v
      rw [SimpleGraph.dist_comm (u := Dc.c₂) (v := z)] at hlen_cz
      omega
    have hdisj : ∀ a ∈ w₁.support, ∀ b ∈ w₂.support, a ≠ b := by
      intro a ha b hb hab
      subst hab
      have h1 := h_no_c₂ a ha
      have h2 := h_no_c₁ a hb
      change T.dist a Dc.c₁ < T.dist a Dc.c₂ at h1
      change T.dist a Dc.c₂ < T.dist a Dc.c₁ at h2
      omega
    let w' : T.Walk u v := w₁.append (Walk.cons Dc.hadj w₂)
    have hw'_supp : w'.support = w₁.support ++ w₂.support := by
      dsimp [w']
      rw [Walk.support_append, Walk.support_cons, List.tail_cons]
    have hw'_path : w'.IsPath := by
      rw [Walk.isPath_def, hw'_supp]
      exact List.nodup_append.mpr ⟨hw₁_path.support_nodup, hw₂_path.support_nodup, hdisj⟩
    have hw_eq : w = w' := (Dc.hT.existsUnique_path u v).unique hw_path hw'_path
    have h1_le := Dc.hle₁ u hu
    have h2_le := Dc.hle₂ v hv
    have hdeq := Dc.hdist u v hu hv
    rw [SimpleGraph.dist_comm (u := Dc.c₂) (v := v)] at hdeq
    have hw₁_r : w₁.length = r := by omega
    rw [hw_eq]
    dsimp [w']
    constructor
    · rw [Walk.getVert_append]
      split_ifs with h
      · exfalso; omega
      · have h0 : r - w₁.length = 0 := by omega
        rw [h0, Walk.getVert_zero]
    · rw [Walk.getVert_append]
      split_ifs with h
      · exfalso; omega
      · have hsub : r + 1 - w₁.length = 1 := by omega
        rw [hsub, Walk.getVert_cons_succ, Walk.getVert_zero]
  rcases lt_or_gt_of_ne (D.hne x₀) with hx | hx <;> rcases lt_or_gt_of_ne (D.hne y₀) with hy | hy
  · exfalso; have := htri₁ x₀ y₀ hx hy; omega
  · have h := side_path D x₀ hx y₀ hy hdist_xy q hq_path hq_len
    exact Or.inl ⟨hx, hy, h.1, h.2⟩
  · have h := side_path D.swap x₀ hx y₀ hy hdist_xy q hq_path hq_len
    exact Or.inr ⟨hx, hy, h.1, h.2⟩
  · exfalso; have := htri₂ x₀ y₀ hx hy; omega

private lemma walk_mem_side_of_not_mem_other {V : Type} [Fintype V] {T : SimpleGraph V} {r : ℕ}
    (D : BicenterData T r) {x : V} (w : T.Walk x D.c₁) (hc₂ : D.c₂ ∉ w.support) :
    x ∈ D.side₁ := by
  by_contra hnot
  have hx₂ : x ∈ D.swap.side₁ := (lt_or_gt_of_ne (D.hne x)).resolve_left hnot
  obtain ⟨p, hp_path, hp_len⟩ := D.hT.connected.exists_path_of_dist x D.c₂
  have hc₁_not : D.c₁ ∉ p.support := by
    intro hc₁
    obtain ⟨q, hq_path, hq_len⟩ := D.hT.connected.exists_path_of_dist x D.c₁
    have heq := D.hT.isAcyclic.path_concat hq_path hp_path D.hadj hc₁
    have hlen_eq : p.length = q.length + 1 := by rw [heq, Walk.length_concat]
    change T.dist x D.c₂ < T.dist x D.c₁ at hx₂
    omega
  have hp_cat : (p.concat D.hadj.symm).IsPath := hp_path.concat hc₁_not D.hadj.symm
  have hw_path : w.toPath.val.IsPath := w.toPath.isPath
  have huniq := (D.hT.existsUnique_path x D.c₁).unique hw_path hp_cat
  apply hc₂
  apply Walk.support_toPath_subset_support
  rw [huniq, Walk.support_concat, List.mem_append, List.mem_singleton]
  left
  exact p.end_mem_support

private noncomputable def rootedCopies {V : Type} [Fintype V] {T : SimpleGraph V} {r : ℕ}
    (D : BicenterData T r) {A : Type} [Fintype A] (R : SimpleGraph A) (root : A) :
    Finset (Finset V) :=
  Finset.univ.filter fun S₁ : Finset V =>
    S₁ ⊆ D.A₁ ∧ D.c₁ ∈ S₁ ∧ ∃ φ : R ≃g T.induce (S₁ : Set V), (φ root).1 = D.c₁

private lemma mem_rootedCopies_iff {V : Type} [Fintype V] {T : SimpleGraph V} {r : ℕ}
    (D : BicenterData T r) {A : Type} [Fintype A] (R : SimpleGraph A) (root : A) (S₁ : Finset V) :
    S₁ ∈ rootedCopies D R root ↔
      S₁ ⊆ D.A₁ ∧ D.c₁ ∈ S₁ ∧ ∃ φ : R ≃g T.induce (S₁ : Set V), (φ root).1 = D.c₁ := by
  simp [rootedCopies]

private lemma attachPath_decomp {V : Type} [Fintype V] {T : SimpleGraph V} {r : ℕ}
    (D : BicenterData T r) {A : Type} [Fintype A] {R : SimpleGraph A} {root : A}
    (hR : R.IsTree) (hR_far : ∃ a₀ : A, R.dist a₀ root = r)
    (_hR_card : r + 2 ≤ Fintype.card A) (S : Finset V) :
    Nonempty (T.induce (S : Set V) ≃g attachPath R root r) ↔
      (S ∩ D.A₁ ∈ rootedCopies D R root ∧ S ∩ D.swap.A₁ ∈ rootedCopies D.swap (pathGraph (r + 1)) 0) ∨
      (S ∩ D.swap.A₁ ∈ rootedCopies D.swap R root ∧ S ∩ D.A₁ ∈ rootedCopies D (pathGraph (r + 1)) 0) := by
  constructor
  · rintro ⟨ψ⟩
    let φ : attachPath R root r ≃g T.induce (S : Set V) := ψ.symm
    obtain ⟨a₀, ha₀⟩ := hR_far
    obtain ⟨q_att, hq_att_path, hq_att_len, hgv₁, hgv₂⟩ := attachPath_diam_walk R root a₀ r hR ha₀
    let hom : attachPath R root r →g T := (SimpleGraph.Embedding.induce (S : Set V)).toHom.comp φ.toHom
    have hinj : Function.Injective hom := Subtype.val_injective.comp φ.injective
    let q := q_att.map hom
    have hq_path : q.IsPath :=
      (Walk.isPath_def _).mpr (by rw [Walk.support_map]; exact hq_att_path.support_nodup.map hinj)
    have hq_len : q.length = 2 * r + 1 := (Walk.length_map hom q_att).trans hq_att_len
    have hq_gv₁ : q.getVert r = (φ (Sum.inl root)).1 := by
      dsimp [q]
      rw [Walk.getVert_map, hgv₁]
      rfl
    have hq_gv₂ : q.getVert (r + 1) = (φ (Sum.inr 0)).1 := by
      dsimp [q]
      rw [Walk.getVert_map, hgv₂]
      rfl
    have hmid := bicenter_path_mid_of_len D hq_path hq_len
    have extract_pair : ∀ (Dc : BicenterData T r)
        (hc₁ : (φ (Sum.inl root)).1 = Dc.c₁) (hc₂ : (φ (Sum.inr 0)).1 = Dc.c₂),
        S ∩ Dc.A₁ ∈ rootedCopies Dc R root ∧
        S ∩ Dc.swap.A₁ ∈ rootedCopies Dc.swap (pathGraph (r + 1)) 0 := by
      intro Dc hc₁ hc₂
      have hin_side₁ : ∀ a : A, (φ (Sum.inl a)).1 ∈ Dc.side₁ := by
        intro a
        obtain ⟨pa, _⟩ := hR.connected.exists_path_of_dist a root
        let fR : R →g attachPath R root r := ⟨Sum.inl, fun h => by dsimp only [attachPath]; exact h⟩
        let w0 := (pa.map fR).map hom
        have hc₁' : hom (fR root) = Dc.c₁ := hc₁
        let w : T.Walk (hom (fR a)) Dc.c₁ := w0.copy rfl hc₁'
        change hom (fR a) ∈ Dc.side₁
        refine walk_mem_side_of_not_mem_other Dc w ?_
        intro hmem
        dsimp only [w, w0] at hmem
        rw [Walk.support_copy, Walk.support_map, Walk.support_map] at hmem
        simp only [List.mem_map] at hmem
        obtain ⟨_, ⟨u, _, rfl⟩, hu⟩ := hmem
        have h_eq : φ (Sum.inl u) = φ (Sum.inr 0) := Subtype.ext (hu.trans hc₂.symm)
        exact Sum.inl_ne_inr (φ.injective h_eq)
      have hin_side₂ : ∀ i : Fin (r + 1), (φ (Sum.inr i)).1 ∈ Dc.swap.side₁ := by
        intro i
        obtain ⟨pi⟩ := pathGraph_preconnected (r + 1) i 0
        let fP : pathGraph (r + 1) →g attachPath R root r :=
          ⟨Sum.inr, fun h => by dsimp only [attachPath]; exact h⟩
        let w0 := (pi.map fP).map hom
        have hc₂' : hom (fP 0) = Dc.swap.c₁ := hc₂
        let w : T.Walk (hom (fP i)) Dc.swap.c₁ := w0.copy rfl hc₂'
        change hom (fP i) ∈ Dc.swap.side₁
        refine walk_mem_side_of_not_mem_other Dc.swap w ?_
        intro hmem
        dsimp only [w, w0] at hmem
        rw [Walk.support_copy, Walk.support_map, Walk.support_map] at hmem
        simp only [List.mem_map] at hmem
        obtain ⟨_, ⟨j, _, rfl⟩, hj⟩ := hmem
        change (φ (Sum.inr j)).1 = Dc.c₁ at hj
        have h_eq : φ (Sum.inr j) = φ (Sum.inl root) := Subtype.ext (hj.trans hc₁.symm)
        exact Sum.inr_ne_inl (φ.injective h_eq)
      have hSA₁ : S ∩ Dc.A₁ = (Finset.univ : Finset A).image (fun a => (φ (Sum.inl a)).1) := by
        ext x
        simp only [Finset.mem_inter, Finset.mem_image, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨hxS, hxA⟩
          obtain ⟨u, hu⟩ := φ.surjective ⟨x, hxS⟩
          rcases u with a | i
          · exact ⟨a, congrArg Subtype.val hu⟩
          · exfalso
            have hx_eq : (φ (Sum.inr i)).1 = x := congrArg Subtype.val hu
            have hx2 : x ∈ Dc.swap.side₁ := hx_eq ▸ hin_side₂ i
            have hx1 : x ∈ Dc.side₁ := (mem_A₁_iff Dc).mp hxA
            change T.dist x Dc.c₁ < T.dist x Dc.c₂ at hx1
            change T.dist x Dc.c₂ < T.dist x Dc.c₁ at hx2
            omega
        · rintro ⟨a, rfl⟩
          exact ⟨(φ (Sum.inl a)).2, (mem_A₁_iff Dc).mpr (hin_side₁ a)⟩
      have hSA₂ : S ∩ Dc.swap.A₁ =
          (Finset.univ : Finset (Fin (r + 1))).image (fun i => (φ (Sum.inr i)).1) := by
        ext x
        simp only [Finset.mem_inter, Finset.mem_image, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨hxS, hxA⟩
          obtain ⟨u, hu⟩ := φ.surjective ⟨x, hxS⟩
          rcases u with a | i
          · exfalso
            have hx_eq : (φ (Sum.inl a)).1 = x := congrArg Subtype.val hu
            have hx1 : x ∈ Dc.side₁ := hx_eq ▸ hin_side₁ a
            have hx2 : x ∈ Dc.swap.side₁ := (mem_A₁_iff Dc.swap).mp hxA
            change T.dist x Dc.c₁ < T.dist x Dc.c₂ at hx1
            change T.dist x Dc.c₂ < T.dist x Dc.c₁ at hx2
            omega
          · exact ⟨i, congrArg Subtype.val hu⟩
        · rintro ⟨i, rfl⟩
          exact ⟨(φ (Sum.inr i)).2, (mem_A₁_iff Dc.swap).mpr (hin_side₂ i)⟩
      constructor
      · rw [mem_rootedCopies_iff]
        refine ⟨Finset.inter_subset_right, ?_, ?_⟩
        · rw [hSA₁]
          exact Finset.mem_image.mpr ⟨root, Finset.mem_univ _, hc₁⟩
        · let φ₁ : R ≃g T.induce ((S ∩ Dc.A₁ : Finset V) : Set V) :=
            { toFun := fun a => ⟨(φ (Sum.inl a)).1, by
                rw [Finset.mem_coe, hSA₁]
                exact Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩⟩
              invFun := fun x => by
                have hx : x.1 ∈ (Finset.univ : Finset A).image (fun a => (φ (Sum.inl a)).1) := by
                  rw [← hSA₁]; exact Finset.mem_coe.mp x.2
                exact (Finset.mem_image.mp hx).choose
              left_inv := fun a => by
                dsimp only
                have hx : (φ (Sum.inl a)).1 ∈
                    (Finset.univ : Finset A).image (fun a' => (φ (Sum.inl a')).1) :=
                  Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩
                have hspec := (Finset.mem_image.mp hx).choose_spec.2
                exact Sum.inl_injective (φ.injective (Subtype.ext hspec))
              right_inv := fun x => by
                ext
                dsimp only
                have hx : x.1 ∈ (Finset.univ : Finset A).image (fun a => (φ (Sum.inl a)).1) := by
                  rw [← hSA₁]; exact Finset.mem_coe.mp x.2
                exact (Finset.mem_image.mp hx).choose_spec.2
              map_rel_iff' := fun {a b} => by
                change T.Adj (φ (Sum.inl a)).1 (φ (Sum.inl b)).1 ↔ R.Adj a b
                simpa [attachPath, SimpleGraph.induce_adj] using
                  (φ.map_rel_iff (a := Sum.inl a) (b := Sum.inl b)) }
          exact ⟨φ₁, hc₁⟩
      · rw [mem_rootedCopies_iff]
        refine ⟨Finset.inter_subset_right, ?_, ?_⟩
        · rw [hSA₂]
          exact Finset.mem_image.mpr ⟨0, Finset.mem_univ _, hc₂⟩
        · let φ₂ : pathGraph (r + 1) ≃g T.induce ((S ∩ Dc.swap.A₁ : Finset V) : Set V) :=
            { toFun := fun i => ⟨(φ (Sum.inr i)).1, by
                rw [Finset.mem_coe, hSA₂]
                exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩
              invFun := fun x => by
                have hx : x.1 ∈ (Finset.univ : Finset (Fin (r + 1))).image
                    (fun i => (φ (Sum.inr i)).1) := by
                  rw [← hSA₂]; exact Finset.mem_coe.mp x.2
                exact (Finset.mem_image.mp hx).choose
              left_inv := fun i => by
                dsimp only
                have hx : (φ (Sum.inr i)).1 ∈ (Finset.univ : Finset (Fin (r + 1))).image
                    (fun i' => (φ (Sum.inr i')).1) :=
                  Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
                have hspec := (Finset.mem_image.mp hx).choose_spec.2
                exact Sum.inr_injective (φ.injective (Subtype.ext hspec))
              right_inv := fun x => by
                ext
                dsimp only
                have hx : x.1 ∈ (Finset.univ : Finset (Fin (r + 1))).image
                    (fun i => (φ (Sum.inr i)).1) := by
                  rw [← hSA₂]; exact Finset.mem_coe.mp x.2
                exact (Finset.mem_image.mp hx).choose_spec.2
              map_rel_iff' := fun {i j} => by
                change T.Adj (φ (Sum.inr i)).1 (φ (Sum.inr j)).1 ↔ (pathGraph (r + 1)).Adj i j
                simpa [attachPath, SimpleGraph.induce_adj] using
                  (φ.map_rel_iff (a := Sum.inr i) (b := Sum.inr j)) }
          exact ⟨φ₂, hc₂⟩
    rcases hmid with ⟨_, _, h1, h2⟩ | ⟨_, _, h1, h2⟩
    · exact Or.inl (extract_pair D (hq_gv₁ ▸ h1) (hq_gv₂ ▸ h2))
    · exact Or.inr (extract_pair D.swap (hq_gv₁ ▸ h1) (hq_gv₂ ▸ h2))
  · have build_iso : ∀ (Dc : BicenterData T r),
        S ∩ Dc.A₁ ∈ rootedCopies Dc R root →
        S ∩ Dc.swap.A₁ ∈ rootedCopies Dc.swap (pathGraph (r + 1)) 0 →
        Nonempty (T.induce (S : Set V) ≃g attachPath R root r) := by
      intro Dc h1 h2
      rw [mem_rootedCopies_iff] at h1 h2
      obtain ⟨hsub₁, hc₁_in, ⟨φ₁, hφ₁⟩⟩ := h1
      obtain ⟨hsub₂, hc₂_in, ⟨φ₂, hφ₂⟩⟩ := h2
      have hS_eq : (S ∩ Dc.A₁) ∪ (S ∩ Dc.swap.A₁) = S := by
        rw [← Finset.inter_union_distrib_left, union_A₁_swap Dc, Finset.inter_univ]
      have hdisj_SA : Disjoint (S ∩ Dc.A₁) (S ∩ Dc.swap.A₁) :=
        Disjoint.mono Finset.inter_subset_right Finset.inter_subset_right (disjoint_A₁_swap Dc)
      let φ : attachPath R root r ≃g T.induce (S : Set V) :=
        { toFun := Sum.elim
            (fun a => ⟨(φ₁ a).1, Finset.mem_coe.mpr (Finset.inter_subset_left (Finset.mem_coe.mp (φ₁ a).2))⟩)
            (fun i => ⟨(φ₂ i).1, Finset.mem_coe.mpr (Finset.inter_subset_left (Finset.mem_coe.mp (φ₂ i).2))⟩)
          invFun := fun x =>
            if hx : x.1 ∈ S ∩ Dc.A₁ then
              Sum.inl (φ₁.symm ⟨x.1, Finset.mem_coe.mpr hx⟩)
            else
              Sum.inr (φ₂.symm ⟨x.1, Finset.mem_coe.mpr
                ((Finset.mem_union.mp ((Finset.ext_iff.mp hS_eq x.1).mpr (Finset.mem_coe.mp x.2))).resolve_left hx)⟩)
          left_inv := fun u => by
            rcases u with a | i
            · dsimp only [Sum.elim_inl]
              have ha : (φ₁ a).1 ∈ S ∩ Dc.A₁ := Finset.mem_coe.mp (φ₁ a).2
              rw [dif_pos ha]
              simp
            · dsimp only [Sum.elim_inr]
              have hi : (φ₂ i).1 ∈ S ∩ Dc.swap.A₁ := Finset.mem_coe.mp (φ₂ i).2
              have hnot : (φ₂ i).1 ∉ S ∩ Dc.A₁ := Finset.disjoint_right.mp hdisj_SA hi
              rw [dif_neg hnot]
              simp
          right_inv := fun x => by
            ext
            dsimp only
            by_cases hx : x.1 ∈ S ∩ Dc.A₁
            · rw [dif_pos hx]
              dsimp only [Sum.elim_inl]
              exact congrArg Subtype.val (φ₁.apply_symm_apply ⟨x.1, Finset.mem_coe.mpr hx⟩)
            · rw [dif_neg hx]
              dsimp only [Sum.elim_inr]
              exact congrArg Subtype.val (φ₂.apply_symm_apply _)
          map_rel_iff' := fun {u v} => by
            rcases u with a | i <;> rcases v with b | j <;> dsimp only [attachPath]
            · change T.Adj (φ₁ a).1 (φ₁ b).1 ↔ R.Adj a b
              simpa [SimpleGraph.induce_adj] using (φ₁.map_rel_iff (a := a) (b := b))
            · change T.Adj (φ₁ a).1 (φ₂ j).1 ↔ a = root ∧ j.1 = 0
              have ha_side : (φ₁ a).1 ∈ Dc.side₁ := (mem_A₁_iff Dc).mp (hsub₁ (Finset.mem_coe.mp (φ₁ a).2))
              have hj_side : (φ₂ j).1 ∈ Dc.swap.side₁ := (mem_A₁_iff Dc.swap).mp (hsub₂ (Finset.mem_coe.mp (φ₂ j).2))
              constructor
              · intro hadj
                obtain ⟨hxa, hyj⟩ := eq_center_of_adj_across Dc ha_side hj_side hadj
                have ha_eq : a = root := φ₁.injective (Subtype.ext (hxa.trans hφ₁.symm))
                have hj_eq : j = 0 := φ₂.injective (Subtype.ext (hyj.trans hφ₂.symm))
                exact ⟨ha_eq, by simp [hj_eq]⟩
              · rintro ⟨rfl, hj0⟩
                have hj_eq : j = 0 := Fin.ext hj0
                subst hj_eq
                rw [hφ₁, hφ₂]
                exact Dc.hadj
            · change T.Adj (φ₂ i).1 (φ₁ b).1 ↔ b = root ∧ i.1 = 0
              have hb_side : (φ₁ b).1 ∈ Dc.side₁ := (mem_A₁_iff Dc).mp (hsub₁ (Finset.mem_coe.mp (φ₁ b).2))
              have hi_side : (φ₂ i).1 ∈ Dc.swap.side₁ := (mem_A₁_iff Dc.swap).mp (hsub₂ (Finset.mem_coe.mp (φ₂ i).2))
              rw [adj_comm]
              constructor
              · intro hadj
                obtain ⟨hxb, hyi⟩ := eq_center_of_adj_across Dc hb_side hi_side hadj
                have hb_eq : b = root := φ₁.injective (Subtype.ext (hxb.trans hφ₁.symm))
                have hi_eq : i = 0 := φ₂.injective (Subtype.ext (hyi.trans hφ₂.symm))
                exact ⟨hb_eq, by simp [hi_eq]⟩
              · rintro ⟨rfl, hi0⟩
                have hi_eq : i = 0 := Fin.ext hi0
                subst hi_eq
                rw [hφ₁, hφ₂]
                exact Dc.hadj
            · change T.Adj (φ₂ i).1 (φ₂ j).1 ↔ (pathGraph (r + 1)).Adj i j
              simpa [SimpleGraph.induce_adj] using (φ₂.map_rel_iff (a := i) (b := j)) }
      exact ⟨φ.symm⟩
    rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact build_iso D h1 h2
    · exact build_iso D.swap h1 h2

private lemma ncard_attachPath_eq {V : Type} [Fintype V] {T : SimpleGraph V} {r : ℕ}
    (D : BicenterData T r) {A : Type} [Fintype A] {R : SimpleGraph A} {root : A}
    (hR : R.IsTree) (hR_far : ∃ a₀ : A, R.dist a₀ root = r)
    (hR_card : r + 2 ≤ Fintype.card A) :
    {S : Finset V | Nonempty (T.induce (S : Set V) ≃g attachPath R root r)}.ncard =
      (rootedCopies D R root).card * (rootedCopies D.swap (pathGraph (r + 1)) 0).card +
      (rootedCopies D.swap R root).card * (rootedCopies D (pathGraph (r + 1)) 0).card := by
  let F_all : Finset (Finset V) :=
    Finset.univ.filter fun S => Nonempty (T.induce (S : Set V) ≃g attachPath R root r)
  have hncard : {S : Finset V | Nonempty (T.induce (S : Set V) ≃g attachPath R root r)}.ncard =
      F_all.card := by
    have hset : {S : Finset V | Nonempty (T.induce (S : Set V) ≃g attachPath R root r)} =
        (F_all : Set (Finset V)) := by
      ext S; simp [F_all]
    rw [hset, Set.ncard_coe_finset]
  rw [hncard]
  let F₁ : Finset (Finset V) :=
    (rootedCopies D R root ×ˢ rootedCopies D.swap (pathGraph (r + 1)) 0).image (fun p => p.1 ∪ p.2)
  let F₂ : Finset (Finset V) :=
    (rootedCopies D.swap R root ×ˢ rootedCopies D (pathGraph (r + 1)) 0).image (fun p => p.1 ∪ p.2)
  have hF_eq : F_all = F₁ ∪ F₂ := by
    ext S
    simp only [F_all, F₁, F₂, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
      Finset.mem_image, Finset.mem_product, Prod.exists]
    rw [attachPath_decomp D hR hR_far hR_card]
    constructor
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · left
        refine ⟨S ∩ D.A₁, S ∩ D.swap.A₁, ⟨h1, h2⟩, ?_⟩
        rw [← Finset.inter_union_distrib_left, union_A₁_swap D, Finset.inter_univ]
      · right
        refine ⟨S ∩ D.swap.A₁, S ∩ D.A₁, ⟨h1, h2⟩, ?_⟩
        rw [← Finset.inter_union_distrib_left, Finset.union_comm D.swap.A₁ D.A₁,
          union_A₁_swap D, Finset.inter_univ]
    · rintro (⟨S₁, S₂, ⟨h1, h2⟩, rfl⟩ | ⟨S₁, S₂, ⟨h1, h2⟩, rfl⟩)
      · left
        have hs₁ : S₁ ⊆ D.A₁ := ((mem_rootedCopies_iff D R root S₁).mp h1).1
        have hs₂ : S₂ ⊆ D.swap.A₁ := ((mem_rootedCopies_iff D.swap (pathGraph (r + 1)) 0 S₂).mp h2).1
        have hdisj₁ : Disjoint S₂ D.A₁ := Disjoint.mono_left hs₂ (disjoint_A₁_swap D).symm
        have hdisj₂ : Disjoint S₁ D.swap.A₁ := Disjoint.mono_left hs₁ (disjoint_A₁_swap D)
        rw [Finset.union_inter_distrib_right, Finset.inter_eq_left.mpr hs₁,
          Finset.disjoint_iff_inter_eq_empty.mp hdisj₁, Finset.union_empty]
        rw [Finset.union_inter_distrib_right, Finset.disjoint_iff_inter_eq_empty.mp hdisj₂,
          Finset.empty_union, Finset.inter_eq_left.mpr hs₂]
        exact ⟨h1, h2⟩
      · right
        have hs₁ : S₁ ⊆ D.swap.A₁ := ((mem_rootedCopies_iff D.swap R root S₁).mp h1).1
        have hs₂ : S₂ ⊆ D.A₁ := ((mem_rootedCopies_iff D (pathGraph (r + 1)) 0 S₂).mp h2).1
        have hdisj₁ : Disjoint S₂ D.swap.A₁ := Disjoint.mono_left hs₂ (disjoint_A₁_swap D)
        have hdisj₂ : Disjoint S₁ D.A₁ := Disjoint.mono_left hs₁ (disjoint_A₁_swap D).symm
        rw [Finset.union_inter_distrib_right, Finset.inter_eq_left.mpr hs₁,
          Finset.disjoint_iff_inter_eq_empty.mp hdisj₁, Finset.union_empty]
        rw [Finset.union_inter_distrib_right, Finset.disjoint_iff_inter_eq_empty.mp hdisj₂,
          Finset.empty_union, Finset.inter_eq_left.mpr hs₂]
        exact ⟨h1, h2⟩
  have hF_disj : Disjoint F₁ F₂ := by
    rw [Finset.disjoint_left]
    intro S hS₁ hS₂
    rw [Finset.mem_image] at hS₁ hS₂
    obtain ⟨⟨S₁, S₂⟩, hmem₁, rfl⟩ := hS₁
    obtain ⟨⟨T₁, T₂⟩, hmem₂, heq⟩ := hS₂
    rw [Finset.mem_product, mem_rootedCopies_iff, mem_rootedCopies_iff] at hmem₁ hmem₂
    have hs₁ : S₁ ⊆ D.A₁ := hmem₁.1.1
    have hs₂ : S₂ ⊆ D.swap.A₁ := hmem₁.2.1
    have ht₁ : T₁ ⊆ D.swap.A₁ := hmem₂.1.1
    have ht₂ : T₂ ⊆ D.A₁ := hmem₂.2.1
    have hdisj_s₂ : Disjoint S₂ D.A₁ := Disjoint.mono_left hs₂ (disjoint_A₁_swap D).symm
    have hdisj_t₁ : Disjoint T₁ D.A₁ := Disjoint.mono_left ht₁ (disjoint_A₁_swap D).symm
    have h_inter : S₁ = T₂ := by
      have h := congrArg (· ∩ D.A₁) heq
      simpa [Finset.union_inter_distrib_right, Finset.inter_eq_left.mpr hs₁,
        Finset.inter_eq_left.mpr ht₂, Finset.disjoint_iff_inter_eq_empty.mp hdisj_s₂,
        Finset.disjoint_iff_inter_eq_empty.mp hdisj_t₁] using h.symm
    obtain ⟨φ₁, _⟩ := hmem₁.1.2.2
    obtain ⟨φ₂, _⟩ := hmem₂.2.2.2
    have hc₁ : S₁.card = Fintype.card A := by
      simpa using (Fintype.card_congr φ₁.toEquiv).symm
    have hc₂ : T₂.card = r + 1 := by
      simpa using (Fintype.card_congr φ₂.toEquiv).symm
    have h_card_inter : S₁.card = T₂.card := congrArg Finset.card h_inter
    omega
  have hinj_pair : ∀ (Dc₁ Dc₂ : BicenterData T r), Disjoint Dc₁.A₁ Dc₂.A₁ →
      ∀ {B : Type} [Fintype B] (RB : SimpleGraph B) (rB : B),
      Set.InjOn (fun p : Finset V × Finset V => p.1 ∪ p.2)
        ((rootedCopies Dc₁ R root ×ˢ rootedCopies Dc₂ RB rB : Finset (Finset V × Finset V)) :
          Set (Finset V × Finset V)) := by
    intro Dc₁ Dc₂ hdisj B _ RB rB ⟨S₁, S₂⟩ h1 ⟨T₁, T₂⟩ h2 heq
    rw [Finset.mem_coe, Finset.mem_product, mem_rootedCopies_iff, mem_rootedCopies_iff] at h1 h2
    have h_1 : S₁ = T₁ := by
      have h := congrArg (· ∩ Dc₁.A₁) heq
      have hd1 : Disjoint S₂ Dc₁.A₁ := Disjoint.mono_left h1.2.1 hdisj.symm
      have hd2 : Disjoint T₂ Dc₁.A₁ := Disjoint.mono_left h2.2.1 hdisj.symm
      simpa [Finset.union_inter_distrib_right, Finset.inter_eq_left.mpr h1.1.1,
        Finset.inter_eq_left.mpr h2.1.1, Finset.disjoint_iff_inter_eq_empty.mp hd1,
        Finset.disjoint_iff_inter_eq_empty.mp hd2] using h
    have h_2 : S₂ = T₂ := by
      have h := congrArg (· ∩ Dc₂.A₁) heq
      have hd1 : Disjoint S₁ Dc₂.A₁ := Disjoint.mono_left h1.1.1 hdisj
      have hd2 : Disjoint T₁ Dc₂.A₁ := Disjoint.mono_left h2.1.1 hdisj
      simpa [Finset.union_inter_distrib_right, Finset.inter_eq_left.mpr h1.2.1,
        Finset.inter_eq_left.mpr h2.2.1, Finset.disjoint_iff_inter_eq_empty.mp hd1,
        Finset.disjoint_iff_inter_eq_empty.mp hd2] using h
    exact Prod.ext h_1 h_2
  rw [hF_eq, Finset.card_union_of_disjoint hF_disj]
  dsimp only [F₁, F₂]
  rw [Finset.card_image_of_injOn (hinj_pair D D.swap (disjoint_A₁_swap D) (pathGraph (r + 1)) 0),
    Finset.card_product,
    Finset.card_image_of_injOn (hinj_pair D.swap D (disjoint_A₁_swap D).symm (pathGraph (r + 1)) 0),
    Finset.card_product]

private lemma mem_rootedCopies_self {V : Type} [Fintype V] {T : SimpleGraph V} {r : ℕ}
    (D : BicenterData T r) : D.A₁ ∈ rootedCopies D D.T₁ D.root₁ := by
  rw [mem_rootedCopies_iff]
  refine ⟨Finset.Subset.refl _, mem_A₁_self D, ?_⟩
  let φ : D.T₁ ≃g T.induce (D.A₁ : Set V) :=
    { toFun := fun x => ⟨x.1, Finset.mem_coe.mpr ((mem_A₁_iff D).mpr x.2)⟩
      invFun := fun x => ⟨x.1, (mem_A₁_iff D).mp (Finset.mem_coe.mp x.2)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_rel_iff' := fun {_ _} => Iff.rfl }
  exact ⟨φ, rfl⟩

private lemma rootedCopies_rays_pos {V : Type} [Fintype V] {T : SimpleGraph V} {r : ℕ}
    (D : BicenterData T r) : 0 < (rootedCopies D (pathGraph (r + 1)) 0).card := by
  obtain ⟨a₀, ha₀⟩ := exists_far_vertex D
  obtain ⟨p, hp_path, hp_len⟩ := D.ht_side₁.connected.exists_path_of_dist a₀ D.root₁
  let p' := p.reverse
  have hp'_path : p'.IsPath := hp_path.reverse
  have hp'_len : p'.length = r := by dsimp [p']; rw [Walk.length_reverse, hp_len, ha₀]
  let P : Finset V := (p'.support.map Subtype.val).toFinset
  have hP_sub : P ⊆ D.A₁ := by
    intro x hx
    rw [List.mem_toFinset, List.mem_map] at hx
    obtain ⟨y, _, rfl⟩ := hx
    exact (mem_A₁_iff D).mpr y.2
  have hc₁_P : D.c₁ ∈ P := by
    rw [List.mem_toFinset, List.mem_map]
    exact ⟨D.root₁, p'.start_mem_support, rfl⟩
  let φ : pathGraph (r + 1) ≃g T.induce (P : Set V) :=
    { toFun := fun i => ⟨(p'.getVert i.1).1, by
        rw [Finset.mem_coe, List.mem_toFinset, List.mem_map]
        exact ⟨p'.getVert i.1, p'.getVert_mem_support i.1, rfl⟩⟩
      invFun := fun x => ⟨(p'.support.map Subtype.val).idxOf x.1, by
        have hmem := List.mem_toFinset.mp (Finset.mem_coe.mp x.2)
        have hlt := List.idxOf_lt_length_of_mem hmem
        rw [List.length_map, p'.length_support, hp'_len] at hlt
        exact hlt⟩
      left_inv := fun i => by
        ext
        dsimp
        have hi_lt : i.1 < (p'.support.map Subtype.val).length := by
          rw [List.length_map, p'.length_support, hp'_len]; exact i.isLt
        have hnodup : (p'.support.map Subtype.val).Nodup :=
          hp'_path.support_nodup.map Subtype.val_injective
        rw [p'.getVert_eq_support_getElem (by omega : i.1 ≤ p'.length)]
        have hget : (p'.support[i.1]' (by rw [p'.length_support, hp'_len]; exact i.isLt)).1 =
            (p'.support.map Subtype.val)[i.1]' hi_lt := by simp
        rw [hget]
        exact hnodup.idxOf_getElem i.1 hi_lt
      right_inv := fun x => by
        ext
        dsimp
        have hmem : x.1 ∈ p'.support.map Subtype.val := List.mem_toFinset.mp (Finset.mem_coe.mp x.2)
        have hlt := List.idxOf_lt_length_of_mem hmem
        rw [p'.getVert_eq_support_getElem (by rw [List.length_map, p'.length_support] at hlt; omega)]
        have hget : (p'.support[(p'.support.map Subtype.val).idxOf x.1]'
            (by rw [List.length_map] at hlt; exact hlt)).1 =
            (p'.support.map Subtype.val)[(p'.support.map Subtype.val).idxOf x.1]' hlt :=
          (List.getElem_map (f := Subtype.val)).symm
        rw [hget]
        exact List.getElem_idxOf hlt
      map_rel_iff' := fun {i j} => by
        change T.Adj (p'.getVert i.1).1 (p'.getVert j.1).1 ↔ (pathGraph (r + 1)).Adj i j
        have hadj_iff : ∀ a b : Fin (r + 1), a.1 ≤ b.1 →
            (T.Adj (p'.getVert a.1).1 (p'.getVert b.1).1 ↔ a.1 + 1 = b.1) := by
          intro a b hab
          constructor
          · intro hadj
            have hadj_sub : D.T₁.Adj (p'.getVert a.1) (p'.getVert b.1) := hadj
            let q := (p'.drop a.1).take (b.1 - a.1)
            have hsub : q.IsSubwalk p' := (Walk.isSubwalk_take _ _).trans (Walk.isSubwalk_drop _ _)
            have hp'_dist : p'.length = D.T₁.dist D.root₁ a₀ :=
              hp'_len.trans (SimpleGraph.dist_comm.trans ha₀).symm
            have hdist_eq : q.length = D.T₁.dist (p'.getVert a.1) ((p'.drop a.1).getVert (b.1 - a.1)) :=
              length_eq_dist_of_subwalk hp'_dist hsub
            have hql : q.length = b.1 - a.1 := by
              dsimp [q]
              rw [Walk.take_length, Walk.drop_length]
              have := b.isLt
              omega
            have hdv : D.T₁.dist (p'.getVert a.1) ((p'.drop a.1).getVert (b.1 - a.1)) = 1 := by
              rw [Walk.drop_getVert, Nat.add_sub_of_le hab, dist_eq_one_iff_adj.mpr hadj_sub]
            omega
          · intro hsucc
            rw [← hsucc]
            exact p'.adj_getVert_succ (by omega)
        rw [pathGraph_adj]
        rcases le_total i.1 j.1 with hij | hji
        · rw [hadj_iff i j hij]
          constructor
          · exact Or.inl
          · rintro (h | h) <;> omega
        · rw [adj_comm, hadj_iff j i hji]
          constructor
          · exact Or.inr
          · rintro (h | h) <;> omega }
  refine Finset.card_pos.mpr ⟨P, ?_⟩
  rw [mem_rootedCopies_iff]
  exact ⟨hP_sub, hc₁_P, φ, by
    dsimp [φ]
    rw [Walk.getVert_zero]
    rfl⟩

private lemma rootedCopies_nonempty_implies_le_card {V : Type} [Fintype V] {T : SimpleGraph V} {r : ℕ}
    (D : BicenterData T r) {A : Type} [Fintype A] {R : SimpleGraph A} {root : A}
    (hpos : 0 < (rootedCopies D R root).card) : Fintype.card A ≤ D.A₁.card := by
  obtain ⟨S₁, hS₁⟩ := Finset.card_pos.mp hpos
  rw [mem_rootedCopies_iff] at hS₁
  obtain ⟨hsub, _, ⟨φ, _⟩⟩ := hS₁
  have hc : Fintype.card A = S₁.card := by
    simpa using Fintype.card_congr φ.toEquiv
  exact hc ▸ Finset.card_le_card hsub

private lemma rootedCopies_eq_one_of_eq_card {V : Type} [Fintype V] {T : SimpleGraph V} {r : ℕ}
    (D : BicenterData T r) {A : Type} [Fintype A] {R : SimpleGraph A} {root : A}
    (hcard : Fintype.card A = D.A₁.card) :
    (0 < (rootedCopies D R root).card ↔ RootedIso D.T₁ D.root₁ R root) ∧
    (RootedIso D.T₁ D.root₁ R root → (rootedCopies D R root).card = 1) := by
  have hsub_eq : ∀ S₁ ∈ rootedCopies D R root, S₁ = D.A₁ := by
    intro S₁ hS₁
    rw [mem_rootedCopies_iff] at hS₁
    obtain ⟨hsub, _, ⟨φ, _⟩⟩ := hS₁
    have hc : S₁.card = Fintype.card A := by simpa using (Fintype.card_congr φ.toEquiv).symm
    exact Finset.eq_of_subset_of_card_le hsub (by omega)
  constructor
  · constructor
    · intro hpos
      obtain ⟨S₁, hS₁⟩ := Finset.card_pos.mp hpos
      have heq := hsub_eq S₁ hS₁
      subst heq
      rw [mem_rootedCopies_iff] at hS₁
      obtain ⟨_, _, ⟨φ, hφ⟩⟩ := hS₁
      let ψ : D.T₁ ≃g T.induce (D.A₁ : Set V) :=
        { toFun := fun x => ⟨x.1, Finset.mem_coe.mpr ((mem_A₁_iff D).mpr x.2)⟩
          invFun := fun x => ⟨x.1, (mem_A₁_iff D).mp (Finset.mem_coe.mp x.2)⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl
          map_rel_iff' := fun {_ _} => Iff.rfl }
      exact ⟨ψ.trans φ.symm, by
        dsimp [ψ, BicenterData.root₁]
        exact φ.symm_apply_eq.mpr (Subtype.ext hφ.symm)⟩
    · rintro ⟨φ, hφ⟩
      refine Finset.card_pos.mpr ⟨D.A₁, ?_⟩
      rw [mem_rootedCopies_iff]
      refine ⟨Finset.Subset.refl _, mem_A₁_self D, ?_⟩
      let ψ : D.T₁ ≃g T.induce (D.A₁ : Set V) :=
        { toFun := fun x => ⟨x.1, Finset.mem_coe.mpr ((mem_A₁_iff D).mpr x.2)⟩
          invFun := fun x => ⟨x.1, (mem_A₁_iff D).mp (Finset.mem_coe.mp x.2)⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl
          map_rel_iff' := fun {_ _} => Iff.rfl }
      exact ⟨φ.symm.trans ψ, by
        dsimp [ψ]
        have h1 : φ.symm root = D.root₁ := φ.symm_apply_eq.mpr hφ.symm
        rw [h1]
        rfl⟩
  · intro h_iso
    have hpos : 0 < (rootedCopies D R root).card := by
      obtain ⟨φ, hφ⟩ := h_iso
      refine Finset.card_pos.mpr ⟨D.A₁, ?_⟩
      rw [mem_rootedCopies_iff]
      refine ⟨Finset.Subset.refl _, mem_A₁_self D, ?_⟩
      let ψ : D.T₁ ≃g T.induce (D.A₁ : Set V) :=
        { toFun := fun x => ⟨x.1, Finset.mem_coe.mpr ((mem_A₁_iff D).mpr x.2)⟩
          invFun := fun x => ⟨x.1, (mem_A₁_iff D).mp (Finset.mem_coe.mp x.2)⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl
          map_rel_iff' := fun {_ _} => Iff.rfl }
      exact ⟨φ.symm.trans ψ, by
        dsimp [ψ]
        have h1 : φ.symm root = D.root₁ := φ.symm_apply_eq.mpr hφ.symm
        rw [h1]
        rfl⟩
    have hle1 : (rootedCopies D R root).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro a ha b hb
      rw [hsub_eq a ha, hsub_eq b hb]
    omega

private lemma rootedCopies_card_le_of_rootedIso {V W : Type} [Fintype V] [Fintype W]
    {G : SimpleGraph V} {H : SimpleGraph W} {r : ℕ}
    (DG : BicenterData G r) (DH : BicenterData H r)
    (hiso : RootedIso DG.T₁ DG.root₁ DH.T₁ DH.root₁)
    {A : Type} [Fintype A] (R : SimpleGraph A) (root : A) :
    (rootedCopies DG R root).card ≤ (rootedCopies DH R root).card := by
  obtain ⟨ψ, hψ⟩ := hiso
  let mapS : Finset V → Finset W := fun S₁ =>
    (Finset.univ.filter (fun y : DH.side₁ => (ψ.symm y).1 ∈ S₁)).image Subtype.val
  refine Finset.card_le_card_of_injOn mapS ?_ ?_
  · intro S₁ hS₁
    rw [Finset.mem_coe, mem_rootedCopies_iff] at hS₁ ⊢
    obtain ⟨hsub, hc₁, ⟨φ, hφ⟩⟩ := hS₁
    have hc₁_map : DH.c₁ ∈ mapS S₁ := by
      simp only [mapS, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨DH.root₁, ?_, rfl⟩
      have hsym : ψ.symm DH.root₁ = DG.root₁ := ψ.symm_apply_eq.mpr hψ.symm
      rw [hsym]
      exact hc₁
    have hmem_map_side : ∀ {w : W}, w ∈ mapS S₁ → w ∈ DH.side₁ := by
      intro w hw
      simp only [mapS, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hw
      obtain ⟨y', _, rfl⟩ := hw
      exact y'.2
    have hmem_map_inv : ∀ {w : W} (hw : w ∈ mapS S₁),
        (ψ.symm ⟨w, hmem_map_side hw⟩).1 ∈ S₁ := by
      intro w hw
      have hw0 := hw
      simp only [mapS, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hw0
      obtain ⟨y', hy'_in, hy'_eq⟩ := hw0
      have : (⟨w, hmem_map_side hw⟩ : DH.side₁) = y' := Subtype.ext hy'_eq.symm
      rw [this]
      exact hy'_in
    have hmem_to_map : ∀ x : (S₁ : Set V),
        (ψ ⟨x.1, (mem_A₁_iff DG).mp (hsub (Finset.mem_coe.mp x.2))⟩).1 ∈ mapS S₁ := by
      intro x
      simp only [mapS, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨ψ ⟨x.1, (mem_A₁_iff DG).mp (hsub (Finset.mem_coe.mp x.2))⟩,
        by rw [ψ.symm_apply_apply]; exact Finset.mem_coe.mp x.2, rfl⟩
    let ψS : G.induce (S₁ : Set V) ≃g H.induce (mapS S₁ : Set W) :=
      { toFun := fun x =>
          ⟨(ψ ⟨x.1, (mem_A₁_iff DG).mp (hsub (Finset.mem_coe.mp x.2))⟩).1,
            Finset.mem_coe.mpr (hmem_to_map x)⟩
        invFun := fun y =>
          ⟨(ψ.symm ⟨y.1, hmem_map_side (Finset.mem_coe.mp y.2)⟩).1,
            Finset.mem_coe.mpr (hmem_map_inv (Finset.mem_coe.mp y.2))⟩
        left_inv := fun x => by
          ext
          dsimp only
          exact congrArg (Subtype.val : DG.side₁ → V)
            (ψ.symm_apply_apply ⟨x.1, (mem_A₁_iff DG).mp (hsub (Finset.mem_coe.mp x.2))⟩)
        right_inv := fun y => by
          ext
          dsimp only
          exact congrArg (Subtype.val : DH.side₁ → W)
            (ψ.apply_symm_apply ⟨y.1, hmem_map_side (Finset.mem_coe.mp y.2)⟩)
        map_rel_iff' := fun {a b} => ψ.map_rel_iff }
    have hroot : (⟨(φ root).1, (mem_A₁_iff DG).mp (hsub (Finset.mem_coe.mp (φ root).2))⟩ : DG.side₁) =
        DG.root₁ := Subtype.ext hφ
    refine ⟨fun y hy => (mem_A₁_iff DH).mpr (hmem_map_side hy), hc₁_map, φ.trans ψS, ?_⟩
    exact (congrArg (fun z => (ψ z).1) hroot).trans (congrArg Subtype.val hψ)
  · intro S₁ hS₁ S₂ hS₂ heq
    rw [Finset.mem_coe, mem_rootedCopies_iff] at hS₁ hS₂
    ext x
    by_cases hx : x ∈ DG.A₁
    · let x_sub : DG.side₁ := ⟨x, (mem_A₁_iff DG).mp hx⟩
      have hm := Finset.ext_iff.mp heq (ψ x_sub).1
      simp only [mapS, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hm
      constructor <;> intro hxS
      · obtain ⟨y', hy', hy'_eq⟩ := hm.mp ⟨ψ x_sub, by simpa using hxS, rfl⟩
        have : y' = ψ x_sub := Subtype.ext hy'_eq
        rw [this, ψ.symm_apply_apply] at hy'
        exact hy'
      · obtain ⟨y', hy', hy'_eq⟩ := hm.mpr ⟨ψ x_sub, by simpa using hxS, rfl⟩
        have : y' = ψ x_sub := Subtype.ext hy'_eq
        rw [this, ψ.symm_apply_apply] at hy'
        exact hy'
    · exact ⟨fun h => False.elim (hx (hS₁.1 h)), fun h => False.elim (hx (hS₂.1 h))⟩

private lemma rootedCopies_card_eq_of_rootedIso {V W : Type} [Fintype V] [Fintype W]
    {G : SimpleGraph V} {H : SimpleGraph W} {r : ℕ}
    (DG : BicenterData G r) (DH : BicenterData H r)
    (hiso : RootedIso DG.T₁ DG.root₁ DH.T₁ DH.root₁)
    {A : Type} [Fintype A] (R : SimpleGraph A) (root : A) :
    (rootedCopies DG R root).card = (rootedCopies DH R root).card :=
  le_antisymm (rootedCopies_card_le_of_rootedIso DG DH hiso R root)
    (rootedCopies_card_le_of_rootedIso DH DG hiso.symm R root)

private lemma glue_bicenter_iso {V W : Type} [Fintype V] [Fintype W]
    {G : SimpleGraph V} {H : SimpleGraph W} {r : ℕ}
    (DG : BicenterData G r) (DH : BicenterData H r)
    (h1 : RootedIso DG.T₁ DG.root₁ DH.T₁ DH.root₁)
    (h2 : RootedIso DG.swap.T₁ DG.swap.root₁ DH.swap.T₁ DH.swap.root₁) :
    Nonempty (G ≃g H) := by
  obtain ⟨φ₁, hφ₁⟩ := h1
  obtain ⟨φ₂, hφ₂⟩ := h2
  let toF : V → W := fun x =>
    if hx : x ∈ DG.side₁ then (φ₁ ⟨x, hx⟩).1
    else (φ₂ ⟨x, mem_swap_side₁_of_not_mem DG hx⟩).1
  let invF : W → V := fun y =>
    if hy : y ∈ DH.side₁ then (φ₁.symm ⟨y, hy⟩).1
    else (φ₂.symm ⟨y, mem_swap_side₁_of_not_mem DH hy⟩).1
  have hleft : Function.LeftInverse invF toF := by
    intro x
    dsimp only [toF, invF]
    by_cases hx : x ∈ DG.side₁
    · rw [dif_pos hx, dif_pos (φ₁ ⟨x, hx⟩).2]
      simp
    · have hx2 : x ∈ DG.swap.side₁ := mem_swap_side₁_of_not_mem DG hx
      have hnot : (φ₂ ⟨x, hx2⟩).1 ∉ DH.side₁ := by
        intro hmem
        have hmem2 : (φ₂ ⟨x, hx2⟩).1 ∈ DH.swap.side₁ := (φ₂ ⟨x, hx2⟩).2
        change H.dist _ DH.c₁ < H.dist _ DH.c₂ at hmem
        change H.dist _ DH.c₂ < H.dist _ DH.c₁ at hmem2
        omega
      rw [dif_neg hx, dif_neg hnot]
      simp
  have hright : Function.RightInverse invF toF := by
    intro y
    dsimp only [toF, invF]
    by_cases hy : y ∈ DH.side₁
    · rw [dif_pos hy, dif_pos (φ₁.symm ⟨y, hy⟩).2]
      simp
    · have hy2 : y ∈ DH.swap.side₁ := mem_swap_side₁_of_not_mem DH hy
      have hnot : (φ₂.symm ⟨y, hy2⟩).1 ∉ DG.side₁ := by
        intro hmem
        have hmem2 : (φ₂.symm ⟨y, hy2⟩).1 ∈ DG.swap.side₁ := (φ₂.symm ⟨y, hy2⟩).2
        change G.dist _ DG.c₁ < G.dist _ DG.c₂ at hmem
        change G.dist _ DG.c₂ < G.dist _ DG.c₁ at hmem2
        omega
      rw [dif_neg hy, dif_neg hnot]
      simp
  refine ⟨⟨⟨toF, invF, hleft, hright⟩, ?_⟩⟩
  intro x y
  dsimp only [Equiv.coe_fn_mk, toF]
  by_cases hx : x ∈ DG.side₁ <;> by_cases hy : y ∈ DG.side₁
  · rw [dif_pos hx, dif_pos hy]
    exact φ₁.map_rel_iff (a := ⟨x, hx⟩) (b := ⟨y, hy⟩)
  · have hy2 : y ∈ DG.swap.side₁ := mem_swap_side₁_of_not_mem DG hy
    rw [dif_pos hx, dif_neg hy]
    constructor
    · intro hadj
      obtain ⟨hx_c, hy_c⟩ := eq_center_of_adj_across DH (φ₁ ⟨x, hx⟩).2 (φ₂ ⟨y, hy2⟩).2 hadj
      have hx1 : (⟨x, hx⟩ : DG.side₁) = DG.root₁ :=
        φ₁.injective (Subtype.ext (hx_c.trans (congrArg Subtype.val hφ₁).symm))
      have hy1 : (⟨y, hy2⟩ : DG.swap.side₁) = DG.swap.root₁ :=
        φ₂.injective (Subtype.ext (hy_c.trans (congrArg Subtype.val hφ₂).symm))
      have hx_eq : x = DG.c₁ := congrArg Subtype.val hx1
      have hy_eq : y = DG.c₂ := congrArg Subtype.val hy1
      rw [hx_eq, hy_eq]
      exact DG.hadj
    · intro hadj
      obtain ⟨hx_c, hy_c⟩ := eq_center_of_adj_across DG hx hy2 hadj
      have hx1 : (⟨x, hx⟩ : DG.side₁) = DG.root₁ := Subtype.ext hx_c
      have hy1 : (⟨y, hy2⟩ : DG.swap.side₁) = DG.swap.root₁ := Subtype.ext hy_c
      rw [hx1, hy1, hφ₁, hφ₂]
      exact DH.hadj
  · have hx2 : x ∈ DG.swap.side₁ := mem_swap_side₁_of_not_mem DG hx
    rw [dif_neg hx, dif_pos hy]
    rw [adj_comm, adj_comm (G := G)]
    constructor
    · intro hadj
      obtain ⟨hy_c, hx_c⟩ := eq_center_of_adj_across DH (φ₁ ⟨y, hy⟩).2 (φ₂ ⟨x, hx2⟩).2 hadj
      have hy1 : (⟨y, hy⟩ : DG.side₁) = DG.root₁ :=
        φ₁.injective (Subtype.ext (hy_c.trans (congrArg Subtype.val hφ₁).symm))
      have hx1 : (⟨x, hx2⟩ : DG.swap.side₁) = DG.swap.root₁ :=
        φ₂.injective (Subtype.ext (hx_c.trans (congrArg Subtype.val hφ₂).symm))
      have hy_eq : y = DG.c₁ := congrArg Subtype.val hy1
      have hx_eq : x = DG.c₂ := congrArg Subtype.val hx1
      rw [hy_eq, hx_eq]
      exact DG.hadj
    · intro hadj
      obtain ⟨hy_c, hx_c⟩ := eq_center_of_adj_across DG hy hx2 hadj
      have hy1 : (⟨y, hy⟩ : DG.side₁) = DG.root₁ := Subtype.ext hy_c
      have hx1 : (⟨x, hx2⟩ : DG.swap.side₁) = DG.swap.root₁ := Subtype.ext hx_c
      rw [hy1, hx1, hφ₁, hφ₂]
      exact DH.hadj
  · have hx2 : x ∈ DG.swap.side₁ := mem_swap_side₁_of_not_mem DG hx
    have hy2 : y ∈ DG.swap.side₁ := mem_swap_side₁_of_not_mem DG hy
    rw [dif_neg hx, dif_neg hy]
    exact φ₂.map_rel_iff (a := ⟨x, hx2⟩) (b := ⟨y, hy2⟩)

private lemma h3_max_side {V W : Type} [Fintype V] [Fintype W]
    {G : SimpleGraph V} {H : SimpleGraph W} {r : ℕ}
    (hcard : Fintype.card V = Fintype.card W)
    (hkelly : ∀ (U : Type) [Fintype U] (Q : SimpleGraph U),
      Fintype.card U < Fintype.card V →
      {S : Finset V | Nonempty (G.induce (S : Set V) ≃g Q)}.ncard =
        {T : Finset W | Nonempty (H.induce (T : Set W) ≃g Q)}.ncard)
    (DG : BicenterData G r) (DH : BicenterData H r)
    (hmax1 : DG.swap.A₁.card ≤ DG.A₁.card)
    (hmax2 : DH.A₁.card ≤ DG.A₁.card)
    (hmax3 : DH.swap.A₁.card ≤ DG.A₁.card) :
    Nonempty (G ≃g H) := by
  have hlt₁ : Fintype.card (DG.side₁ ⊕ Fin (r + 1)) < Fintype.card V := by
    rw [Fintype.card_sum, Fintype.card_fin, card_side₁_eq_A₁_card]
    have h2 : r + 2 ≤ DG.swap.A₁.card := by rw [A₁_card_eq_ncard]; exact DG.hbig₂
    have hsum := card_A₁_add_swap DG
    omega
  have hG_big : r + 2 ≤ Fintype.card DG.side₁ := by
    rw [card_side₁_eq_A₁_card, A₁_card_eq_ncard]; exact DG.hbig₁
  have hQ₁ := hkelly (DG.side₁ ⊕ Fin (r + 1)) (attachPath DG.T₁ DG.root₁ r) hlt₁
  rw [ncard_attachPath_eq DG DG.ht_side₁ (exists_far_vertex DG) hG_big,
    ncard_attachPath_eq DH DG.ht_side₁ (exists_far_vertex DG) hG_big] at hQ₁
  have h_pos_G : 0 < (rootedCopies DG DG.T₁ DG.root₁).card *
      (rootedCopies DG.swap (pathGraph (r + 1)) 0).card :=
    Nat.mul_pos (Finset.card_pos.mpr ⟨DG.A₁, mem_rootedCopies_self DG⟩)
      (rootedCopies_rays_pos DG.swap)
  have h_pos_H : 0 < (rootedCopies DH DG.T₁ DG.root₁).card *
      (rootedCopies DH.swap (pathGraph (r + 1)) 0).card +
      (rootedCopies DH.swap DG.T₁ DG.root₁).card *
      (rootedCopies DH (pathGraph (r + 1)) 0).card := by omega
  have choose_side : ∀ (DH' : BicenterData H r),
      DH'.A₁.card ≤ DG.A₁.card → DH'.swap.A₁.card ≤ DG.A₁.card →
      0 < (rootedCopies DH' DG.T₁ DG.root₁).card →
      Nonempty (G ≃g H) := by
    intro DH' hleA hleB hpos_copy
    have hc_ge := rootedCopies_nonempty_implies_le_card DH' hpos_copy
    rw [card_side₁_eq_A₁_card] at hc_ge
    have hc_eq : DH'.A₁.card = DG.A₁.card := le_antisymm hleA hc_ge
    have hc_swap_eq : DG.swap.A₁.card = DH'.swap.A₁.card := by
      have s1 := card_A₁_add_swap DG
      have s2 := card_A₁_add_swap DH'
      omega
    have hiso₁ : RootedIso DG.T₁ DG.root₁ DH'.T₁ DH'.root₁ := by
      have heq_f : Fintype.card DG.side₁ = DH'.A₁.card := by
        rw [card_side₁_eq_A₁_card, hc_eq]
      exact ((rootedCopies_eq_one_of_eq_card DH' heq_f).1.mp hpos_copy).symm
    have hlt₂ : Fintype.card (DG.swap.side₁ ⊕ Fin (r + 1)) < Fintype.card V := by
      rw [Fintype.card_sum, Fintype.card_fin, card_side₁_eq_A₁_card]
      have h1 : r + 2 ≤ DG.A₁.card := by rw [A₁_card_eq_ncard]; exact DG.hbig₁
      have hsum := card_A₁_add_swap DG
      omega
    have hG₂_big : r + 2 ≤ Fintype.card DG.swap.side₁ := by
      rw [card_side₁_eq_A₁_card, A₁_card_eq_ncard]; exact DG.hbig₂
    have hH₂_big : r + 2 ≤ Fintype.card DH'.swap.side₁ := by
      rw [card_side₁_eq_A₁_card, A₁_card_eq_ncard]; exact DH'.hbig₂
    have hlt_H2 : Fintype.card (DH'.swap.side₁ ⊕ Fin (r + 1)) < Fintype.card V := by
      rw [Fintype.card_sum, Fintype.card_fin, card_side₁_eq_A₁_card]
      have h1 : r + 2 ≤ DH'.A₁.card := by rw [A₁_card_eq_ncard]; exact DH'.hbig₁
      have hsum := card_A₁_add_swap DH'
      omega
    by_cases hsymG : RootedIso DG.T₁ DG.root₁ DG.swap.T₁ DG.swap.root₁
    · by_cases hsymH : RootedIso DH'.T₁ DH'.root₁ DH'.swap.T₁ DH'.swap.root₁
      · exact glue_bicenter_iso DG DH' hiso₁ (hsymG.symm.trans (hiso₁.trans hsymH))
      · exfalso
        have hQ₂ := hkelly (DH'.swap.side₁ ⊕ Fin (r + 1))
          (attachPath DH'.swap.T₁ DH'.swap.root₁ r) hlt_H2
        rw [ncard_attachPath_eq DG DH'.swap.ht_side₁ (exists_far_vertex DH'.swap) hH₂_big,
          ncard_attachPath_eq DH' DH'.swap.ht_side₁ (exists_far_vertex DH'.swap) hH₂_big] at hQ₂
        have hpos_rhs : 0 < (rootedCopies DH'.swap DH'.swap.T₁ DH'.swap.root₁).card *
            (rootedCopies DH' (pathGraph (r + 1)) 0).card :=
          Nat.mul_pos (Finset.card_pos.mpr ⟨DH'.swap.A₁, mem_rootedCopies_self DH'.swap⟩)
            (rootedCopies_rays_pos DH')
        have hcard_H2_eq : Fintype.card DH'.swap.side₁ = DG.A₁.card := by
          have h1 := hsymG.card_eq
          rw [card_side₁_eq_A₁_card, card_side₁_eq_A₁_card] at h1
          rw [card_side₁_eq_A₁_card]
          exact hc_swap_eq.symm.trans h1.symm
        have h0_a : (rootedCopies DG DH'.swap.T₁ DH'.swap.root₁).card = 0 := by
          by_contra hne
          have hp := Nat.pos_of_ne_zero hne
          have hri := (rootedCopies_eq_one_of_eq_card DG hcard_H2_eq).1.mp hp
          exact hsymH (hiso₁.symm.trans hri)
        have hcard_H2_eq2 : Fintype.card DH'.swap.side₁ = DG.swap.A₁.card := by
          rw [card_side₁_eq_A₁_card]; exact hc_swap_eq.symm
        have h0_b : (rootedCopies DG.swap DH'.swap.T₁ DH'.swap.root₁).card = 0 := by
          by_contra hne
          have hp := Nat.pos_of_ne_zero hne
          have hri := (rootedCopies_eq_one_of_eq_card DG.swap hcard_H2_eq2).1.mp hp
          exact hsymH (hiso₁.symm.trans (hsymG.trans hri))
        rw [h0_a, h0_b] at hQ₂
        omega
    · have hnsymH : ¬ RootedIso DH'.T₁ DH'.root₁ DH'.swap.T₁ DH'.swap.root₁ := by
        intro hsymH
        have hQ₂ := hkelly (DG.swap.side₁ ⊕ Fin (r + 1))
          (attachPath DG.swap.T₁ DG.swap.root₁ r) hlt₂
        rw [ncard_attachPath_eq DG DG.swap.ht_side₁ (exists_far_vertex DG.swap) hG₂_big,
          ncard_attachPath_eq DH' DG.swap.ht_side₁ (exists_far_vertex DG.swap) hG₂_big] at hQ₂
        have hpos_lhs : 0 < (rootedCopies DG.swap DG.swap.T₁ DG.swap.root₁).card *
            (rootedCopies DG (pathGraph (r + 1)) 0).card :=
          Nat.mul_pos (Finset.card_pos.mpr ⟨DG.swap.A₁, mem_rootedCopies_self DG.swap⟩)
            (rootedCopies_rays_pos DG)
        have hcard_G2_eq1 : Fintype.card DG.swap.side₁ = DH'.A₁.card := by
          have h1 := hsymH.card_eq
          rw [card_side₁_eq_A₁_card, card_side₁_eq_A₁_card] at h1
          rw [card_side₁_eq_A₁_card]
          exact hc_swap_eq.trans h1.symm
        have h0_a : (rootedCopies DH' DG.swap.T₁ DG.swap.root₁).card = 0 := by
          by_contra hne
          have hp := Nat.pos_of_ne_zero hne
          have hri := (rootedCopies_eq_one_of_eq_card DH' hcard_G2_eq1).1.mp hp
          exact hsymG (hiso₁.trans hri)
        have hcard_G2_eq2 : Fintype.card DG.swap.side₁ = DH'.swap.A₁.card := by
          rw [card_side₁_eq_A₁_card]; exact hc_swap_eq
        have h0_b : (rootedCopies DH'.swap DG.swap.T₁ DG.swap.root₁).card = 0 := by
          by_contra hne
          have hp := Nat.pos_of_ne_zero hne
          have hri := (rootedCopies_eq_one_of_eq_card DH'.swap hcard_G2_eq2).1.mp hp
          exact hsymG (hiso₁.trans (hsymH.trans hri))
        rw [h0_a, h0_b] at hQ₂
        omega
      have hQ₁' := hkelly (DG.side₁ ⊕ Fin (r + 1)) (attachPath DG.T₁ DG.root₁ r) hlt₁
      rw [ncard_attachPath_eq DG DG.ht_side₁ (exists_far_vertex DG) hG_big,
        ncard_attachPath_eq DH' DG.ht_side₁ (exists_far_vertex DG) hG_big] at hQ₁'
      have hc_G1 : (rootedCopies DG DG.T₁ DG.root₁).card = 1 :=
        (rootedCopies_eq_one_of_eq_card DG (card_side₁_eq_A₁_card DG)).2 (RootedIso.refl _ _)
      have hc_H1 : (rootedCopies DH' DG.T₁ DG.root₁).card = 1 :=
        (rootedCopies_eq_one_of_eq_card DH' (by rw [card_side₁_eq_A₁_card, hc_eq])).2 hiso₁.symm
      have h0_G2 : (rootedCopies DG.swap DG.T₁ DG.root₁).card = 0 := by
        by_contra hne
        have hp := Nat.pos_of_ne_zero hne
        have hle := rootedCopies_nonempty_implies_le_card DG.swap hp
        rw [card_side₁_eq_A₁_card] at hle
        have hsame : DG.swap.A₁.card = DG.A₁.card := le_antisymm hmax1 hle
        have hri := (rootedCopies_eq_one_of_eq_card DG.swap
          (by rw [card_side₁_eq_A₁_card, hsame])).1.mp hp
        exact hsymG hri.symm
      have h0_H2 : (rootedCopies DH'.swap DG.T₁ DG.root₁).card = 0 := by
        by_contra hne
        have hp := Nat.pos_of_ne_zero hne
        have hle := rootedCopies_nonempty_implies_le_card DH'.swap hp
        rw [card_side₁_eq_A₁_card] at hle
        have hsame : DH'.swap.A₁.card = DH'.A₁.card := le_antisymm (hc_eq.symm ▸ hleB) (hc_eq ▸ hle)
        have hri := (rootedCopies_eq_one_of_eq_card DH'.swap
          (by rw [card_side₁_eq_A₁_card, hsame, hc_eq])).1.mp hp
        exact hnsymH (hiso₁.symm.trans hri.symm)
      rw [hc_G1, hc_H1, h0_G2, h0_H2] at hQ₁'
      have hrays₂ : (rootedCopies DG.swap (pathGraph (r + 1)) 0).card =
          (rootedCopies DH'.swap (pathGraph (r + 1)) 0).card := by omega
      have hQ₂ := hkelly (DG.swap.side₁ ⊕ Fin (r + 1))
        (attachPath DG.swap.T₁ DG.swap.root₁ r) hlt₂
      rw [ncard_attachPath_eq DG DG.swap.ht_side₁ (exists_far_vertex DG.swap) hG₂_big,
        ncard_attachPath_eq DH' DG.swap.ht_side₁ (exists_far_vertex DG.swap) hG₂_big] at hQ₂
      have heq_cross : (rootedCopies DG DG.swap.T₁ DG.swap.root₁).card =
          (rootedCopies DH' DG.swap.T₁ DG.swap.root₁).card :=
        rootedCopies_card_eq_of_rootedIso DG DH' hiso₁ DG.swap.T₁ DG.swap.root₁
      have heq_rays₁ : (rootedCopies DG (pathGraph (r + 1)) 0).card =
          (rootedCopies DH' (pathGraph (r + 1)) 0).card :=
        rootedCopies_card_eq_of_rootedIso DG DH' hiso₁ (pathGraph (r + 1)) 0
      have hc_G2 : (rootedCopies DG.swap DG.swap.T₁ DG.swap.root₁).card = 1 :=
        (rootedCopies_eq_one_of_eq_card DG.swap (card_side₁_eq_A₁_card DG.swap)).2 (RootedIso.refl _ _)
      rw [heq_cross, hrays₂, ← heq_rays₁, hc_G2, one_mul] at hQ₂
      have hc_H2 : (rootedCopies DH'.swap DG.swap.T₁ DG.swap.root₁).card = 1 := by
        have hpos_r1 := rootedCopies_rays_pos DG
        have hmul_eq : (rootedCopies DH'.swap DG.swap.T₁ DG.swap.root₁).card *
            (rootedCopies DG (pathGraph (r + 1)) 0).card =
            1 * (rootedCopies DG (pathGraph (r + 1)) 0).card := by omega
        exact Nat.eq_of_mul_eq_mul_right hpos_r1 hmul_eq
      have hiso₂ : RootedIso DG.swap.T₁ DG.swap.root₁ DH'.swap.T₁ DH'.swap.root₁ :=
        ((rootedCopies_eq_one_of_eq_card DH'.swap (by rw [card_side₁_eq_A₁_card, hc_swap_eq])).1.mp
          (hc_H2 ▸ Nat.zero_lt_one)).symm
      exact glue_bicenter_iso DG DH' hiso₁ hiso₂
  rcases Nat.eq_zero_or_pos (rootedCopies DH DG.T₁ DG.root₁).card with h0 | hpos
  · have hpos_swap : 0 < (rootedCopies DH.swap DG.T₁ DG.root₁).card := by
      rw [h0, zero_mul, zero_add] at hQ₁
      by_contra h0s
      have h0s' : (rootedCopies DH.swap DG.T₁ DG.root₁).card = 0 := by omega
      rw [h0s', zero_mul] at hQ₁
      omega
    exact choose_side DH.swap hmax3 hmax2 hpos_swap
  · exact choose_side DH hmax2 hmax3 hpos

end Tree3485H3

theorem result :
    OMA.R_ReconstructionConjecture_reconstruction_conjecture_variants_tree_R1_H4_R1.H3 := by
  intro V W _ _ G H hTG hTH hcard r hr hGd hHd hkelly
    c₁ c₂ hc_adj hc_ne hc_le1 hc_le2 hc_t1 hc_t2 hc_dist hc_big1 hc_big2
    d₁ d₂ hd_adj hd_ne hd_le1 hd_le2 hd_t1 hd_t2 hd_dist hd_big1 hd_big2
  let DG : BicenterData G r :=
    ⟨c₁, c₂, hr, hTG, hGd, hc_adj, hc_ne, hc_le1, hc_le2, hc_t1, hc_t2, hc_dist, hc_big1, hc_big2⟩
  let DH : BicenterData H r :=
    ⟨d₁, d₂, hr, hTH, hHd, hd_adj, hd_ne, hd_le1, hd_le2, hd_t1, hd_t2, hd_dist, hd_big1, hd_big2⟩
  let DG' : BicenterData G r := if DG.swap.A₁.card ≤ DG.A₁.card then DG else DG.swap
  let DH' : BicenterData H r := if DH.swap.A₁.card ≤ DH.A₁.card then DH else DH.swap
  have hDG' : DG'.swap.A₁.card ≤ DG'.A₁.card := by
    dsimp only [DG']
    split_ifs with h
    · exact h
    · exact Nat.le_of_not_ge h
  have hDH' : DH'.swap.A₁.card ≤ DH'.A₁.card := by
    dsimp only [DH']
    split_ifs with h
    · exact h
    · exact Nat.le_of_not_ge h
  by_cases hGH : DH'.A₁.card ≤ DG'.A₁.card
  · exact h3_max_side hcard hkelly DG' DH' hDG' hGH (hDH'.trans hGH)
  · have hHG : DG'.A₁.card ≤ DH'.A₁.card := Nat.le_of_not_ge hGH
    have hkelly_symm : ∀ (U : Type) [Fintype U] (Q : SimpleGraph U),
        Fintype.card U < Fintype.card W →
        {S : Finset W | Nonempty (H.induce (S : Set W) ≃g Q)}.ncard =
          {T : Finset V | Nonempty (G.induce (T : Set V) ≃g Q)}.ncard :=
      fun U _ Q hU => (hkelly U Q (hcard ▸ hU)).symm
    obtain ⟨φ⟩ := h3_max_side hcard.symm hkelly_symm DH' DG' hDH' hHG (hDG'.trans hHG)
    exact ⟨φ.symm⟩

end KellyStep8

namespace KellyStep9

/-
# An odd-diameter tree with a path on one side of its central edge

A small central side gives a pendant path longer than half the diameter.
Deleting an internal vertex of that path shows that the other tree has a
path at least as long. The degree counts of its two attachment vertices
come from comparing the numbers of vertices above each degree threshold.
A second deletion at a terminal leaf identifies corresponding trimmed
paths, which can be interchanged by an automorphism of the leaf card.

Credit: @Deldor14. The tree deletion, distance and component-root lemmas
are adapted from @green-notes' proof of tree.R1.H3.R1.H2.
-/
end KellyStep9
namespace OMA
namespace TreeArms
open SimpleGraph
open Classical
variable {V : Type*} {G : SimpleGraph V} {c : V} {n : Nat}

private lemma isTree_path_eq {U : Type} (T : SimpleGraph U) (hT : T.IsTree)
    {x y : U} {p q : T.Walk x y} (hp : p.IsPath) (hq : q.IsPath) :
    p = q :=
  congrArg Subtype.val ((hT.isAcyclic.subsingleton_path x y).elim ⟨p, hp⟩ ⟨q, hq⟩)

private lemma start_notMem_tail_support_of_isPath {U : Type} {T : SimpleGraph U} {a b : U}
    {w : T.Walk a b} (hw : w.IsPath) : a ∉ w.support.tail := by
  cases w <;> simp_all [Walk.isPath_def]

private lemma existsUnique_root_of_component {U : Type} [Fintype U]
    (T : SimpleGraph U) (hT : T.IsTree) (c : U)
    (C : (T.induce {c}ᶜ).ConnectedComponent) :
    ∃! u : ({c}ᶜ : Set U), u ∈ C.supp ∧ T.Adj c u.1 := by
  obtain ⟨z, hz⟩ := C.nonempty_supp
  have hzc : z.1 ≠ c := z.2
  obtain ⟨p, hp, _⟩ := hT.connected.exists_path_of_dist c z.1
  have hnp : ¬ p.Nil := Walk.not_nil_of_ne hzc.symm
  let uVal : U := p.snd
  have hadj : T.Adj c uVal := p.adj_snd hnp
  have huc : uVal ∈ ({c}ᶜ : Set U) := Set.mem_compl_singleton_iff.mpr hadj.ne.symm
  let u : ({c}ᶜ : Set U) := ⟨uVal, huc⟩
  have hsupp_tail : ∀ x ∈ p.tail.support, x ∈ ({c}ᶜ : Set U) := by
    intro x hx
    rw [Walk.support_tail_of_not_nil p hnp] at hx
    exact Set.mem_compl_singleton_iff.mpr fun hxc =>
      start_notMem_tail_support_of_isPath hp (hxc ▸ hx)
  let p' : (T.induce {c}ᶜ).Walk u z :=
    (p.tail.induce ({c}ᶜ : Set U) hsupp_tail).copy rfl (Subtype.ext rfl)
  have hreach : (T.induce {c}ᶜ).Reachable u z := ⟨p'⟩
  have hu_mem : u ∈ C.supp := by
    rw [ConnectedComponent.mem_supp_iff] at hz ⊢
    exact (ConnectedComponent.sound hreach).trans hz
  refine ⟨u, ⟨hu_mem, hadj⟩, fun u' ⟨hu'_mem, hadj'⟩ => ?_⟩
  by_contra hne
  have hne_val : uVal ≠ u'.1 := fun h => hne (Subtype.ext h).symm
  obtain ⟨q⟩ := C.reachable_of_mem_supp hu_mem hu'_mem
  let q_path := q.toPath
  let g : T.induce {c}ᶜ →g T := (SimpleGraph.Embedding.induce ({c}ᶜ : Set U)).toHom
  have hqG : (q_path.val.map g).IsPath := q_path.isPath.map Subtype.val_injective
  have hc_not_q : c ∉ (q_path.val.map g).support := by
    rw [Walk.support_map, List.mem_map]
    rintro ⟨x, _, hxc⟩
    exact x.2 hxc
  let two_step : T.Walk uVal u'.1 := Walk.cons hadj.symm (Walk.cons hadj' Walk.nil)
  have htwo_path : two_step.IsPath := by
    simp [two_step, Walk.cons_isPath_iff, hne_val, hadj.ne.symm, hadj'.ne]
  have heq := isTree_path_eq T hT hqG htwo_path
  have hc_in : c ∈ two_step.support := by simp [two_step]
  rw [← heq] at hc_in
  exact hc_not_q hc_in


private lemma Arm.first (a : Arm G c (n+1)) (i : Fin (n+1)) :
    G.Adj c (a.vertex i) ↔ i.val=0 := by
  rw [G.adj_comm,(a.external i c (fun ⟨j,e⟩ => a.away j e))]
  simp

private lemma Arm.nextexists {V : Type} [Fintype V] {G : SimpleGraph V} {c : V}
    (conn : G.Connected) (branch : ∃ x,3 ≤ (G.neighborSet x).ncard) (a : Arm G c (n+1))
    (low : (G.neighborSet c).ncard ≤ 2) : ∃ z, z≠a.vertex 0 ∧ G.Adj c z := by
  classical
  by_contra h
  have no {z} (adj : G.Adj c z) : z=a.vertex 0 := Classical.byContradiction (fun neq => h ⟨z,neq,adj⟩)
  let S (x : V) : Prop := x=c ∨ x∈Set.range a.vertex
  have close {x y} (xs : S x) (xy : G.Adj x y) : S y := by
    rcases xs with rfl|⟨i,rfl⟩
    · exact Or.inr ⟨0,(no xy).symm⟩
    · by_cases mem : y∈Set.range a.vertex
      · exact Or.inr mem
      · exact Or.inl ((a.external _ _ mem).mp xy).2
  have extend {u v} (p : G.Walk u v) (hu : S u) : S v := by
    induction p with
    | nil => exact hu
    | cons ad _ ih => exact ih (close hu ad)
  obtain ⟨x,hi⟩ := branch
  rcases extend (conn c x).some (Or.inl rfl) with rfl|⟨i,rfl⟩
  · omega
  · have := a.degree_bound i;omega

private lemma Arm.extend {V : Type} [Fintype V] {G : SimpleGraph V} {c : V} (conn : G.Connected)
    (branch : ∃ x,3 ≤ (G.neighborSet x).ncard) (a : Arm G c (n+1)) (low : (G.neighborSet c).ncard ≤ 2) :
    ∃ z, G.Adj c z ∧ ∃ b : Arm G z (n+2), b.vertex 0=c ∧ ∀ i,b.vertex i.succ=a.vertex i := by
  classical
  obtain ⟨z,ne,adj⟩ := a.nextexists conn branch low
  have one := (a.first 0).mpr rfl
  have all (y) (h : G.Adj c y) : y=a.vertex 0 ∨ y=z := by
    by_contra! bad
    have t := (Set.two_lt_ncard_iff (Set.toFinite (G.neighborSet c))).mpr
      ⟨a.vertex 0,z,y,one,adj,h,ne.symm,bad.1.symm,bad.2.symm⟩
    omega
  have out : z ∉ Set.range a.vertex := by
    rintro ⟨i,e⟩
    have i0 : i=0 := Fin.ext ((a.first i).mp (e ▸ adj))
    exact ne (e.symm.trans (congrArg a.vertex i0))
  let vs : Fin (n+2) → V := Fin.cases c a.vertex
  have inj : Function.Injective vs := by
    intro i j
    refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
    · simp
    · exact fun e => (a.away j e.symm).elim
    · exact fun e => (a.away i e).elim
    · exact fun e => congrArg Fin.succ (a.vertex.injective e)
  refine ⟨z,adj,⟨⟨vs,inj⟩,?_,?_,?_⟩,rfl,fun _ => rfl⟩
  · exact Fin.cases adj.ne (fun i e => out ⟨i,e⟩)
  · intro i j
    refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
    · simp [vs]
    · change G.Adj c (a.vertex j) ↔ _
      rw [a.first];simp
    · change G.Adj (a.vertex i) c ↔ _
      rw [G.adj_comm,a.first];simp
    · change G.Adj (a.vertex i) (a.vertex j) ↔ _
      rw [a.internal];simp
  · intro i x outside
    have cx : x≠c := fun e => outside ⟨0,e.symm⟩
    have ax : x∉Set.range a.vertex := fun ⟨j,e⟩ => outside ⟨j.succ,e⟩
    refine Fin.cases ?_ (fun i => ?_) i
    · change G.Adj c x ↔ 0=0 ∧ x=z
      constructor
      · intro h
        exact ⟨rfl,(all x h).resolve_left (fun e => ax ⟨0,e.symm⟩)⟩
      · rintro ⟨_,rfl⟩;exact adj
    · change G.Adj (a.vertex i) x ↔ i.val+1=0 ∧ x=z
      rw [a.external _ _ ax]
      simp [cx]

private lemma line_dist {V : Type} {G : SimpleGraph V} (tree : G.IsTree) (f : Fin (n+1) → V)
    (inj : Function.Injective f) (step : ∀ i : Fin n,G.Adj (f i.castSucc) (f i.succ)) :
    G.dist (f 0) (f (Fin.last n)) = n := by
  let l := List.ofFn f
  have size : l.length=n+1 := List.length_ofFn
  have non : l ≠ [] := by intro emp;rw [emp] at size;simp at size
  have chain : l.IsChain G.Adj := by
    rw [List.isChain_iff_getElem]
    intro i hi
    have lt : i < n := by omega
    dsimp only [l]
    simp only [List.getElem_ofFn]
    exact step ⟨i,lt⟩
  let w := Walk.ofSupport l non chain
  have path : w.IsPath := by
    rw [Walk.isPath_def,Walk.support_ofSupport]
    exact List.nodup_ofFn.mpr inj
  have len := isTree_dist_eq_length_of_isPath G tree w path
  have shape := w.length_support
  rw [Walk.support_ofSupport] at shape
  have zero : l.head non = f 0 := by simp [l,List.head_eq_getElem_zero]
  have last : l.getLast non = f (Fin.last n) := List.getLast_ofFn_succ f
  have e : G.dist (l.head non) (l.getLast non) = n := by omega
  rwa [zero,last] at e

private lemma Arm.tip_dist {V : Type} {G : SimpleGraph V} {c : V} (tree : G.IsTree)
    (a : Arm G c (n+1)) : G.dist c (a.vertex (Fin.last n)) = n+1 := by
  let f : Fin (n+2) → V := Fin.cases c a.vertex
  have inj : Function.Injective f := by
    intro i j
    refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
    · simp
    · exact fun h => (a.away j h.symm).elim
    · exact fun h => (a.away i h).elim
    · exact fun h => congrArg Fin.succ (a.vertex.injective h)
  have adj (i : Fin (n+1)) : G.Adj (f i.castSucc) (f i.succ) := by
    refine Fin.cases ((a.first 0).mpr rfl) (fun j => ?_) i
    exact (a.internal j.castSucc j.succ).mpr (Or.inl rfl)
  exact line_dist tree f inj adj

private def Arm.keep {V : Type} {G : SimpleGraph V} {c x : V} (a : Arm G c n)
    (xc : x≠c) (outside : x∉Set.range a.vertex) : Arm (G.induce {x}ᶜ) (⟨c,xc.symm⟩ : ({x}ᶜ : Set V)) n where
  vertex := ⟨fun i => ⟨a.vertex i,fun e => outside ⟨i,e⟩⟩,
    fun _ _ e => a.vertex.injective (congrArg Subtype.val e)⟩
  away i := fun e => a.away i (congrArg Subtype.val e)
  internal := a.internal
  external i y hy := by
    have yy : y.val∉Set.range a.vertex := fun ⟨j,e⟩ => hy ⟨j,Subtype.ext e⟩
    change G.Adj (a.vertex i) y.val ↔ _
    rw [a.external _ _ yy]
    simp [Subtype.ext_iff]

private lemma Arm.low_tip {V : Type} [Fintype V] {G : SimpleGraph V} {c : V} (a : Arm G c (n+1))
    (i : Fin (n+1)) (leaf : (G.neighborSet (a.vertex i)).ncard = 1) : i = Fin.last n := by
  by_contra ne
  have lt : i.val < n := by contrapose! ne; apply Fin.ext; simp;omega
  let j : Fin (n+1) := ⟨i.val+1,by omega⟩
  have next := (a.internal i j).mpr (Or.inl rfl)
  have unique := (Set.ncard_le_one (Set.toFinite (G.neighborSet (a.vertex i)))).mp leaf.le
  by_cases z : i.val=0
  · have left := ((a.first i).mpr z).symm
    exact a.away j (unique _ next _ left)
  · let k : Fin (n+1) := ⟨i.val-1,by omega⟩
    have prev := (a.internal i k).mpr (Or.inr (by dsimp [k];omega))
    have h := congrArg Fin.val (a.vertex.injective (unique _ next _ prev))
    dsimp [j,k] at h;omega

private lemma Arm.leaf {V : Type} [Fintype V] {G : SimpleGraph V} {c : V} (a : Arm G c (n+1)) :
    G.degree (a.vertex (Fin.last n))=1 := by
  cases n with
  | zero =>
    apply degree_eq_one_iff_existsUnique_adj.mpr
    refine ⟨c,((a.first _).mpr rfl).symm,?_⟩
    intro y adj
    by_cases inside : y∈Set.range a.vertex
    · obtain ⟨i,rfl⟩ := inside
      exact (adj.ne (congrArg a.vertex (Fin.ext (by simp)))).elim
    · exact ((a.external _ _ inside).mp adj).2
  | succ n => exact a.tip_deg

private lemma Arm.branch_out {V : Type} [Fintype V] {G : SimpleGraph V} {c u : V} (a : Arm G c n)
    (hi : 3 ≤ G.degree u) : u ∉ Set.range a.vertex := by
  rintro ⟨i,e⟩
  have b := a.degree_bound i;rw [ncard_neighborSet_eq_degree,e] at b;omega

private lemma arm_alternatives {V : Type} [Fintype V] {G : SimpleGraph V} (tr : G.IsTree)
    {c d : V} {k l : Nat} (A : Arm G c (k+1)) (B : Arm G d (l+1))
    (ha : 3≤G.degree c) (hb : 3≤G.degree d) :
    (A.vertex (Fin.last k) = B.vertex (Fin.last l) ∧ k=l) ∨
      G.dist (B.vertex (Fin.last l)) (A.vertex (Fin.last k)) = k+1+(l+1)+G.dist c d := by
  let x := A.vertex (Fin.last k)
  let y := B.vertex (Fin.last l)
  have ar : G.dist x c=k+1 := G.dist_comm.trans (A.tip_dist tr)
  have br : G.dist y d=l+1 := G.dist_comm.trans (B.tip_dist tr)
  have h := A.dist_outside tr.connected (Set.mem_range_self _) (A.branch_out hb) (x:=x)
  have eqcd : G.dist d c = G.dist c d := G.dist_comm
  by_cases eq : x=y
  · have b := B.dist_outside tr.connected (Set.mem_range_self _) (B.branch_out ha) (x:=y)
    rw [← eq] at b br
    exact Or.inl ⟨eq,by omega⟩
  · have outside : x∉Set.range B.vertex := by
      rintro ⟨i,e⟩
      have leaf : G.degree x=1 := A.leaf
      rw [←e,←ncard_neighborSet_eq_degree] at leaf
      exact eq (e.symm.trans (congrArg B.vertex (B.low_tip i leaf)))
    have split := B.dist_outside tr.connected (Set.mem_range_self _) outside (x:=y)
    rw [G.dist_comm (u:=d) (v:=x)] at split
    change _ ∨ G.dist y x = _
    exact Or.inr (by omega)

private theorem large_anchored {V : Type} [Fintype V] {G : SimpleGraph V} (conn : G.Connected)
    (branch : ∃ x,3 ≤ (G.neighborSet x).ncard) {k : Nat} (pos : 1 ≤ k)
    (arm : ∃ c,Nonempty (Arm G c k)) :
    ∃ l, k ≤ l ∧ ∃ c, 3 ≤ G.degree c ∧ Nonempty (Arm G c l) := by
  classical
  let nums := (Finset.range (Fintype.card V+1)).filter (fun t => ∃ c,Nonempty (Arm G c t))
  have mem {t} (ht : ∃ c, Nonempty (Arm G c t)) : t∈nums := by
    obtain ⟨c,⟨a⟩⟩ := ht
    have bd := Fintype.card_le_of_injective a.vertex a.vertex.injective
    simp only [Fintype.card_fin] at bd
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),c,⟨a⟩⟩
  let ne : nums.Nonempty := ⟨k,mem arm⟩
  let L := nums.max' ne
  have maximal : ∀ t, (∃ c, Nonempty (Arm G c t)) → t ≤ L := fun _ ht => Finset.le_max' _ _ (mem ht)
  have mk := maximal k arm
  obtain ⟨c,⟨a⟩⟩ := (Finset.mem_filter.mp (nums.max'_mem ne)).2
  refine ⟨L,mk,c,?_,⟨a⟩⟩
  by_contra! low
  have low' : (G.neighborSet c).ncard ≤ 2 := by rw [ncard_neighborSet_eq_degree];omega
  obtain ⟨t,e⟩ : ∃ t,L=t+1 := ⟨L-1,by omega⟩
  have ax : Nonempty (Arm G c (t+1)) := e ▸ ⟨a⟩
  obtain ⟨a'⟩ := ax
  obtain ⟨z,_,b,_,_⟩ := a'.extend conn branch low'
  have := maximal (t+2) ⟨z,⟨b⟩⟩
  omega

private lemma dist_bound {V : Type} [Fintype V] {G : SimpleGraph V} (conn : G.Connected)
    (x y : V) : G.dist x y ≤ G.diam := by
  have : Nonempty V := ⟨x⟩
  exact SimpleGraph.dist_le_diam (connected_iff_ediam_ne_top.mp conn)

private lemma Arm.radius_bound {V : Type} {G : SimpleGraph V} {c : V} (conn : G.Connected)
    (a : Arm G c (n+1)) (i) : G.dist c (a.vertex i) ≤ n+1 := by
  have b := a.internalNear 0 i
  have ad := G.dist_eq_one_iff_adj.mpr ((a.first 0).mpr rfl)
  have t := (conn c (a.vertex 0)).dist_triangle_left (a.vertex i)
  omega

private lemma shorten_diameter {V : Type} [Fintype V] {G : SimpleGraph V} {c : V}
    (tree : G.IsTree) (a : Arm G c (n+2)) (r : Nat) (big : r+1 ≤ n+2) (diam : G.diam = 2*r+1) :
    (G.induce {a.vertex (Fin.last (n+1))}ᶜ).diam ≤ 2*r := by
  classical
  let v := a.vertex (Fin.last (n+1))
  let K := G.induce {v}ᶜ
  let d : ({v}ᶜ : Set V) := ⟨c,(a.away _).symm⟩
  let b := a.shorten
  have kt := induce_compl_singleton_isTree_of_deg_one G tree a.tip_deg
  have dist := induce_compl_singleton_dist_eq G tree kt
  have long : G.dist v c = n+2 := G.dist_comm.trans (a.tip_dist tree)
  have len := dist_bound tree.connected v c
  have out (x : ({v}ᶜ : Set V)) (hx : x∉Set.range b.vertex) : K.dist d x + (n+2) ≤ 2*r+1 := by
    have notA : x.val ∉ Set.range a.vertex := by
      rintro ⟨j,e⟩
      refine Fin.lastCases (motive := fun j => a.vertex j=x.val → False) ?_ ?_ j e
      · intro e;exact x.property e.symm
      · intro i e;exact hx ⟨i,Subtype.ext e⟩
    have bound := dist_bound tree.connected v x.val
    have split := a.dist_outside tree.connected (Set.mem_range_self _) notA (x:=v)
    change (G.induce {v}ᶜ).dist d x + (n+2) ≤ 2*r+1
    rw [dist]
    change G.dist c x.val + (n+2) ≤ 2*r+1
    omega
  have : Nonempty ({v}ᶜ : Set V) := ⟨d⟩
  obtain ⟨x,y,ed⟩ := K.exists_dist_eq_diam
  have tri := (kt.connected x d).dist_triangle_left y
  rw [K.dist_comm (u:=x) (v:=d)] at tri
  change K.dist x y ≤ K.dist d x + K.dist d y at tri
  change K.diam ≤ 2*r
  by_cases hx : x∈Set.range b.vertex <;> by_cases hy : y∈Set.range b.vertex
  · obtain ⟨i,rfl⟩ := hx
    obtain ⟨j,rfl⟩ := hy
    have inside := b.internalNear i j
    change K.dist _ _ < n+1 at inside
    omega
  · obtain ⟨i,rfl⟩ := hx
    have l := b.radius_bound kt.connected i
    change K.dist d _ ≤ n+1 at l
    have := out y hy
    omega
  · obtain ⟨j,rfl⟩ := hy
    have l := b.radius_bound kt.connected j
    change K.dist d _ ≤ n+1 at l
    have := out x hx
    omega
  · have := out x hx;have := out y hy;omega

private lemma root_high_shorten {V : Type} [Fintype V] {G : SimpleGraph V} {c : V}
    (a : Arm G c (n+2)) (high : 3 ≤ G.degree c) :
    3 ≤ (G.induce {a.vertex (Fin.last (n+1))}ᶜ).degree ⟨c,(a.away _).symm⟩ := by
  have no : ¬G.Adj c (a.vertex (Fin.last (n+1))) := by
    rw [a.first];simp
  exact high.trans (degree_induce_compl_singleton_of_not_adj G (a.away _).symm no).ge

private lemma no_longer {V : Type} [Fintype V] {G : SimpleGraph V} (tr : G.IsTree)
    {c d : V} {k l r : Nat} (a : Arm G c (k+1)) (b : Arm G d (l+1))
    (ac : 3≤G.degree c) (bc : 3≤G.degree d) (big : r ≤ k+1) (D : G.diam ≤ 2*r) : l≤k := by
  rcases arm_alternatives tr a b ac bc with ⟨_,h⟩|dist
  · omega
  · have d := dist_bound tr.connected (b.vertex (Fin.last l)) (a.vertex (Fin.last k))
    omega

private theorem can_match {V : Type} [Fintype V] {G : SimpleGraph V} (tr : G.IsTree)
    {c d : V} {k r : Nat} (a : Arm G c (k+1)) (b : Arm G d (k+1))
    (ac : 3≤G.degree c) (bc : 3≤G.degree d) (big : r ≤ k+1) (D : G.diam ≤ 2*r) :
    ∃ f : G ≃g G, f (a.vertex (Fin.last k)) = b.vertex (Fin.last k) := by
  rcases arm_alternatives tr a b ac bc with ⟨e,_⟩|dist
  · exact ⟨SimpleGraph.Iso.refl,e⟩
  · have bound := dist_bound tr.connected (b.vertex (Fin.last k)) (a.vertex (Fin.last k))
    have z : G.dist c d=0 := by omega
    obtain rfl := tr.connected.dist_eq_zero_iff.mp z
    obtain ⟨f,_,eq⟩ := swap_or_same a b
    exact ⟨f,eq _⟩

private noncomputable def highCount {V : Type} [Fintype V] (G : SimpleGraph V) (d : Nat) : Nat :=
  ∑ x : V, if d ≤ G.degree x then 1 else 0

private noncomputable def Ncount {V : Type} [Fintype V] (G : SimpleGraph V) (v : V) (d : Nat) : Nat :=
  ∑ x : V, if G.Adj x v ∧ G.degree x=d then 1 else 0

private lemma threshold_deletion {V : Type} [Fintype V] (G : SimpleGraph V) (v : V) (d : Nat) :
    highCount G d = highCount (G.induce {v}ᶜ) d + Ncount G v d + (if d ≤ G.degree v then 1 else 0) := by
  classical
  let U := ({v}ᶜ : Set V)
  let p (x : V) : Nat := if d ≤ G.degree x then 1 else 0
  let q (x : V) : Nat := if G.Adj x v ∧ G.degree x=d then 1 else 0
  let h (x : U) : Nat := if d ≤ (G.induce {v}ᶜ).degree x then 1 else 0
  have dj (x : U) : p x.val = h x + q x.val := by
    dsimp only [p,h,q]
    by_cases ad : G.Adj x.val v
    · have drop := degree_induce_compl_singleton_of_adj G x.property ad
      change (G.induce {v}ᶜ).degree x + 1 = G.degree x.val at drop
      simp only [ad,true_and]
      split <;> split <;> split <;> omega
    · rw [degree_induce_compl_singleton_of_not_adj G x.property ad]
      simp [ad]
  have split (F : V → Nat) : (∑ x : V, F x) = (∑ x : U, F x.val) + F v := by
    let e : U ≃ {x : V // x ∈ (Finset.univ.erase v)} :=
      Equiv.subtypeEquivRight (fun x => by simp [U])
    have s := e.sum_comp (fun x => F x.val)
    have sub : (∑ x : U, F x.val) = ∑ x ∈ Finset.univ.erase v, F x := by
      rw [←Finset.sum_attach (Finset.univ.erase v) F]
      exact s
    rw [sub,Finset.sum_erase_add _ _ (Finset.mem_univ v)]
  have fs := split p
  have qs := split q
  have eq : (∑ x : U,p x.val) = (∑ x : U,h x) + ∑ x : U, q x.val := by
    simp only [←Finset.sum_add_distrib, dj]
  rw [eq] at fs
  have zv : q v = 0 := by simp [q]
  rw [zv,Nat.add_zero] at qs
  change (∑ x : V,p x) = (∑ x : U,h x) + (∑ x : V,q x) + p v
  omega

private lemma neighbor_histogram {V W : Type} [Fintype V] [Fintype W] (G : SimpleGraph V)
    (H : SimpleGraph W) (σ : V ≃ W) (degrees : ∀ v, G.degree v = H.degree (σ v))
    (v : V) (f : G.induce {v}ᶜ ≃g H.induce {σ v}ᶜ) (d : Nat) :
    Ncount G v d = Ncount H (σ v) d := by
  classical
  have global : highCount G d = highCount H d := by
    unfold highCount
    rw [← σ.sum_comp (fun w => if d ≤ H.degree w then 1 else 0)]
    simp only [degrees]
  have local' : highCount (G.induce {v}ᶜ) d = highCount (H.induce {σ v}ᶜ) d := by
    unfold highCount
    calc
      _ = ∑ x : ({v}ᶜ : Set V), (if d ≤ (H.induce {σ v}ᶜ).degree (f x) then 1 else 0) := by
        apply Finset.sum_congr (Finset.ext (by simp))
        intro x _
        simp only [f.degree_eq]
        congr!
      _ = _ := f.toEquiv.sum_comp (fun w => (if d ≤ (H.induce {σ v}ᶜ).degree w then 1 else 0 : Nat))
  have left := threshold_deletion G v d
  have right := threshold_deletion H (σ v) d
  rw [degrees] at left
  omega

private lemma Npos {V : Type} [Fintype V] (G : SimpleGraph V) (v : V) (d : Nat) :
    0 < Ncount G v d ↔ ∃ x, G.Adj x v ∧ G.degree x=d := by
  classical
  simp [Ncount,Finset.Nonempty]

private structure Island {V : Type*} (G : SimpleGraph V) (n : Nat) where
  v : Fin n ↪ V
  inside : ∀ i j, G.Adj (v i) (v j) ↔ i.val+1=j.val ∨ j.val+1=i.val
  closed : ∀ i x, G.Adj (v i) x → x ∈ Set.range v

private def Island.map {W : Type*} {H : SimpleGraph W} (p : Island G n) (f : G ≃g H) :
    Island H n where
  v := p.v.trans f.toEquiv.toEmbedding
  inside _ _ := f.map_adj_iff.trans (p.inside _ _)
  closed i x h := by
    have hx : G.Adj (p.v i) (f.symm x) := f.map_adj_iff.mp (by simpa using h)
    obtain ⟨j,e⟩ := p.closed i _ hx
    exact ⟨j,by simp [e]⟩

private def Arm.cut (a : Arm G c (n+3)) :
    Island (G.induce {a.vertex (⟨1,by omega⟩ : Fin (n+3))}ᶜ) (n+1) := by
  let step : Fin (n+3) := ⟨1,by omega⟩
  let tail (i : Fin (n+1)) : Fin (n+3) := ⟨i.val+2,by omega⟩
  let em : Fin (n+1) ↪ ({a.vertex step}ᶜ : Set V) :=
    ⟨fun i => ⟨a.vertex (tail i),fun h => by have e := congrArg Fin.val (a.vertex.injective h); dsimp [tail,step] at e; simp only [Nat.mod_eq_of_lt (show 1 < n+3 by omega)] at e;omega⟩,
      fun i j h => Fin.ext (by have e := congrArg Fin.val (a.vertex.injective (congrArg Subtype.val h));dsimp [tail] at e;omega)⟩
  refine ⟨em,?_,?_⟩
  · intro i j
    change G.Adj (a.vertex (tail i)) (a.vertex (tail j)) ↔ _
    rw [a.internal]
    dsimp [tail]
    omega
  · intro i x edge
    change G.Adj (a.vertex (tail i)) x.val at edge
    by_cases inside : x.val∈Set.range a.vertex
    · obtain ⟨j,e⟩ := inside
      rw [←e] at edge
      have h := (a.internal _ _).mp edge
      have ne : j.val≠1 := by
        intro j1
        have eq : j=step := Fin.ext j1
        exact x.property (e.symm.trans (congrArg a.vertex eq))
      dsimp [tail] at h
      let t : Fin (n+1) := ⟨j.val-2,by omega⟩
      refine ⟨t,Subtype.ext ((congrArg a.vertex ?_).trans e)⟩
      apply Fin.ext
      change j.val-2+2=j.val
      omega
    · have h := ((a.external _ _ inside).mp edge).1
      dsimp [tail] at h
      omega

private lemma Island.as_arm {V : Type} [Fintype V] (G : SimpleGraph V) (tree : G.IsTree)
    (w : V) (low : ∀ x, G.Adj x w → (G.neighborSet x).ncard ≤ 2)
    (p : Island (G.induce {w}ᶜ) (n+1)) : Nonempty (Arm G w (n+1)) := by
  classical
  let K := G.induce {w}ᶜ
  let C := K.connectedComponentMk (p.v 0)
  have supports (y) : y∈C.supp ↔ y∈Set.range p.v := by
    constructor
    · intro mem
      have start : p.v 0∈C.supp := ConnectedComponent.connectedComponentMk_mem
      obtain ⟨walk⟩ := C.reachable_of_mem_supp start mem
      have step {u v} (q : K.Walk u v) (um : u∈Set.range p.v) : v∈Set.range p.v := by
        induction q with
        | nil => exact um
        | cons edge _ ih => obtain ⟨i,rfl⟩ := um;exact ih (p.closed _ _ edge)
      exact step walk ⟨0,rfl⟩
    · rintro ⟨i,rfl⟩
      let hom : pathGraph (n+1) →g K :=
        { toFun := p.v
          map_rel' := fun {i j} h => (p.inside i j).mpr (pathGraph_adj.mp h) }
      exact ConnectedComponent.sound (((pathGraph_preconnected _ i 0).map hom))
  obtain ⟨root,⟨rs,ad⟩,unique⟩ := existsUnique_root_of_component G tree w C
  obtain ⟨j,ej⟩ := (supports root).mp rs
  have rootAdj (i) : G.Adj (p.v i).val w ↔ i=j := by
    constructor
    · intro h
      exact p.v.injective ((unique _ ⟨(supports _).mpr ⟨i,rfl⟩,h.symm⟩).trans ej.symm)
    · rintro rfl; simpa [ej] using ad.symm
  have endpt : j.val=0 ∨ j.val=n := by
    by_contra! ne
    let l : Fin (n+1) := ⟨j.val-1,by omega⟩
    let r : Fin (n+1) := ⟨j.val+1,by omega⟩
    have L : K.Adj (p.v j) (p.v l) := (p.inside _ _).mpr (Or.inr (by dsimp [l];omega))
    have R : K.Adj (p.v j) (p.v r) := (p.inside _ _).mpr (Or.inl rfl)
    have B := (rootAdj j).mpr rfl
    have lr : (p.v l).val ≠ (p.v r).val := by
      intro eq
      have t := congrArg Fin.val (p.v.injective (Subtype.ext eq));dsimp [l,r] at t;omega
    have many := (Set.two_lt_ncard_iff (Set.toFinite (G.neighborSet (p.v j).val))).mpr
      ⟨(p.v l).val,(p.v r).val,w,L,R,B,lr,(p.v l).property,(p.v r).property⟩
    have := low _ B
    omega
  let order : Fin (n+1) ≃ Fin (n+1) := if j=0 then Equiv.refl _ else Fin.revPerm
  have start : order 0 = j := by
    by_cases z : j=0
    · simp [order,z]
    · have jl : j.val=n := endpt.resolve_left (fun e => z (Fin.ext e))
      apply Fin.ext; simp [order,z,jl]
  have adj_order (i l) : ((order i).val+1=(order l).val ∨ (order l).val+1=(order i).val) ↔
      (i.val+1=l.val ∨ l.val+1=i.val) := by
    by_cases z : j=0
    · simp [order,z]
    · simp [order,z,Fin.rev];omega
  let em : Fin (n+1) ↪ V := (order.toEmbedding.trans p.v).trans (Function.Embedding.subtype _)
  refine ⟨⟨em,fun i => (p.v (order i)).property,?_,?_⟩⟩
  · intro i l
    exact (p.inside _ _).trans (adj_order _ _)
  · intro i x out
    by_cases eq : x=w
    · subst x
      change G.Adj (p.v (order i)).val w ↔ _
      rw [rootAdj,← start]
      constructor
      · intro h; exact ⟨congrArg Fin.val (order.injective h),rfl⟩
      · intro h; exact congrArg order (Fin.ext h.1)
    · have no : ¬G.Adj (em i) x := by
        intro h
        have hh : K.Adj (p.v (order i)) ⟨x,eq⟩ := h
        obtain ⟨l,el⟩ := p.closed _ _ hh
        exact out ⟨order.symm l,by change (p.v (order (order.symm l))).val=x;rw [order.apply_symm_apply];exact congrArg Subtype.val el⟩
      simp [no,eq]

private lemma transfer_three {V W : Type} [Fintype V] [Fintype W] {G : SimpleGraph V}
    {H : SimpleGraph W} (tr : H.IsTree) (σ : V ≃ W)
    (cards : ∀ v, Nonempty (G.induce {v}ᶜ ≃g H.induce {σ v}ᶜ))
    (deg : ∀ v, G.degree v=H.degree (σ v)) (br : ∃ x,3 ≤ (H.neighborSet x).ncard)
    {c : V} (a : Arm G c (n+3)) : ∃ z, Nonempty (Arm H z (n+3)) := by
  classical
  let cut := a.vertex (⟨1,by omega⟩ : Fin (n+3))
  have lowG (x) (h : G.Adj x cut) : G.degree x ≤ 2 := by
    by_cases mem : x∈Set.range a.vertex
    · obtain ⟨i,rfl⟩ := mem
      simpa only [ncard_neighborSet_eq_degree] using a.degree_bound i
    · have no := ((a.external (⟨1,by omega⟩ : Fin (n+3)) x mem).mp h.symm).1
      exact (by contradiction : False).elim
  let f := (cards cut).some
  have lowH (x) (h : H.Adj x (σ cut)) : (H.neighborSet x).ncard ≤ 2 := by
    have sizes := neighbor_histogram G H σ deg cut f (H.degree x)
    have pos := (Npos H (σ cut) (H.degree x)).mpr ⟨x,h,rfl⟩
    rw [←sizes] at pos
    obtain ⟨y,hy,dy⟩ := (Npos G cut (H.degree x)).mp pos
    rw [ncard_neighborSet_eq_degree,←dy]
    exact lowG _ hy
  let island := a.cut.map f
  obtain ⟨b⟩ := island.as_arm H tr (σ cut) lowH
  have cutSmall : (H.neighborSet (σ cut)).ncard ≤ 2 := by
    rw [ncard_neighborSet_eq_degree,←deg]
    simpa only [ncard_neighborSet_eq_degree] using a.degree_bound (⟨1,by omega⟩ : Fin (n+3))
  obtain ⟨y,cy,b',_,_⟩ := b.extend tr.connected br cutSmall
  obtain ⟨z,_,b'',_,_⟩ := b'.extend tr.connected br (lowH _ cy.symm)
  exact ⟨z,⟨b''⟩⟩

private lemma arm_leaf {V : Type} [Fintype V] {G : SimpleGraph V} {x y : V} (ad : G.Adj y x)
    (leaf : G.degree y=1) : Nonempty (Arm G x 1) := by
  obtain ⟨z,hz,unique⟩ := degree_eq_one_iff_existsUnique_adj.mp leaf
  have eq := unique x ad
  subst z
  let em : Fin 1 ↪ V := ⟨fun _ => y,fun _ _ _ => Subsingleton.elim _ _⟩
  refine ⟨⟨em,fun _ => ad.ne,?_,?_⟩⟩
  · intro i j
    have i0 : i=0 := Subsingleton.elim _ _
    have j0 : j=0 := Subsingleton.elim _ _
    simp [i0,j0,em]
  · intro i w _
    have i0 : i=0 := Subsingleton.elim _ _
    change G.Adj y w ↔ i.val=0 ∧ w=x
    constructor
    · intro h;exact ⟨congrArg Fin.val i0,unique _ h⟩
    · rintro ⟨_,rfl⟩;exact ad

private theorem transfer_any {V W : Type} [Fintype V] [Fintype W] {G : SimpleGraph V}
    {H : SimpleGraph W} (tr : H.IsTree) (σ : V ≃ W)
    (cards : ∀ v, Nonempty (G.induce {v}ᶜ ≃g H.induce {σ v}ᶜ))
    (deg : ∀ v, G.degree v=H.degree (σ v)) (br : ∃ x,3 ≤ (H.neighborSet x).ncard)
    {c : V} (a : Arm G c (n+2)) : ∃ z, Nonempty (Arm H z (n+2)) := by
  cases n with
  | succ n => exact transfer_three tr σ cards deg br a
  | zero =>
    let u := a.vertex 0
    let v := a.vertex (Fin.last 1)
    have ad : G.Adj v u := (a.internal _ _).mpr (Or.inr rfl)
    have left : 0<Ncount G u 1 := (Npos G u 1).mpr ⟨v,ad,a.tip_deg⟩
    rw [neighbor_histogram G H σ deg u (cards u).some 1] at left
    obtain ⟨w,edge,hdeg⟩ := (Npos H _ _).mp left
    obtain ⟨b⟩ := arm_leaf edge hdeg
    have tiny : (H.neighborSet (σ u)).ncard ≤ 2 := by
      rw [ncard_neighborSet_eq_degree,←deg]
      simpa only [ncard_neighborSet_eq_degree] using a.degree_bound 0
    obtain ⟨z,_,A,_,_⟩ := b.extend tr.connected br tiny
    exact ⟨z,⟨A⟩⟩

private lemma glue_unrooted {V W : Type} [Fintype V] [Fintype W] {G : SimpleGraph V}
    {H : SimpleGraph W} {c : V} {d : W} {r n : Nat} (a : Arm G c (n+2)) (b : Arm H d (n+2))
    (tg : G.IsTree) (dg : G.diam=2*r+1) (big : r+1 ≤ n+2) (cg : 3 ≤ G.degree c) (dh : 3 ≤ H.degree d)
    (f : G.induce {a.vertex (Fin.last (n+1))}ᶜ ≃g H.induce {b.vertex (Fin.last (n+1))}ᶜ) :
    Nonempty (G ≃g H) := by
  let A := a.shorten
  let B := b.shorten.map f.symm
  have tree := induce_compl_singleton_isTree_of_deg_one G tg a.tip_deg
  have dims := shorten_diameter tg a r big dg
  have highA := root_high_shorten a cg
  have highB : 3 ≤ (G.induce {a.vertex (Fin.last (n+1))}ᶜ).degree (f.symm ⟨d,(b.away _).symm⟩) :=
    (root_high_shorten b dh).trans (f.symm.degree_eq _).ge
  obtain ⟨g,im⟩ := can_match tree A B highA highB (by omega : r ≤ n+1) dims
  let e := g.trans f
  apply extend_card e
  intro x
  rw [a.tip_only,b.tip_only]
  let s := A.vertex (Fin.last n)
  let t := b.shorten.vertex (Fin.last n)
  have ee : e s=t := by
    change f (g s)=t
    change g s = f.symm t at im
    rw [im,f.apply_symm_apply]
  change x.val=s.val ↔ (e x).val=t.val
  rw [←Subtype.ext_iff,←Subtype.ext_iff,←ee]
  exact e.injective.eq_iff.symm

private lemma match_after_cut {V W : Type} [Fintype V] [Fintype W] {G : SimpleGraph V}
    {H : SimpleGraph W} {c : V} {d w : W} {r n m : Nat} (a : Arm G c (n+2)) (b : Arm H d (m+2))
    (tg : G.IsTree) (dg : G.diam=2*r+1) (big : r+1 ≤ n+2) (more : n ≤ m)
    (cg : 3 ≤ G.degree c) (dh : 3 ≤ H.degree d) (leaf : H.degree w=1)
    (f : G.induce {a.vertex (Fin.last (n+1))}ᶜ ≃g H.induce {w}ᶜ) :
    Nonempty (G ≃g H) := by
  let K := G.induce {a.vertex (Fin.last (n+1))}ᶜ
  let h := (⟨c,(a.away _).symm⟩ : ({a.vertex (Fin.last (n+1))}ᶜ : Set V))
  have tree : K.IsTree := induce_compl_singleton_isTree_of_deg_one G tg a.tip_deg
  have D : K.diam ≤ 2*r := shorten_diameter tg a r big dg
  have hhi : 3 ≤ K.degree h := root_high_shorten a cg
  have brK : ∃ x,3 ≤ (K.neighborSet x).ncard := ⟨h,by rwa [ncard_neighborSet_eq_degree]⟩
  have bound {L} {z} (B : Arm K z (L+1)) (high : 3 ≤ K.degree z) : L ≤ n :=
    no_longer tree a.shorten B hhi high (by omega : r ≤ n+1) D
  have same : w=b.vertex (Fin.last (m+1)) := by
    by_contra diff
    have out : w∉Set.range b.vertex := by
      rintro ⟨i,e⟩
      have hl : (H.neighborSet (b.vertex i)).ncard=1 := by rw [ncard_neighborSet_eq_degree,e,leaf]
      exact diff (e.symm.trans (congrArg b.vertex (b.low_tip i hl)))
    have nc : w ≠ d := by intro e;rw [e] at leaf;omega
    let kept := (b.keep nc out).map f.symm
    obtain ⟨L,le,z,high,B⟩ := large_anchored tree.connected brK (by omega : 1 ≤ m+2) ⟨_,⟨kept⟩⟩
    obtain ⟨j,rfl⟩ : ∃ j,L=j+1 := ⟨L-1,by omega⟩
    obtain ⟨B⟩ := B
    have := bound B high
    omega
  subst w
  let B := b.shorten.map f.symm
  have high : 3 ≤ K.degree (f.symm ⟨d,(b.away _).symm⟩) :=
    (root_high_shorten b dh).trans (f.symm.degree_eq _).ge
  have eq : m=n := Nat.le_antisymm (bound B high) more
  subst m
  exact glue_unrooted a b tg dg big cg dh f

private lemma one_sided {V W : Type} [Fintype V] [Fintype W] {G : SimpleGraph V}
    {H : SimpleGraph W} (tg : G.IsTree) (th : H.IsTree) (σ : V ≃ W)
    (cards : ∀ v, Nonempty (G.induce {v}ᶜ ≃g H.induce {σ v}ᶜ))
    (deg : ∀ v, G.degree v=H.degree (σ v)) (bg : ∃ x,3 ≤ (G.neighborSet x).ncard)
    (bh : ∃ x,3 ≤ (H.neighborSet x).ncard) {r} (ge : 1 ≤ r) (dg : G.diam=2*r+1)
    (long : ∃ c,Nonempty (Arm G c (r+1))) : Nonempty (G ≃g H) := by
  obtain ⟨L,large,c,cg,As⟩ := large_anchored tg.connected bg (by omega : 1 ≤ r+1) long
  obtain ⟨n,rfl⟩ : ∃ n, L=n+2 := ⟨L-2,by omega⟩
  obtain ⟨A⟩ := As
  have existsH := transfer_any th σ cards deg bh A
  obtain ⟨M,more,d,dh,Bs⟩ := large_anchored th.connected bh (by omega : 1 ≤ n+2) existsH
  obtain ⟨m,rfl⟩ : ∃ m,M=m+2 := ⟨M-2,by omega⟩
  obtain ⟨B⟩ := Bs
  let v := A.vertex (Fin.last (n+1))
  have hl : H.degree (σ v)=1 := (deg v).symm.trans A.tip_deg
  exact match_after_cut A B tg dg large (by omega) cg dh hl (cards v).some

private lemma induced_dist_eq {V : Type} (G : SimpleGraph V) (tr : G.IsTree) (S : Set V)
    (sub : (G.induce S).IsTree) (x y : S) : (G.induce S).dist x y = G.dist x.val y.val := by
  obtain ⟨p,path,len⟩ := sub.connected.exists_path_of_dist x y
  let h : G.induce S →g G := (SimpleGraph.Embedding.induce S).toHom
  have e := isTree_dist_eq_length_of_isPath G tr (p.map h) (path.map Subtype.val_injective)
  rwa [Walk.length_map,len] at e

private lemma full_path {V : Type} [Fintype V] (G : SimpleGraph V) (tr : G.IsTree) (c x : V)
    (r : Nat) (far : G.dist c x=r) (small : Fintype.card V ≤ r+1) :
    ∃ f : Fin (r+1) ≃ V, f 0 = c ∧ ∀ i j, G.Adj (f i) (f j) ↔ i.val+1=j.val ∨ j.val+1=i.val := by
  obtain ⟨p,path,len⟩ := tr.connected.exists_path_of_dist c x
  let f (i : Fin (r+1)) := p.getVert i.val
  have inj : Function.Injective f := fun i j h => Fin.ext <| path.getVert_injOn
    (show i.val ≤ p.length by omega) (show j.val ≤ p.length by omega) h
  have hcard := Fintype.card_le_of_injective f inj
  have onto := (Fintype.bijective_iff_injective_and_card f).mpr
    ⟨inj,by simpa using le_antisymm hcard (by simpa using small)⟩
  refine ⟨Equiv.ofBijective f onto,p.getVert_zero,?_⟩
  intro i j
  let idx (i : Fin (r+1)) : Fin p.support.length := ⟨i.val,by rw [p.length_support];omega⟩
  have eq (i) : p.support.get (idx i) = f i := p.support_getElem_eq_getVert (idx i).isLt
  change G.Adj (f i) (f j) ↔ _
  simpa only [eq,idx] using (shortest_induced p len).2 (idx i) (idx j)

private lemma side_arm {V : Type} [Fintype V] (G : SimpleGraph V) (tr : G.IsTree) (r : Nat)
    (diam : G.diam=2*r+1) (a b : V) (ab : G.Adj a b)
    (split : ∀ x, G.dist x a ≠ G.dist x b)
    (left : ∀ x, G.dist x a < G.dist x b → G.dist x a ≤ r)
    (right : ∀ x, G.dist x b < G.dist x a → G.dist x b ≤ r)
    (sub : (G.induce {x | G.dist x a < G.dist x b}).IsTree)
    (cross : ∀ x y, G.dist x a < G.dist x b → G.dist y b < G.dist y a →
      G.dist x y = G.dist x a + 1 + G.dist b y)
    (small : {x : V | G.dist x a < G.dist x b}.ncard ≤ r+1) :
    Nonempty (Arm G b (r+1)) := by
  classical
  let S := {x : V | G.dist x a < G.dist x b}
  have : Nonempty V := ⟨a⟩
  have opposed (u w : V) (far : G.dist u w=2*r+1) (uS : u∈S) (wS : w∈S) : False := by
    have l := left u uS
    have k := left w wS
    have t := (tr.connected u a).dist_triangle_left w
    rw [G.dist_comm (u:=a) (v:=w)] at t
    omega
  have findLeft : ∃ x∈S, G.dist a x=r := by
    obtain ⟨u,w,d⟩ := G.exists_dist_eq_diam
    have far := d.trans diam
    have solve (u w : V) (e : G.dist u w=2*r+1) (lu : u∈S) (rw' : G.dist w b < G.dist w a) :
        ∃ x∈S,G.dist a x=r := by
      refine ⟨u,lu,?_⟩
      have split' := cross u w lu rw'
      rw [G.dist_comm (u:=b) (v:=w)] at split'
      rw [G.dist_comm (u:=a) (v:=u)]
      have h := left u lu
      have k := right w rw'
      omega
    rcases lt_or_gt_of_ne (split u) with ul|ur <;> rcases lt_or_gt_of_ne (split w) with wl|wr
    · exact (opposed u w far ul wl).elim
    · exact solve u w far ul wr
    · exact solve w u (G.dist_comm.trans far) wl ur
    · have h := right u ur
      have k := right w wr
      have t := (tr.connected u b).dist_triangle_left w
      rw [G.dist_comm (u:=b) (v:=w)] at t
      omega
  have adist : G.dist a b = 1 := G.dist_eq_one_iff_adj.mpr ab
  have memA : a ∈ S := by change G.dist a a < G.dist a b;simp [adist]
  obtain ⟨x,hx,far⟩ := findLeft
  obtain ⟨f,start,internal⟩ := full_path (G.induce S) sub ⟨a,memA⟩ ⟨x,hx⟩ r
    ((induced_dist_eq G tr S sub _ _).trans far) (by rw [Set.fintypeCard_eq_ncard];exact small)
  let vertex : Fin (r+1) ↪ V := f.toEmbedding.trans (Function.Embedding.subtype _)
  have value (i) : vertex i = (f i).val := rfl
  have bs : b ∉ S := by change ¬G.dist b a < G.dist b b;simp
  have Srange : Set.range vertex=S := by
    ext y
    constructor
    · rintro ⟨i,rfl⟩; exact (f i).property
    · intro ys
      obtain ⟨i,e⟩ := f.surjective ⟨y,ys⟩
      exact ⟨i,congrArg Subtype.val e⟩
  have h0 : vertex 0=a := congrArg Subtype.val start
  refine ⟨⟨vertex,fun i h => bs (h ▸ (f i).property),internal,?_⟩⟩
  intro i y out
  rw [Srange] at out
  have ys : G.dist y b < G.dist y a := lt_of_le_of_ne (not_lt.mp out) (split y).symm
  have d := cross (vertex i) y (f i).property ys
  constructor
  · intro edge
    have ed := G.dist_eq_one_iff_adj.mpr edge
    have e₁ : G.dist (vertex i) a=0 := by omega
    have e₂ : G.dist b y=0 := by omega
    have va := tr.connected.dist_eq_zero_iff.mp e₁
    have iy := vertex.injective (va.trans h0.symm)
    exact ⟨congrArg Fin.val iy,(tr.connected.dist_eq_zero_iff.mp e₂).symm⟩
  · rintro ⟨i0,rfl⟩
    have : i=0 := Fin.ext i0
    rwa [this,h0]

private lemma small_either {V : Type} [Fintype V] (G : SimpleGraph V) (tree : G.IsTree) (r : Nat)
    (diam : G.diam=2*r+1) (a b : V) (ad : G.Adj a b) (neq : ∀ x,G.dist x a ≠ G.dist x b)
    (left : ∀ x,G.dist x a < G.dist x b → G.dist x a ≤ r)
    (right : ∀ x,G.dist x b < G.dist x a → G.dist x b ≤ r)
    (ls : (G.induce {x | G.dist x a < G.dist x b}).IsTree)
    (rs : (G.induce {x | G.dist x b < G.dist x a}).IsTree)
    (cross : ∀ x y, G.dist x a < G.dist x b → G.dist y b < G.dist y a →
      G.dist x y = G.dist x a + 1 + G.dist b y)
    (small : {x | G.dist x a < G.dist x b}.ncard ≤ r+1 ∨ {x | G.dist x b < G.dist x a}.ncard ≤ r+1) :
    ∃ z,Nonempty (Arm G z (r+1)) := by
  rcases small with l|h
  · exact ⟨b,side_arm G tree r diam a b ad neq left right ls cross l⟩
  · refine ⟨a,side_arm G tree r diam b a ad.symm (fun x => (neq x).symm) right left rs ?_ h⟩
    intro x y hx hy
    have k := cross y x hy hx
    rw [G.dist_comm (u:=y) (v:=x),G.dist_comm (u:=y) (v:=a),G.dist_comm (u:=b) (v:=x)] at k
    omega


end TreeArms
end OMA
namespace KellyStep9

section Solution
open SimpleGraph OMA.TreeArms Classical

theorem result : OMA.R_ReconstructionConjecture_reconstruction_conjecture_variants_tree_R1_H4_R1.H4 := by
  intro V W _ _ _ G H σ tg th cards degrees bg r pos dg dh _ a b ab _ neqG lG rG lsG rsG crossG
    c d cd _ neqH lH rH lsH rsH crossH small
  have deg (v) : G.degree v = H.degree (σ v) := by
    simpa only [ncard_neighborSet_eq_degree] using degrees v
  have bh : ∃ w,3 ≤ (H.neighborSet w).ncard := by
    obtain ⟨v,hi⟩ := bg
    exact ⟨σ v,by rwa [←degrees]⟩
  by_cases sg : {x | G.dist x a < G.dist x b}.ncard ≤ r+1 ∨ {x | G.dist x b < G.dist x a}.ncard ≤ r+1
  · exact one_sided tg th σ cards deg bg bh pos dg (small_either G tg r dg a b ab neqG lG rG lsG rsG crossG sg)
  · have sh : {x | H.dist x c < H.dist x d}.ncard ≤ r+1 ∨ {x | H.dist x d < H.dist x c}.ncard ≤ r+1 := by
      rcases small with h|h|h|h
      · exact (sg (Or.inl h)).elim
      · exact (sg (Or.inr h)).elim
      · exact Or.inl h
      · exact Or.inr h
    have rcards (w) : Nonempty (H.induce {w}ᶜ ≃g G.induce {σ.symm w}ᶜ) := by
      obtain ⟨v,rfl⟩ := σ.surjective w
      rw [σ.symm_apply_apply]
      exact ⟨(cards v).some.symm⟩
    have rdeg (w) : H.degree w = G.degree (σ.symm w) := by
      obtain ⟨v,rfl⟩ := σ.surjective w
      rw [σ.symm_apply_apply]
      exact (deg v).symm
    obtain ⟨iso⟩ := one_sided th tg σ.symm rcards rdeg bh bg pos dh
      (small_either H th r dh c d cd neqH lH rH lsH rsH crossH sh)
    exact ⟨iso.symm⟩

end Solution

end KellyStep9


/- # Reconstruction at a unique center with a large branch

The proof uses the deck of leaf-deleted trees, reconstructs the multiplicities
of rooted branch types, and handles the exceptional straight-arm configurations.
The geometric deck lemmas of @green-notes come from the project's earlier tree
proofs. The four cases, their assembly, and branch transport are due to @Deldor14.
-/

/-
# Large center components in even-diameter tree reconstruction

Call a leaf usable if deleting it preserves the diameter. Such cards retain
their root at the unique center. Separate the case in which every branch
survives some usable deletion from the case where one branch contains all
usable leaves. In the latter case the remaining branches are straight
peripheral paths. The two geometric conclusions distinguish a center of
degree two with a straight arm from trees whose outermost vertices all lie
on such arms.

Credit: @Deldor14. Parent reduction by @green-notes.
-/

namespace OMA.R_ReconstructionConjecture_reconstruction_conjecture_variants_tree_R1_H3_R1_H4_R1
open SimpleGraph

def H1 : Prop :=
  ∀ {V W : Type} [Fintype V] [Fintype W] (G : SimpleGraph V) (H : SimpleGraph W) (σ : V ≃ W),
    G.IsTree → H.IsTree →
    (∀ v, Nonempty (G.induce {v}ᶜ ≃g H.induce {σ v}ᶜ)) →
    (∀ v, (G.neighborSet v).ncard = (H.neighborSet (σ v)).ncard) →
    (∃ v, 3 ≤ (G.neighborSet v).ncard) →
    ∀ (r : Nat) (c : V) (d : W), 2 ≤ r → G.diam = 2*r → H.diam = 2*r →
    G.eccent c = r → H.eccent d = r →
    (∀ v, v ≠ c → (r : ℕ∞) < G.eccent v) → (∀ w, w ≠ d → (r : ℕ∞) < H.eccent w) →
    (G.neighborSet c).ncard = (H.neighborSet d).ncard →
    (∀ v, G.Adj c v → 2 ≤ (G.neighborSet v).ncard) →
    (∀ w, H.Adj d w → 2 ≤ (H.neighborSet w).ncard) →
    let covers := fun {X : Type} [Fintype X] (T : SimpleGraph X) (a : X) =>
      ∀ C : (T.induce {a}ᶜ).ConnectedComponent, ∃ v : ({a}ᶜ : Set X),
        v ∉ C.supp ∧ (T.neighborSet v.val).ncard=1 ∧ (T.induce {v.val}ᶜ).diam=2*r
    covers G c → covers H d → Nonempty (G ≃g H)

def H2 : Prop :=
  ∀ {V W : Type} [Fintype V] [Fintype W] (G : SimpleGraph V) (H : SimpleGraph W) (σ : V ≃ W),
    G.IsTree → H.IsTree →
    (∀ v, Nonempty (G.induce {v}ᶜ ≃g H.induce {σ v}ᶜ)) →
    (∀ v, (G.neighborSet v).ncard = (H.neighborSet (σ v)).ncard) →
    (∃ v, 3 ≤ (G.neighborSet v).ncard) →
    ∀ (r : Nat) (c : V) (d : W), 2 ≤ r → G.diam = 2*r → H.diam = 2*r →
    G.eccent c = r → H.eccent d = r →
    (∀ v, v ≠ c → (r : ℕ∞) < G.eccent v) → (∀ w, w ≠ d → (r : ℕ∞) < H.eccent w) →
    (G.neighborSet c).ncard = (H.neighborSet d).ncard →
    (∀ v, G.Adj c v → 2 ≤ (G.neighborSet v).ncard) →
    (∀ w, H.Adj d w → 2 ≤ (H.neighborSet w).ncard) →
    let covers := fun {X : Type} [Fintype X] (T : SimpleGraph X) (a : X) =>
      ∀ C : (T.induce {a}ᶜ).ConnectedComponent, ∃ v : ({a}ᶜ : Set X),
        v ∉ C.supp ∧ (T.neighborSet v.val).ncard=1 ∧ (T.induce {v.val}ᶜ).diam=2*r
    let pure := fun {X : Type} [Fintype X] (T : SimpleGraph X) (a : X) =>
      ∀ C : (T.induce {a}ᶜ).ConnectedComponent, (∃ v : C.supp, T.dist a v.val.val=r) → C.supp.ncard ≤ r
    let long := fun {X : Type} [Fintype X] (T : SimpleGraph X) (a : X) =>
      (T.neighborSet a).ncard=2 ∧ ∃ C : (T.induce {a}ᶜ).ConnectedComponent,
        (∃ v : C.supp, T.dist a v.val.val=r) ∧ C.supp.ncard ≤ r
    (¬ covers G c ∨ ¬ covers H d) → long G c ∨ long H d ∨ (pure G c ∧ pure H d)

def H3 : Prop :=
  ∀ {V W : Type} [Fintype V] [Fintype W] (G : SimpleGraph V) (H : SimpleGraph W) (σ : V ≃ W),
    G.IsTree → H.IsTree →
    (∀ v, Nonempty (G.induce {v}ᶜ ≃g H.induce {σ v}ᶜ)) →
    (∀ v, (G.neighborSet v).ncard = (H.neighborSet (σ v)).ncard) →
    (∃ v, 3 ≤ (G.neighborSet v).ncard) →
    ∀ (r : Nat) (c : V) (d : W), 2 ≤ r → G.diam = 2*r → H.diam = 2*r →
    G.eccent c = r → H.eccent d = r →
    let long := fun {X : Type} [Fintype X] (T : SimpleGraph X) (a : X) =>
      (T.neighborSet a).ncard=2 ∧ ∃ C : (T.induce {a}ᶜ).ConnectedComponent,
        (∃ v : C.supp, T.dist a v.val.val=r) ∧ C.supp.ncard ≤ r
    (long G c ∨ long H d) → Nonempty (G ≃g H)

def H4 : Prop :=
  ∀ {V W : Type} [Fintype V] [Fintype W] (G : SimpleGraph V) (H : SimpleGraph W) (σ : V ≃ W),
    G.IsTree → H.IsTree →
    (∀ v, Nonempty (G.induce {v}ᶜ ≃g H.induce {σ v}ᶜ)) →
    (∀ v, (G.neighborSet v).ncard = (H.neighborSet (σ v)).ncard) →
    (∃ v, 3 ≤ (G.neighborSet v).ncard) →
    ∀ (r : Nat) (c : V) (d : W), 2 ≤ r → G.diam = 2*r → H.diam = 2*r →
    G.eccent c = r → H.eccent d = r →
    (∀ v, v ≠ c → (r : ℕ∞) < G.eccent v) → (∀ w, w ≠ d → (r : ℕ∞) < H.eccent w) →
    (G.neighborSet c).ncard = (H.neighborSet d).ncard →
    (∀ v, G.Adj c v → 2 ≤ (G.neighborSet v).ncard) →
    (∀ w, H.Adj d w → 2 ≤ (H.neighborSet w).ncard) →
    let pure := fun {X : Type} [Fintype X] (T : SimpleGraph X) (a : X) =>
      ∀ C : (T.induce {a}ᶜ).ConnectedComponent, (∃ v : C.supp, T.dist a v.val.val=r) → C.supp.ncard ≤ r
    pure G c → pure H d → Nonempty (G ≃g H)

theorem main : H1 → H2 → H3 → H4 → OMA.R_ReconstructionConjecture_reconstruction_conjecture_variants_tree_R1_H3_R1.H4 := by
  classical
  intro h1 h2 h3 h4 V W _ _ _ G H σ tg th cards deg bg r c d hr dG dH eG eH uG uH _ dEq nG nH _
  have use₁ := h1 G H σ tg th cards deg bg r c d hr dG dH eG eH uG uH dEq nG nH
  have use₂ := h2 G H σ tg th cards deg bg r c d hr dG dH eG eH uG uH dEq nG nH
  have use₃ := h3 G H σ tg th cards deg bg r c d hr dG dH eG eH
  have use₄ := h4 G H σ tg th cards deg bg r c d hr dG dH eG eH uG uH dEq nG nH
  dsimp only at use₁ use₂ use₃ use₄
  by_cases g : ∀ C : (G.induce {c}ᶜ).ConnectedComponent, ∃ v : ({c}ᶜ : Set V),
      v ∉ C.supp ∧ (G.neighborSet v.val).ncard=1 ∧ (G.induce {v.val}ᶜ).diam=2*r
  · by_cases h : ∀ C : (H.induce {d}ᶜ).ConnectedComponent, ∃ v : ({d}ᶜ : Set W),
        v ∉ C.supp ∧ (H.neighborSet v.val).ncard=1 ∧ (H.induce {v.val}ᶜ).diam=2*r
    · exact use₁ g h
    · rcases use₂ (Or.inr h) with l|l|⟨p,q⟩
      · exact use₃ (Or.inl l)
      · exact use₃ (Or.inr l)
      · exact use₄ p q
  · rcases use₂ (Or.inl g) with l|l|⟨p,q⟩
    · exact use₃ (Or.inl l)
    · exact use₃ (Or.inr l)
    · exact use₄ p q

end OMA.R_ReconstructionConjecture_reconstruction_conjecture_variants_tree_R1_H3_R1_H4_R1

namespace LargeBranchCase1

/-
# Recovering the branches observed in diameter-preserving leaf cards

Count each rooted branch shape across the cards that preserve the diameter.
A branch contributes its original shape whenever the deleted leaf is outside
it. When the leaf is in the branch, its replacement has one fewer vertex.
The leaves eligible for such deletions are determined by the rooted shape
and by whether any leaf deletion decreases the diameter. Descending induction
on branch size therefore recovers all multiplicities.

Credit: @Deldor14. The tree distance, center and deletion lemmas are adapted
from @green-notes' proof of tree.R1.H3.R1.H2.
-/

end LargeBranchCase1
namespace OMA
namespace TreeArms
open SimpleGraph Classical

-- Tree deletion and distance lemmas adapted from @green-notes, tree.R1.H3.R1.H2.
private structure FinGraph where
  V : Type
  finite : Fintype V
  G : SimpleGraph V

private instance (P : FinGraph) : Fintype P.V := P.finite

private structure RootGraph extends FinGraph where
  root : V

private def rootRel (A B : RootGraph) : Prop := ∃ f : A.G ≃g B.G, f A.root=B.root

private instance : Setoid RootGraph where
  r := rootRel
  iseqv := by
    refine ⟨fun _ => ⟨SimpleGraph.Iso.refl,rfl⟩,?_,?_⟩
    · rintro A B ⟨f,e⟩
      exact ⟨f.symm,by rw [←e,f.symm_apply_apply]⟩
    · rintro A B C ⟨f,e⟩ ⟨g,e'⟩
      exact ⟨f.trans g,by change g (f A.root)=C.root;rw [e,e']⟩

private abbrev RootShape := Quotient (inferInstance : Setoid RootGraph)

private def rootShape {A : Type} [Fintype A] (S : SimpleGraph A) (a : A) : RootShape :=
  Quotient.mk _ ⟨⟨A,inferInstance,S⟩,a⟩

private lemma rootShape_iff {A B : Type} [Fintype A] [Fintype B] (S : SimpleGraph A) (a : A)
    (T : SimpleGraph B) (b : B) : rootShape S a = rootShape T b ↔ ∃ f : S ≃g T,f a=b := Quotient.eq

private noncomputable def rootSize : RootShape → Nat :=
  Quotient.lift (fun A : RootGraph => Fintype.card A.V) (fun _ _ h => by
    obtain ⟨f,_⟩ := h;exact Fintype.card_congr f.toEquiv)

private abbrev Branch {V : Type} (G : SimpleGraph V) (c : V) := (G.induce {c}ᶜ).ConnectedComponent

private noncomputable def attachment {V : Type} [Fintype V] {G : SimpleGraph V} (tree : G.IsTree)
    {c : V} (C : Branch G c) : C.supp :=
  ⟨(existsUnique_root_of_component G tree c C).choose,(existsUnique_root_of_component G tree c C).choose_spec.1.1⟩

private lemma is_attachment {V : Type} [Fintype V] {G : SimpleGraph V} (tree : G.IsTree)
    {c : V} (C : Branch G c) (v : C.supp) : G.Adj c v.val.val ↔ v=attachment tree C := by
  have unique := (existsUnique_root_of_component G tree c C).choose_spec
  constructor
  · intro h
    exact Subtype.ext (unique.2 v.val ⟨v.property,h⟩)
  · rintro rfl;exact unique.1.2

private noncomputable def branchShape {V : Type} [Fintype V] {G : SimpleGraph V} (tree : G.IsTree)
    {c : V} (C : Branch G c) := rootShape C.toSimpleGraph (attachment tree C)

private lemma join_components {A B : Type} {S : SimpleGraph A} {T : SimpleGraph B}
    (e : S.ConnectedComponent ≃ T.ConnectedComponent)
    (iso : ∀ C:S.ConnectedComponent, C.toSimpleGraph ≃g (e C).toSimpleGraph) :
    ∃ f:S ≃g T, ∀ C:S.ConnectedComponent,∀ x:C.supp,f x.val=(iso C x).val := by
  let map (x : A) := (iso (S.connectedComponentMk x) ⟨x,rfl⟩).val
  have apply_at (C : S.ConnectedComponent) (x : C.supp) : map x.val = (iso C x).val := by
    obtain ⟨x,hx⟩ := x
    change S.connectedComponentMk x=C at hx
    subst C
    rfl
  have tag (x) : T.connectedComponentMk (map x) = e (S.connectedComponentMk x) :=
    (iso _ ⟨x,rfl⟩).property
  have inj : Function.Injective map := by
    intro x y eq
    have same : S.connectedComponentMk x=S.connectedComponentMk y :=
      e.injective ((tag x).symm.trans ((congrArg T.connectedComponentMk eq).trans (tag y)))
    let C := S.connectedComponentMk x
    let u : C.supp := ⟨x,rfl⟩
    let v : C.supp := ⟨y,same.symm⟩
    have same' := (apply_at C u).symm.trans (eq.trans (apply_at C v))
    exact congrArg Subtype.val ((iso C).injective (Subtype.ext same'))
  have onto : Function.Surjective map := by
    intro y
    obtain ⟨C,eq⟩ := e.surjective (T.connectedComponentMk y)
    let v : (e C).supp := ⟨y,eq.symm⟩
    obtain ⟨x,h⟩ := (iso C).surjective v
    exact ⟨x.val,(apply_at C x).trans (congrArg Subtype.val h)⟩
  have ad (x y) : T.Adj (map x) (map y) ↔ S.Adj x y := by
    by_cases same : S.connectedComponentMk x=S.connectedComponentMk y
    · let C := S.connectedComponentMk x
      let u : C.supp := ⟨x,rfl⟩
      let v : C.supp := ⟨y,same.symm⟩
      rw [show map x = _ from apply_at C u,show map y = _ from apply_at C v]
      exact (iso C).map_adj_iff
    · have l : ¬S.Adj x y := fun adj => same (ConnectedComponent.connectedComponentMk_eq_of_adj adj)
      have r : ¬T.Adj (map x) (map y) := fun adj =>
        same (e.injective ((tag x).symm.trans ((ConnectedComponent.connectedComponentMk_eq_of_adj adj).trans (tag y))))
      exact iff_of_false r l
  exact ⟨⟨Equiv.ofBijective map ⟨inj,onto⟩,fun {x y} => ad x y⟩,apply_at⟩

private lemma trees_of_equal_branches {V W : Type} [Fintype V] [Fintype W] {G : SimpleGraph V}
    {H : SimpleGraph W} (tg : G.IsTree) (th : H.IsTree) {c : V} {d : W}
    (M : ∀ q : RootShape, Fintype.card {C : Branch G c // branchShape tg C=q} =
      Fintype.card {D : Branch H d // branchShape th D=q}) : Nonempty (G ≃g H) := by
  classical
  let matching (q : RootShape) := (Fintype.card_eq.mp (M q)).some
  let e : Branch G c ≃ Branch H d := Equiv.ofFiberEquiv matching
  have good (C : Branch G c) : branchShape tg C=branchShape th (e C) := (Equiv.ofFiberEquiv_map matching C).symm
  have rootMatch (C : Branch G c) :
      ∃ f:C.toSimpleGraph ≃g (e C).toSimpleGraph,f (attachment tg C)=attachment th (e C) :=
    (rootShape_iff _ _ _ _).mp (good C)
  choose iso rootIso using rootMatch
  obtain ⟨f,apply_at⟩ := join_components e iso
  apply extend_card f
  intro x
  let C := (G.induce {c}ᶜ).connectedComponentMk x
  let v : C.supp := ⟨x,rfl⟩
  rw [show f x = _ from apply_at C v]
  change G.Adj c v.val.val ↔ H.Adj d (iso C v).val.val
  rw [is_attachment tg C v,is_attachment th (e C) (iso C v),←rootIso]
  exact (iso C).injective.eq_iff.symm

private def restrict_iso {V W : Type} {G : SimpleGraph V} {H : SimpleGraph W}
    (f : G ≃g H) (S : Set V) (T : Set W) (h : ∀ x,x∈S ↔ f x∈T) : G.induce S ≃g H.induce T :=
  ⟨f.toEquiv.subtypeEquiv h,fun {_ _} => f.map_adj_iff⟩

private theorem iso_preserves_branches {V W : Type} [Fintype V] [Fintype W] {G : SimpleGraph V}
    {H : SimpleGraph W} (tg : G.IsTree) (th : H.IsTree) {c : V} {d : W} (f : G ≃g H) (eq : f c=d) :
    ∃ e:Branch G c ≃ Branch H d,∀ C,branchShape tg C=branchShape th (e C) := by
  subst d
  let g := restrict_iso f {c}ᶜ {f c}ᶜ (fun x => by simp)
  let e := g.connectedComponentEquiv
  refine ⟨e,fun C => ?_⟩
  let a := restrict_iso g C.supp (e C).supp (fun x => (ConnectedComponent.iso_image_comp_eq_map_iff_eq_comp (φ:=g)).symm)
  apply (rootShape_iff _ _ _ _).mpr
  refine ⟨a,(is_attachment th (e C) (a (attachment tg C))).mp ?_⟩
  change H.Adj (f c) (f (attachment tg C).val.val)
  exact f.map_adj_iff.mpr ((is_attachment tg C _).mpr rfl)

private lemma dist_through_center {V : Type} (T : SimpleGraph V) (hT : T.IsTree)
    (c : V) {a b : ({c}ᶜ : Set V)}
    (hne : (T.induce {c}ᶜ).connectedComponentMk a ≠ (T.induce {c}ᶜ).connectedComponentMk b) :
    T.dist a.val b.val = T.dist c a.val + T.dist c b.val := by
  obtain ⟨p, hp, hlen⟩ := hT.connected.exists_path_of_dist a.val b.val
  have hcmem : c ∈ p.support := by
    by_contra h
    have hs : ∀ x ∈ p.support, x ∈ ({c}ᶜ : Set V) := by
      rintro x hx rfl
      exact h hx
    exact hne (ConnectedComponent.sound ⟨p.induce _ hs⟩)
  obtain ⟨q, s, hq, hs, hqs⟩ := hp.mem_support_iff_exists_append.mp hcmem
  rw [← hlen, hqs, Walk.length_append, isTree_dist_eq_length_of_isPath T hT q hq,
    isTree_dist_eq_length_of_isPath T hT s hs, (T.dist_comm (u := a.val) (v := c))]

-- The endpoint construction follows @green-notes, tree.R1.H3.R1.H2.

private def forgetPart {V : Type} (G : SimpleGraph V) (c : V) (C : Branch G c) : C.toSimpleGraph ↪g G where
  toFun x := x.val.val
  inj' _ _ h := Subtype.ext (Subtype.ext h)
  map_rel_iff' := Iff.rfl

private lemma br_dist {V : Type} [Fintype V] {G : SimpleGraph V} (tg : G.IsTree)
    {c : V} (C : Branch G c) (x y : C.supp) :
    C.toSimpleGraph.dist x y = G.dist x.val.val y.val.val := by
  obtain ⟨p,path,len⟩ := C.connected_toSimpleGraph.exists_path_of_dist x y
  have e := isTree_dist_eq_length_of_isPath G tg (p.map (forgetPart G c C).toHom) (path.map (forgetPart _ _ _).injective)
  rwa [Walk.length_map,len] at e

private lemma root_dist {V : Type} [Fintype V] {G : SimpleGraph V} (tg : G.IsTree)
    {c : V} (C : Branch G c) (x : C.supp) :
    G.dist c x.val.val = C.toSimpleGraph.dist (attachment tg C) x + 1 := by
  obtain ⟨p,path,len⟩ := C.connected_toSimpleGraph.exists_path_of_dist (attachment tg C) x
  let e := forgetPart G c C
  let q := p.map e.toHom
  have edge : G.Adj c (e (attachment tg C)) := (is_attachment tg C _).mpr rfl
  have qpath : q.IsPath := path.map e.injective
  have away : c∉q.support := by
    rw [Walk.support_map,List.mem_map];rintro ⟨z,_,eq⟩;exact z.val.property eq
  have full := isTree_dist_eq_length_of_isPath G tg (q.cons edge) ((Walk.cons_isPath_iff ..).mpr ⟨qpath,away⟩)
  change G.dist c (e.toHom x) = _
  rw [←full,Walk.length_cons,Walk.length_map,len]

private lemma rad_essential {X I : Type} (P : X → Prop) (f : X → I)
    (pair : ∃ a b,P a ∧ P b ∧ f a≠f b) :
    let E := fun x => ∀ a b,P a → P b → f a≠f b → x=a ∨ x=b
    ∀ x, E x ↔ (∃ z,E z) ∧ P x ∧ ∀ y,P y → f y=f x → y=x := by
  dsimp only
  intro x
  constructor
  · intro ex
    obtain ⟨a,b,pa,pb,ab⟩ := pair
    refine ⟨⟨x,ex⟩,?_,?_⟩
    · rcases ex a b pa pb ab with rfl|rfl <;> assumption
    · intro y py same
      rcases ex a b pa pb ab with rfl|rfl
      · exact ((ex y b py pb (same ▸ ab)).resolve_right (fun h => ab (congrArg f h))).symm
      · exact ((ex a y pa py (same ▸ ab)).resolve_left (fun h => ab (congrArg f h.symm))).symm
  · rintro ⟨⟨z,ez⟩,px,unique⟩ a b pa pb ab
    by_contra! neq
    have ax : f a≠f x := fun e => neq.1 (unique a pa e).symm
    have bx : f b≠f x := fun e => neq.2 (unique b pb e).symm
    rcases ez a b pa pb ab with rfl|rfl
    · rcases ez b x pb px bx with eq|eq
      · exact ab (congrArg f eq)
      · exact neq.1 eq.symm
    · rcases ez a x pa px ax with eq|eq
      · exact ab (congrArg f eq.symm)
      · exact neq.2 eq.symm

private lemma far_pair {V : Type} [Fintype V] {G : SimpleGraph V} (tg : G.IsTree)
    {c : V} {r : Nat} (upper : ∀ x,G.dist c x ≤ r) (a b : ({c}ᶜ : Set V)) :
    G.dist a.val b.val=2*r ↔ G.dist c a.val=r ∧ G.dist c b.val=r ∧
      (G.induce {c}ᶜ).connectedComponentMk a ≠ (G.induce {c}ᶜ).connectedComponentMk b := by
  constructor
  · intro far
    have tri := (tg.connected a.val c).dist_triangle_left b.val
    rw [G.dist_comm (u:=a.val) (v:=c)] at tri
    have ua := upper a.val
    have ub := upper b.val
    refine ⟨by omega,by omega,?_⟩
    intro e
    let C := (G.induce {c}ᶜ).connectedComponentMk a
    let x : C.supp := ⟨a,rfl⟩
    let y : C.supp := ⟨b,e.symm⟩
    have l := root_dist tg C x
    have k := root_dist tg C y
    change G.dist c a.val = _ at l
    change G.dist c b.val = _ at k
    have path := (C.connected_toSimpleGraph x (attachment tg C)).dist_triangle_left y
    rw [br_dist tg C x y,C.toSimpleGraph.dist_comm (u:=x) (v:=attachment tg C)] at path
    change G.dist a.val b.val ≤ _ at path
    omega
  · rintro ⟨la,lb,diff⟩
    rw [dist_through_center G tg c diff,la,lb];omega

private lemma length_walk_induce {U : Type*} (T : SimpleGraph U) (S : Set U) {a b : U}
    (p : T.Walk a b) (hp : ∀ x ∈ p.support, x ∈ S) :
    (p.induce S hp).length = p.length := by
  have h := congrArg Walk.length (Walk.map_induce p hp)
  rwa [Walk.length_map] at h

private lemma induce_compl_singleton_diam_le {U : Type} [Fintype U]
    (T : SimpleGraph U) (hT : T.IsTree) {v : U} (hdeg1 : T.degree v = 1) :
    (T.induce {v}ᶜ).diam ≤ T.diam := by
  have : Nonempty U := hT.connected.nonempty
  have hT' : (T.induce {v}ᶜ).IsTree := induce_compl_singleton_isTree_of_deg_one T hT hdeg1
  have : Nonempty ({v}ᶜ : Set U) := hT'.connected.nonempty
  obtain ⟨a, b, hab⟩ := (T.induce {v}ᶜ).exists_dist_eq_diam
  rw [← hab, induce_compl_singleton_dist_eq T hT hT']
  exact dist_le_diam (connected_iff_ediam_ne_top.mp hT.connected)

private lemma good_leaf_of_ne_diam_ends {U : Type} [Fintype U] (T : SimpleGraph U) (hT : T.IsTree)
    {r : ℕ} (_hr : 2 ≤ r) (hdiam : T.diam = 2 * r) {x0 xd : U} (hxd : T.dist x0 xd = 2 * r)
    {v : U} (hv1 : T.degree v = 1) (hx0 : v ≠ x0) (hxd_ne : v ≠ xd) :
    (T.induce {v}ᶜ).diam = 2 * r := by
  obtain ⟨p, hp, hplen⟩ := hT.connected.exists_path_of_dist x0 xd
  have hnot : v ∉ p.support := by
    intro hv_mem
    obtain ⟨q, s, hq, hs, hp_eq⟩ := hp.mem_support_iff_exists_append.mp hv_mem
    have hq_nn : ¬ q.Nil := Walk.not_nil_of_ne hx0.symm
    have hs_nn : ¬ s.Nil := Walk.not_nil_of_ne hxd_ne
    have hadj1 : T.Adj v q.penultimate := (q.adj_penultimate hq_nn).symm
    have hadj2 : T.Adj v s.snd := s.adj_snd hs_nn
    have hne12 : q.penultimate ≠ s.snd := by
      have hdisj : q.support.Disjoint s.tail.support := by
        have h1 := (hp_eq ▸ hp).support_nodup
        rw [Walk.support_append, List.nodup_append', ← Walk.support_tail_of_not_nil s hs_nn] at h1
        exact h1.2.2
      have hm1 : q.penultimate ∈ q.support := Walk.getVert_mem_support q (q.length - 1)
      have hm2 : s.snd ∈ s.tail.support := by
        rw [Walk.support_tail_of_not_nil s hs_nn]
        exact s.snd_mem_tail_support hs_nn
      intro heq
      rw [heq] at hm1
      exact hdisj hm1 hm2
    have h2 : 2 ≤ T.degree v := by
      rw [← T.card_neighborFinset_eq_degree]
      have hsub : {q.penultimate, s.snd} ⊆ T.neighborFinset v := by
        intro z hz
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rw [SimpleGraph.mem_neighborFinset]
        rcases hz with rfl | rfl <;> assumption
      calc
        2 = ({q.penultimate, s.snd} : Finset U).card := (Finset.card_pair hne12).symm
        _ ≤ (T.neighborFinset v).card := Finset.card_le_card hsub
    omega
  have hw_supp : ∀ x ∈ p.support, x ∈ ({v}ᶜ : Set U) := fun x hx =>
    Set.mem_compl_singleton_iff.mpr fun heq => hnot (heq ▸ hx)
  let p' := p.induce ({v}ᶜ : Set U) hw_supp
  have hp' : p'.IsPath := by
    refine Walk.IsPath.of_map (f := (SimpleGraph.Embedding.induce ({v}ᶜ : Set U)).toHom) ?_
    rw [Walk.map_induce]
    exact hp
  have hT' : (T.induce {v}ᶜ).IsTree := induce_compl_singleton_isTree_of_deg_one T hT hv1
  have : Nonempty ({v}ᶜ : Set U) := hT'.connected.nonempty
  have hdist : (T.induce {v}ᶜ).dist ⟨x0, hw_supp x0 p.start_mem_support⟩
      ⟨xd, hw_supp xd p.end_mem_support⟩ = 2 * r := by
    have h1 := isTree_dist_eq_length_of_isPath (T.induce {v}ᶜ) hT' p' hp'
    rw [← h1, length_walk_induce, hplen, hxd]
  have hediam' : (T.induce {v}ᶜ).ediam ≠ ⊤ := connected_iff_ediam_ne_top.mp hT'.connected
  have hge : 2 * r ≤ (T.induce {v}ᶜ).diam := hdist ▸ dist_le_diam hediam'
  have hle : (T.induce {v}ᶜ).diam ≤ 2 * r := hdiam ▸ induce_compl_singleton_diam_le T hT hv1
  omega

private lemma component_toSimpleGraph_degree {U : Type} [Fintype U]
    (T : SimpleGraph U) (c : U) (C : (T.induce {c}ᶜ).ConnectedComponent) (x : C.supp) :
    C.toSimpleGraph.degree x = (T.induce {c}ᶜ).degree x.1 := by
  let f : C.supp ↪ ({c}ᶜ : Set U) := ⟨Subtype.val, Subtype.val_injective⟩
  have heq : (C.toSimpleGraph.neighborFinset x).map f = (T.induce {c}ᶜ).neighborFinset x.1 := by
    ext y
    rw [Finset.mem_map, SimpleGraph.mem_neighborFinset]
    constructor
    · rintro ⟨z, hz, rfl⟩
      rw [SimpleGraph.mem_neighborFinset] at hz
      exact hz
    · intro hxy
      have hy : y ∈ C.supp := C.mem_supp_of_adj_mem_supp x.2 hxy
      refine ⟨⟨y, hy⟩, ?_, rfl⟩
      rw [SimpleGraph.mem_neighborFinset]
      exact hxy
  have hcard := congrArg Finset.card heq
  rw [Finset.card_map, C.toSimpleGraph.card_neighborFinset_eq_degree,
    (T.induce {c}ᶜ).card_neighborFinset_eq_degree] at hcard
  exact hcard


private def badFlag {V : Type} [Fintype V] (G : SimpleGraph V) (r : Nat) : Prop :=
  ∃ v, G.degree v=1 ∧ (G.induce {v}ᶜ).diam≠2*r

private lemma bad_iff_extreme {V : Type} [Fintype V] {G : SimpleGraph V} (tree : G.IsTree)
    {c : V} {r : Nat} (hr : 2≤r) (diam : G.diam=2*r) (upper : ∀ x,G.dist c x≤r)
    (v : ({c}ᶜ : Set V)) (hv : G.degree v.val=1) :
    (G.induce {v.val}ᶜ).diam≠2*r ↔
      ∀ a b : ({c}ᶜ : Set V),G.dist c a.val=r → G.dist c b.val=r →
        (G.induce {c}ᶜ).connectedComponentMk a ≠ (G.induce {c}ᶜ).connectedComponentMk b →
        v=a ∨ v=b := by
  constructor
  · intro bad a b pa pb diff
    by_contra! h
    exact bad (good_leaf_of_ne_diam_ends G tree hr diam ((far_pair tree upper a b).mpr ⟨pa,pb,diff⟩)
      hv (fun e => h.1 (Subtype.ext e)) (fun e => h.2 (Subtype.ext e)))
  · intro essential good
    have tree' := induce_compl_singleton_isTree_of_deg_one G tree hv
    have : Nonempty ({v.val}ᶜ : Set V) := tree'.connected.nonempty
    obtain ⟨x,y,e⟩ := (G.induce {v.val}ᶜ).exists_dist_eq_diam
    have far : G.dist x.val y.val=2*r := (induce_compl_singleton_dist_eq G tree tree' x y).symm.trans (e.trans good)
    have xa : x.val≠c := by intro e;rw [e] at far;have := upper y.val;omega
    have ya : y.val≠c := by intro e;rw [e,G.dist_comm] at far;have := upper x.val;omega
    let a : ({c}ᶜ : Set V) := ⟨x.val,xa⟩
    let b : ({c}ᶜ : Set V) := ⟨y.val,ya⟩
    obtain ⟨pa,pb,diff⟩ := (far_pair tree upper a b).mp far
    rcases essential a b pa pb diff with vx|vy
    · exact x.property (congrArg Subtype.val vx).symm
    · exact y.property (congrArg Subtype.val vy).symm

private def usable {V : Type} [Fintype V] (T : SimpleGraph V) (a : V) (r : Nat) (bad : Prop) (x : V) : Prop :=
  x≠a ∧ T.degree x=1 ∧
    ¬(bad ∧ T.dist a x+1=r ∧ ∀ y,T.dist a y+1=r → y=x)

private lemma intrinsic_usable {V : Type} [Fintype V] {G : SimpleGraph V} (tree : G.IsTree)
    {c : V} {r : Nat} (hr : 2≤r) (diam : G.diam=2*r) (upper : ∀ x,G.dist c x≤r)
    (center : ∀ v,G.degree v=1 → v≠c) (nol : ∀ v,G.Adj c v → 2 ≤ (G.neighborSet v).ncard)
    (pair : ∃ a b : ({c}ᶜ : Set V),G.dist c a.val=r ∧ G.dist c b.val=r ∧
      (G.induce {c}ᶜ).connectedComponentMk a ≠ (G.induce {c}ᶜ).connectedComponentMk b)
    (C : Branch G c) (x : C.supp) :
    (G.degree x.val.val=1 ∧ (G.induce {x.val.val}ᶜ).diam=2*r) ↔
      usable C.toSimpleGraph (attachment tree C) r (badFlag G r) x := by
  let P (a : ({c}ᶜ : Set V)) := G.dist c a.val=r
  let f := (G.induce {c}ᶜ).connectedComponentMk
  have ext := rad_essential P f pair x.val
  have reduce (leaf : G.degree x.val.val=1) :
      (G.induce {x.val.val}ᶜ).diam≠2*r ↔ badFlag G r ∧
        C.toSimpleGraph.dist (attachment tree C) x+1=r ∧
        ∀ y,C.toSimpleGraph.dist (attachment tree C) y+1=r → y=x := by
    rw [bad_iff_extreme tree hr diam upper x.val leaf]
    change (∀ a b,P a → P b → f a≠f b → x.val=a ∨ x.val=b) ↔ _
    refine ext.trans ?_
    constructor
    · rintro ⟨z,px,one⟩
      have essential := ext.mpr ⟨z,px,one⟩
      refine ⟨⟨x.val.val,leaf,(bad_iff_extreme tree hr diam upper x.val leaf).mpr essential⟩,?_,?_⟩
      · exact (root_dist tree C x).symm.trans px
      · intro y py
        apply Subtype.ext
        exact one y.val ((root_dist tree C y).trans py) (y.property.trans x.property.symm)
    · rintro ⟨⟨u,du,bad⟩,px,one⟩
      let u' : ({c}ᶜ : Set V) := ⟨u,center u du⟩
      refine ⟨⟨u',(bad_iff_extreme tree hr diam upper u' du).mp bad⟩,(root_dist tree C x).trans px,?_⟩
      intro y py sy
      let y' : C.supp := ⟨y,sy.trans x.property⟩
      exact congrArg Subtype.val (one y' ((root_dist tree C y').symm.trans py))
  have degree (ne : x≠attachment tree C) : C.toSimpleGraph.degree x=G.degree x.val.val := by
    rw [component_toSimpleGraph_degree]
    exact degree_induce_compl_singleton_of_not_adj G x.val.property (fun h => ne ((is_attachment tree C x).mp h.symm))
  constructor
  · rintro ⟨leaf,good⟩
    have ne : x≠attachment tree C := by
      intro eq
      have d := nol _ ((is_attachment tree C x).mpr eq)
      rw [ncard_neighborSet_eq_degree,leaf] at d
      omega
    exact ⟨ne,(degree ne).trans leaf,fun h => (reduce leaf).mpr h good⟩
  · rintro ⟨ne,low,h⟩
    have leaf := (degree ne).symm.trans low
    exact ⟨leaf,Classical.byContradiction (fun bad => h ((reduce leaf).mp bad))⟩

private lemma reachable_delete_leaf {V : Type} [Fintype V] (G : SimpleGraph V) {v : V} (hv : G.degree v=1)
    (x y : ({v}ᶜ : Set V)) (reach : G.Reachable x.val y.val) : (G.induce {v}ᶜ).Reachable x y := by
  classical
  obtain ⟨u,adj,unique⟩ := degree_eq_one_iff_existsUnique_adj.mp hv
  obtain ⟨p⟩ := reach
  let q := p.toPath
  refine ⟨(q.val.induce {v}ᶜ ?_).copy (Subtype.ext rfl) (Subtype.ext rfl)⟩
  intro z hz
  change z≠v
  rintro rfl
  obtain ⟨l,r,lr⟩ := Walk.mem_support_iff_exists_append.mp hz
  apply List.nodup_iff_forall_not_duplicate.mp q.nodup_support u
  rw [lr,Walk.support_append,List.duplicate_iff_two_le_count,List.count_append]
  have L := List.one_le_count_iff.mpr (l.getVert_mem_support (l.length-1))
  have ny : z≠y.val := Ne.symm (show y.val≠z from y.property)
  change 1 ≤ l.support.count l.penultimate at L
  have R := List.one_le_count_iff.mpr (r.snd_mem_tail_support (Walk.not_nil_of_ne ny))
  rw [unique _ (l.adj_penultimate (Walk.not_nil_of_ne x.property)).symm] at L
  rw [unique _ (r.adj_snd (Walk.not_nil_of_ne ny))] at R
  omega

private noncomputable def unclipCC {V : Type} [Fintype V] (G : SimpleGraph V) {v : V} (leaf : G.degree v=1) :
    (G.induce {v}ᶜ).ConnectedComponent ≃ G.ConnectedComponent := by
  let j : G.induce {v}ᶜ →g G := (SimpleGraph.Embedding.induce _).toHom
  let f (C : (G.induce {v}ᶜ).ConnectedComponent) := C.map j
  refine Equiv.ofBijective f ⟨?_,?_⟩
  · intro C D
    refine C.ind (fun x => D.ind (fun y eq => ?_))
    apply ConnectedComponent.sound
    apply reachable_delete_leaf G leaf
    exact ConnectedComponent.exact eq
  · intro C
    refine C.ind (fun x => ?_)
    by_cases e : x=v
    · subst x
      obtain ⟨y,h,_⟩ := degree_eq_one_iff_existsUnique_adj.mp leaf
      refine ⟨(G.induce {v}ᶜ).connectedComponentMk ⟨y,h.ne.symm⟩,?_⟩
      exact ConnectedComponent.sound h.symm.reachable
    · exact ⟨(G.induce {v}ᶜ).connectedComponentMk ⟨x,e⟩,rfl⟩

private def commute_delete {V : Type} (G : SimpleGraph V) {c v : V} (ne : c≠v) :
    (G.induce {v}ᶜ).induce {(⟨c,ne⟩ : ({v}ᶜ : Set V))}ᶜ ≃g
    (G.induce {c}ᶜ).induce {(⟨v,ne.symm⟩ : ({c}ᶜ : Set V))}ᶜ where
  toFun x := ⟨⟨x.val.val,fun e => x.property (Subtype.ext e)⟩,fun e => x.val.property (congrArg Subtype.val e)⟩
  invFun x := ⟨⟨x.val.val,fun e => x.property (Subtype.ext e)⟩,fun e => x.val.property (congrArg Subtype.val e)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

private noncomputable def originalCC {V : Type} [Fintype V] {G : SimpleGraph V} {c v : V} (ne : c≠v)
    (leaf : (G.induce {c}ᶜ).degree ⟨v,ne.symm⟩=1) :
    Branch (G.induce {v}ᶜ) ⟨c,ne⟩ ≃ Branch G c :=
  (commute_delete G ne).connectedComponentEquiv.trans (unclipCC (G.induce {c}ᶜ) leaf)

private lemma originalCC_mk {V : Type} [Fintype V] {G : SimpleGraph V} {c v : V} (ne : c≠v)
    (leaf : (G.induce {c}ᶜ).degree ⟨v,ne.symm⟩=1)
    (x : ({(⟨c,ne⟩ : ({v}ᶜ : Set V))}ᶜ : Set ({v}ᶜ : Set V))) :
    originalCC ne leaf (((G.induce {v}ᶜ).induce _).connectedComponentMk x) =
      (G.induce {c}ᶜ).connectedComponentMk ⟨x.val.val,fun e => x.property (Subtype.ext e)⟩ := rfl

private noncomputable def clippedPart {V : Type} [Fintype V] {G : SimpleGraph V} {c v : V} (ne : c≠v)
    (leaf : (G.induce {c}ᶜ).degree ⟨v,ne.symm⟩=1) (C : Branch (G.induce {v}ᶜ) ⟨c,ne⟩) :
    C.toSimpleGraph ≃g (originalCC ne leaf C).toSimpleGraph.induce {x | x.val.val≠v} := by
  let O := originalCC ne leaf C
  let mk (x : C.supp) : O.supp :=
    ⟨⟨x.val.val.val,fun e => x.val.property (Subtype.ext e)⟩,
     (originalCC_mk ne leaf x.val).symm.trans (congrArg (originalCC ne leaf) x.property)⟩
  let embed (x : C.supp) : {x : O.supp // x.val.val ≠ v} := ⟨mk x,x.val.val.property⟩
  have inj : Function.Injective embed := by
    intro x y h
    exact Subtype.ext (Subtype.ext (Subtype.ext (congrArg (fun z : {x:O.supp // x.val.val≠v} => z.val.val.val) h)))
  have onto : Function.Surjective embed := by
    intro y
    let x : ({(⟨c,ne⟩ : ({v}ᶜ : Set V))}ᶜ : Set ({v}ᶜ : Set V)) :=
      ⟨⟨y.val.val.val,y.property⟩,fun e => y.val.val.property (congrArg Subtype.val e)⟩
    have mem : x∈C.supp := (originalCC ne leaf).injective ((originalCC_mk ne leaf x).trans y.val.property)
    exact ⟨⟨x,mem⟩,rfl⟩
  exact ⟨Equiv.ofBijective embed ⟨inj,onto⟩,Iff.rfl⟩

private lemma clippedPart_root {V : Type} [Fintype V] {G : SimpleGraph V} (tree : G.IsTree) {c v : V}
    (ne : c≠v) (leaf : (G.induce {c}ᶜ).degree ⟨v,ne.symm⟩=1) (degree : G.degree v=1)
    (C : Branch (G.induce {v}ᶜ) ⟨c,ne⟩) :
    (clippedPart ne leaf C (attachment (induce_compl_singleton_isTree_of_deg_one G tree degree) C)).val =
      attachment tree (originalCC ne leaf C) := by
  apply (is_attachment tree _ _).mp
  exact (is_attachment (induce_compl_singleton_isTree_of_deg_one G tree degree) C _).mpr rfl

private abbrev Cuts (T : RootGraph) (r : Nat) (b : Prop) :=
  {x : T.V // usable T.G T.root r b x}

private noncomputable def afterCut (T : RootGraph) {r : Nat} {b : Prop} (x : Cuts T r b) : RootShape :=
  rootShape (T.G.induce {x.val}ᶜ) (⟨T.root,x.property.1.symm⟩ : ({x.val}ᶜ : Set T.V))

private def cutsEquiv {S T : RootGraph} {r : Nat} {b : Prop} (f : S.G ≃g T.G)
    (e : f S.root=T.root) : Cuts S r b ≃ Cuts T r b := by
  refine f.toEquiv.subtypeEquiv fun x => ?_
  have unique : (∀ y,T.G.dist (f S.root) y+1=r → y=f x) ↔
      ∀ y,S.G.dist S.root y+1=r → y=x := by
    constructor
    · intro h y hy
      exact f.injective (h (f y) (by rwa [iso_dist]))
    · intro h y hy
      obtain ⟨u,rfl⟩ := f.surjective y
      exact congrArg f (h u (by rwa [iso_dist] at hy))
  change usable S.G S.root r b x ↔ usable T.G T.root r b (f x)
  simp only [usable,←e,f.degree_eq,f.injective.ne_iff,iso_dist,unique]

private lemma afterCut_congr {S T : RootGraph} {r : Nat} {b : Prop} (f : S.G ≃g T.G)
    (e : f S.root=T.root) (x : Cuts S r b) : afterCut S x=afterCut T (cutsEquiv f e x) := by
  let g := restrict_iso f {x.val}ᶜ {f x.val}ᶜ (fun z => by simp)
  apply (rootShape_iff _ _ _ _).mpr
  exact ⟨g,Subtype.ext e⟩

private noncomputable def cutNumber (r : Nat) (b : Prop) : RootShape → Nat :=
  Quotient.lift (fun R : RootGraph => Fintype.card (Cuts R r b)) (by
    rintro A B ⟨f,e⟩
    exact Fintype.card_congr (cutsEquiv f e))

private noncomputable def gain (r : Nat) (b : Prop) (q : RootShape) : RootShape → Nat :=
  Quotient.lift (fun R : RootGraph => Fintype.card {x : Cuts R r b // afterCut R x=q}) (by
    rintro A B ⟨f,e⟩
    let E := cutsEquiv (r:=r) (b:=b) f e
    apply Fintype.card_congr (E.subtypeEquiv _)
    intro x
    change (afterCut A x=q) ↔ afterCut B (cutsEquiv f e x)=q
    rw [afterCut_congr f e])

private lemma gain_smaller {r : Nat} {b : Prop} {p q : RootShape} (pos : 0 < gain r b q p) :
    rootSize q < rootSize p := by
  induction p using Quotient.inductionOn with
  | _ T =>
    change 0 < Fintype.card {x : Cuts T r b // afterCut T x=q} at pos
    obtain ⟨⟨x,e⟩⟩ := Fintype.card_pos_iff.mp pos
    subst q
    change Fintype.card ({x.val}ᶜ : Set T.V) < Fintype.card T.V
    exact Fintype.card_subtype_lt (p := fun y : T.V => y∈({x.val}ᶜ : Set T.V)) (x:=x.val) (by simp)

private lemma sum_indicator {A : Type*} [Fintype A] (p : A → Prop) [DecidablePred p] :
    (∑ x:A, if p x then 1 else 0) = Fintype.card {x // p x} := by
  classical
  rw [Fintype.card_subtype]
  simp

private lemma sum_by_shape {I Q : Type*} [Fintype I] (tag : I → Q) (S : Finset Q)
    (mem : ∀ i,tag i∈S) (f : Q → Nat) :
    ∑ i:I, f (tag i) = ∑ q ∈ S, Fintype.card {i // tag i=q} * f q := by
  classical
  have maps : ∀ i∈(Finset.univ : Finset I),tag i∈S := fun i _ => mem i
  rw [←(Finset.sum_fiberwise_of_maps_to maps (fun i => f (tag i)))]
  apply Finset.sum_congr rfl
  intro q _
  rw [Fintype.card_subtype]
  calc
    _ = ∑ _i ∈ Finset.univ.filter (fun i => tag i=q), f q := Finset.sum_congr rfl (fun i hi => congrArg f (Finset.mem_filter.mp hi).2)
    _ = _ := by simp

private lemma leaf_double_count {I : Type} [Fintype I] (K : I → Type) [∀ i,Fintype (K i)] {Q : Type*}
    (tag : I → Q) (prune : (z : Sigma K) → Q) (cardTag : Sigma K → I → Q)
    (rest : ∀ z i,z.fst≠i → cardTag z i=tag i) (own : ∀ z,cardTag z z.fst=prune z) (q : Q) :
    (∑ z:Sigma K,Fintype.card {i // cardTag z i=q}) =
    ∑ i:I, ((if tag i=q then Fintype.card (Sigma K) - Fintype.card (K i) else 0) +
      Fintype.card {x : K i // prune ⟨i,x⟩=q}) := by
  classical
  simp only [←sum_indicator]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  let same (z : Sigma K) := z.fst=i
  have assign (z : Sigma K) :
      (if cardTag z i=q then 1 else 0 : Nat) =
      (if ¬ same z ∧ tag i=q then 1 else 0) + (if same z ∧ prune z=q then 1 else 0) := by
    by_cases h : same z
    · have e : cardTag z i=prune z := (show z.fst=i from h) ▸ own z
      simp [h,e]
    · simp [h,rest z i h]
  rw [Finset.sum_congr rfl (fun z _ => assign z),Finset.sum_add_distrib]
  let E : {z : Sigma K // same z} ≃ K i :=
    { toFun := fun z => (show z.val.fst=i from z.property) ▸ z.val.snd
      invFun := fun x => ⟨⟨i,x⟩,rfl⟩
      left_inv := by rintro ⟨⟨j,x⟩,h⟩;change j=i at h;subst i;rfl
      right_inv := fun _ => rfl }
  have R : (∑ z:Sigma K,if ¬same z ∧ tag i=q then 1 else 0 : Nat) =
      if tag i=q then Fintype.card (Sigma K)-Fintype.card (K i) else 0 := by
    by_cases hn : tag i=q
    · simp only [hn,and_true,if_true]
      rw [sum_indicator (fun z => ¬same z),Fintype.card_subtype_compl,Fintype.card_congr E]
    · simp [hn]
  rw [R]
  congr 1
  rw [sum_indicator (fun z => same z ∧ prune z=q),sum_indicator (fun x => prune ⟨i,x⟩=q)]
  apply Fintype.card_congr
  exact { toFun := fun ⟨⟨j,x⟩,⟨e,eq⟩⟩ => by
            change j=i at e
            subst i
            exact ⟨x,eq⟩
          invFun := fun x => ⟨⟨i,x.val⟩,rfl,x.property⟩
          left_inv := by rintro ⟨⟨j,x⟩,⟨e,eq⟩⟩;change j=i at e;subst i;rfl
          right_inv := fun _ => rfl }

private theorem any_card (A : Type*) (i j : Fintype A) : @Fintype.card A i = @Fintype.card A j :=
  congrArg (fun k => @Fintype.card A k) (Subsingleton.elim i j)

private theorem usable_inst {A : Type} (i j : Fintype A) (S : SimpleGraph A) (c : A) (r : Nat) (b : Prop) (v : A) :
    @usable A i S c r b v ↔ @usable A j S c r b v := by
  obtain rfl := Subsingleton.elim i j
  rfl

private structure TreeData {V : Type} [Fintype V] (G : SimpleGraph V) (c : V) (r : Nat) where
  tree : G.IsTree
  pos : 2 ≤ r
  diam : G.diam=2*r
  upper : ∀ x,G.dist c x≤r
  center : ∀ v,G.degree v=1 → v≠c
  noLeaf : ∀ v,G.Adj c v → 2 ≤ (G.neighborSet v).ncard
  pair : ∃ a b : ({c}ᶜ : Set V),G.dist c a.val=r ∧ G.dist c b.val=r ∧
    (G.induce {c}ᶜ).connectedComponentMk a ≠ (G.induce {c}ᶜ).connectedComponentMk b

private abbrev Leaves {V : Type} [Fintype V] (G : SimpleGraph V) (r : Nat) :=
  {v : V // G.degree v=1 ∧ (G.induce {v}ᶜ).diam=2*r}

namespace TreeData
variable {V : Type} [Fintype V] {G : SimpleGraph V} {c : V} {r : Nat} (d : TreeData G c r)

noncomputable def pack (C : Branch G c) : RootGraph := ⟨⟨C.supp,inferInstance,C.toSimpleGraph⟩,attachment d.tree C⟩

lemma shaped (C : Branch G c) : branchShape d.tree C=Quotient.mk _ (d.pack C) :=
  Quotient.sound ⟨SimpleGraph.Iso.refl,rfl⟩

abbrev Choices (C : Branch G c) := Cuts (d.pack C) r (badFlag G r)

lemma intrinsic (C : Branch G c) (x : C.supp) :
    (G.degree x.val.val=1 ∧ (G.induce {x.val.val}ᶜ).diam=2*r) ↔
      usable (d.pack C).G (d.pack C).root r (badFlag G r) x :=
  (intrinsic_usable d.tree d.pos d.diam d.upper d.center d.noLeaf d.pair C x).trans (usable_inst _ _ _ _ _ _ _)

set_option maxHeartbeats 1600000 in
noncomputable def leafEquiv : (Σ C,d.Choices C) ≃ Leaves G r where
  toFun z := ⟨z.snd.val.val.val,(d.intrinsic z.fst _).mpr z.snd.property⟩
  invFun v := by
    let u : ({c}ᶜ : Set V) := ⟨v.val,d.center _ v.property.1⟩
    let C := (G.induce {c}ᶜ).connectedComponentMk u
    exact ⟨C,⟨⟨u,rfl⟩,(d.intrinsic C _).mp v.property⟩⟩
  left_inv := by
    rintro ⟨C,⟨⟨⟨u,uc⟩,inC⟩,ok⟩⟩
    change (G.induce {c}ᶜ).connectedComponentMk ⟨u,uc⟩=C at inC
    subst C
    rfl
  right_inv _ := rfl

lemma still_leaf (v : Leaves G r) : (G.induce {c}ᶜ).degree ⟨v.val,d.center _ v.property.1⟩=1 := by
  have no : ¬G.Adj v.val c := by
    intro adj
    have l := d.noLeaf _ adj.symm
    rw [ncard_neighborSet_eq_degree,v.property.1] at l;omega
  exact (degree_induce_compl_singleton_of_not_adj G (d.center _ v.property.1) no).trans v.property.1

noncomputable def compEquiv (v : Leaves G r) :
    Branch (G.induce {v.val}ᶜ) ⟨c,(d.center _ v.property.1).symm⟩ ≃ Branch G c :=
  originalCC _ (d.still_leaf v)

noncomputable def displayed (v : Leaves G r) (C : Branch G c) : RootShape :=
  branchShape (induce_compl_singleton_isTree_of_deg_one G d.tree v.property.1) ((d.compEquiv v).symm C)

lemma kept {v : Leaves G r} (C : Branch G c) (away : ∀ x:C.supp,x.val.val≠v.val) :
    d.displayed v C=branchShape d.tree C := by
  obtain ⟨D,rfl⟩ := (d.compEquiv v).surjective C
  unfold displayed
  rw [(d.compEquiv v).symm_apply_apply]
  let E := clippedPart _ (d.still_leaf v) D
  let T := ((d.compEquiv v) D).toSimpleGraph
  let upper : T.induce {x | x.val.val≠v.val} ≃g T :=
    { toFun := Subtype.val
      invFun := fun x => ⟨x,away x⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_rel_iff' := Iff.rfl }
  apply Quotient.sound
  exact ⟨E.trans upper,clippedPart_root d.tree _ (d.still_leaf v) v.property.1 D⟩

lemma trimmed (v : Leaves G r) (C : Branch G c) (x : d.Choices C) (eq : x.val.val.val=v.val) :
    d.displayed v C=afterCut (d.pack C) x := by
  obtain ⟨D,rfl⟩ := (d.compEquiv v).surjective C
  unfold displayed
  rw [(d.compEquiv v).symm_apply_apply]
  let E := clippedPart _ (d.still_leaf v) D
  let T := ((d.compEquiv v) D).toSimpleGraph
  have core (y : ((d.compEquiv v) D).supp) :
      y.val.val≠v.val ↔ y≠x.val := by
    constructor
    · intro yes e; exact yes ((congrArg (fun z : ((d.compEquiv v) D).supp => z.val.val) e).trans eq)
    · intro yes e;exact yes (Subtype.ext (Subtype.ext (e.trans eq.symm)))
  let alias' := restrict_iso (SimpleGraph.Iso.refl : T ≃g T) {y | y.val.val≠v.val} {x.val}ᶜ core
  apply Quotient.sound
  exact ⟨E.trans alias',Subtype.ext (clippedPart_root d.tree _ (d.still_leaf v) v.property.1 D)⟩

noncomputable def total (q : RootShape) : Nat :=
  ∑ v : Leaves G r, Fintype.card {C : Branch G c // d.displayed v C=q}

set_option maxHeartbeats 1600000 in
lemma expansion (q : RootShape) :
    d.total q = ∑ C : Branch G c, ((if branchShape d.tree C=q then Fintype.card (Leaves G r) -
      cutNumber r (badFlag G r) (branchShape d.tree C) else 0) + gain r (badFlag G r) q (branchShape d.tree C)) := by
  classical
  let p (z : Σ C,d.Choices C) := afterCut (d.pack z.fst) z.snd
  have rest (z : Σ C,d.Choices C) (C) (hn : z.fst≠C) :
      d.displayed (d.leafEquiv z) C=branchShape d.tree C := by
    apply d.kept
    intro x e
    have e' : x.val=z.snd.val.val := Subtype.ext e
    exact hn (z.snd.val.property.symm.trans ((congrArg (G.induce {c}ᶜ).connectedComponentMk e').symm.trans x.property))
  have own (z : Σ C,d.Choices C) : d.displayed (d.leafEquiv z) z.fst=p z :=
    d.trimmed _ _ _ rfl
  have sum := leaf_double_count d.Choices (branchShape d.tree) p (fun z C => d.displayed (d.leafEquiv z) C) rest own q
  rw [Fintype.card_congr d.leafEquiv] at sum
  refine (d.leafEquiv.sum_comp (fun v => Fintype.card {C : Branch G c // d.displayed v C=q})).symm.trans (Eq.trans ?_ (sum.trans ?_))
  · apply Finset.sum_congr rfl
    intro z _
    exact any_card _ _ _
  · apply Finset.sum_congr rfl
    intro C _
    rw [d.shaped C]
    apply congrArg₂ Nat.add
    · by_cases yes : Quotient.mk _ (d.pack C) = q
      · simp only [if_pos yes]
        exact congrArg (fun n => Fintype.card (Leaves G r) - n) (any_card _ _ _)
      · simp only [if_neg yes]
    · exact any_card _ _ _

end TreeData

private theorem eliminate_branches {Q : Type*} (S : Finset Q) (size : Q → Nat) (w : Q → Q → Nat)
    (f g : Q → Nat) (diag : ∀ i∈S,0<w i i)
    (strict : ∀ i∈S,∀ j∈S,i≠j → 0<w i j → size i < size j)
    (tests : ∀ i∈S, ∑ j ∈ S, w i j * f j = ∑ j ∈ S, w i j * g j) :
    ∀ i∈S,f i=g i := by
  classical
  by_contra! bad
  obtain ⟨i,si,bad⟩ := bad
  let differences := S.filter (fun j => f j≠g j)
  have non : differences.Nonempty := ⟨i,Finset.mem_filter.mpr ⟨si,bad⟩⟩
  obtain ⟨u,hu,um⟩ := Finset.exists_max_image differences size non
  obtain ⟨su,une⟩ := Finset.mem_filter.mp hu
  have agree (j) (inS : j∈S.erase u) : w u j * f j = w u j * g j := by
    by_cases eq : f j=g j
    · rw [eq]
    · have jm := Finset.mem_erase.mp inS
      have le := um j (Finset.mem_filter.mpr ⟨jm.2,eq⟩)
      by_cases zero : w u j=0
      · simp [zero]
      · have := strict u su j jm.2 jm.1.symm (by omega)
        omega
  have h := tests u su
  rw [←Finset.sum_erase_add _ _ su,←Finset.sum_erase_add _ _ su] at h
  have s := Finset.sum_congr rfl agree
  have eq : w u u*f u=w u u*g u := by omega
  exact une (Nat.eq_of_mul_eq_mul_left (diag u su) eq)

private def Covers {V : Type} [Fintype V] (G : SimpleGraph V) (c : V) (r : Nat) :=
  ∀ C : Branch G c, ∃ v : ({c}ᶜ : Set V), v∉C.supp ∧ (G.neighborSet v.val).ncard=1 ∧ (G.induce {v.val}ᶜ).diam=2*r

set_option maxHeartbeats 1600000 in
private lemma coefficient_positive {V : Type} [Fintype V] {G : SimpleGraph V} {c : V} {r : Nat}
    (d : TreeData G c r) (covers : Covers G c r) (C : Branch G c) :
    cutNumber r (badFlag G r) (branchShape d.tree C) < Fintype.card (Leaves G r) := by
  classical
  let f (x : d.Choices C) := d.leafEquiv ⟨C,x⟩
  rw [d.shaped C]
  change Fintype.card (d.Choices C) < Fintype.card (Leaves G r)
  apply Fintype.card_lt_of_injective_not_surjective f
  · intro x y eq
    exact Sigma.mk.inj_iff.mp (d.leafEquiv.injective eq) |>.2 |>.eq
  · intro onto
    obtain ⟨v,out,deg,diam⟩ := covers C
    rw [ncard_neighborSet_eq_degree] at deg
    obtain ⟨x,ex⟩ := onto ⟨v.val,deg,diam⟩
    have val := congrArg (fun z : Leaves G r => z.val) ex
    change x.val.val.val = v.val at val
    have eq : x.val.val=v := Subtype.ext val
    exact out (eq ▸ x.val.property)

set_option maxHeartbeats 1600000 in
private lemma recover_shapes {V W : Type} [Fintype V] [Fintype W]
    {G : SimpleGraph V} {H : SimpleGraph W} {c : V} {d : W} {r : Nat}
    (D : TreeData G c r) (E : TreeData H d r) (gc : Covers G c r) (hc : Covers H d r)
    (bad : badFlag G r = badFlag H r) (nleaves : Fintype.card (Leaves G r)=Fintype.card (Leaves H r))
    (data : ∀ q,D.total q=E.total q) : Nonempty (G ≃g H) := by
  classical
  let X := @branchShape _ _ G D.tree c
  let Y := @branchShape _ _ H E.tree d
  let S := Finset.univ.image X ∪ Finset.univ.image Y
  have xm (i) : X i∈S := Finset.mem_union_left _ (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩)
  have ym (i) : Y i∈S := Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩)
  let gap (q) := Fintype.card (Leaves G r)-cutNumber r (badFlag G r) q
  let coeff (q t) := (if t=q then gap t else 0) + gain r (badFlag G r) q t
  let m (q) := Fintype.card {i // X i=q}
  let n (q) := Fintype.card {i // Y i=q}
  have pos (q) (mem : q∈S) : 0 < gap q := by
    rcases Finset.mem_union.mp mem with xl|yl
    · obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp xl
      exact Nat.sub_pos_of_lt (coefficient_positive D gc i)
    · obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp yl
      dsimp only [gap]
      rw [nleaves,bad]
      exact Nat.sub_pos_of_lt (coefficient_positive E hc i)
  have tests (q) : (∑ t∈S,coeff q t*m t) = ∑ t∈S,coeff q t*n t := by
    have L := D.expansion q
    have R := E.expansion q
    rw [←bad,←nleaves] at R
    have xl : D.total q=∑ i:Branch G c,coeff q (X i) := L
    have yl : E.total q=∑ i:Branch H d,coeff q (Y i) := R
    rw [sum_by_shape X S xm] at xl
    rw [sum_by_shape Y S ym] at yl
    refine Eq.trans ?_ ((xl.symm.trans ((data q).trans yl)).trans ?_)
    · apply Finset.sum_congr rfl
      intro t _
      rw [Nat.mul_comm]
      exact congrArg (fun z => z * coeff q t) (any_card _ _ _)
    · apply Finset.sum_congr rfl
      intro t _
      rw [Nat.mul_comm]
      exact congrArg (fun z => coeff q t * z) (any_card _ _ _)
  have eq := eliminate_branches S rootSize coeff m n (fun q h => by
    have p := pos q h;dsimp only [coeff];rw [if_pos rfl];omega)
    (fun i _ j _ ne p => by
      change 0 < (if j=i then gap j else 0) + gain r (badFlag G r) i j at p
      rw [if_neg ne.symm,Nat.zero_add] at p
      exact gain_smaller p)
    (fun q _ => tests q)
  apply trees_of_equal_branches D.tree E.tree
  intro q
  by_cases mem : q∈S
  · exact eq q mem
  · have lx : ∀ i,X i≠q := fun i h => mem (h ▸ xm i)
    have ly : ∀ j,Y j≠q := fun j h => mem (h ▸ ym j)
    change Fintype.card {i // X i=q}=Fintype.card {j // Y j=q}
    simp [lx,ly]

private lemma split_walk_first_mem {U : Type} (T : SimpleGraph U) (P : Set U)
    [DecidablePred (· ∈ P)] {y c : U} (q : T.Walk y c) (hc : c ∈ P) :
    ∃ (z : U) (q₁ : T.Walk y z) (q₂ : T.Walk z c),
      z ∈ P ∧ q = q₁.append q₂ ∧ (∀ u ∈ q₁.support, u ∈ P → u = z) := by
  induction q with
  | nil =>
    exact ⟨_, Walk.nil, Walk.nil, hc, rfl, fun u hu _ => by simp only [Walk.support_nil, List.mem_singleton] at hu; exact hu⟩
  | @cons a b c h q' ih =>
    by_cases ha : a ∈ P
    · exact ⟨a, Walk.nil, Walk.cons h q', ha, rfl, fun u hu _ => by simp only [Walk.support_nil, List.mem_singleton] at hu; exact hu⟩
    · obtain ⟨z, q₁, q₂, hz, hq', huniq⟩ := ih hc
      refine ⟨z, Walk.cons h q₁, q₂, hz, by rw [hq']; rfl, fun u hu huP => ?_⟩
      simp only [Walk.support_cons, List.mem_cons] at hu
      rcases hu with rfl | hu
      · exact False.elim (ha huP)
      · exact huniq u hu huP

private lemma isPath_append_of_first_meet {U : Type} {T : SimpleGraph U}
    {y z x : U} {q₁ : T.Walk y z} {s : T.Walk z x}
    (hq₁ : q₁.IsPath) (hs : s.IsPath)
    (hmeet : ∀ u ∈ q₁.support, u ∈ s.support.tail → u = z) :
    (q₁.append s).IsPath := by
  rw [Walk.isPath_def, Walk.support_append, List.nodup_append']
  refine ⟨hq₁.support_nodup, hs.support_nodup.tail, fun u huq hus => ?_⟩
  have huz : u = z := hmeet u huq hus
  subst huz
  exact start_notMem_tail_support_of_isPath hs hus

private lemma exists_unique_center_of_diam_eq_two_mul {U : Type} [Fintype U]
    (T : SimpleGraph U) (hT : T.IsTree) {r : ℕ} (hr : 1 ≤ r) (hdiam : T.diam = 2 * r) :
    ∃ c : U, T.eccent c = r ∧ ∀ v : U, v ≠ c → (r : ℕ∞) < T.eccent v := by
  have : Nonempty U := hT.connected.nonempty
  obtain ⟨x0, xd, hxd⟩ := T.exists_dist_eq_diam
  obtain ⟨p, hp, hplen⟩ := hT.connected.exists_path_of_dist x0 xd
  have hplen_r : p.length = 2 * r := hplen.trans (hxd.trans hdiam)
  let c : U := p.getVert r
  let p₁ : T.Walk x0 c := p.take r
  let p₂ : T.Walk c xd := p.drop r
  have hp1 : p₁.IsPath := hp.take r
  have hp2 : p₂.IsPath := hp.drop r
  have hp1_len : p₁.length = r := by rw [Walk.take_length]; omega
  have hp2_len : p₂.length = r := by rw [Walk.drop_length]; omega
  have hp_app : p₁.append p₂ = p := p.append_take_drop_eq r
  have hkey : ∀ y : U, (T.dist y xd = T.dist y c + r ∨ T.dist y x0 = T.dist y c + r) := by
    intro y
    obtain ⟨q, hq, hqlen⟩ := hT.connected.exists_path_of_dist y c
    obtain ⟨z, q₁, q₂, hz_mem, hq_eq, hq_first⟩ :=
      split_walk_first_mem T {u | u ∈ p.support} q (p.getVert_mem_support r)
    have hq_app : (q₁.append q₂).IsPath := hq_eq ▸ hq
    have hq1 : q₁.IsPath := hq_app.of_append_left
    have hq2 : q₂.IsPath := hq_app.of_append_right
    have hq_len : q.length = q₁.length + q₂.length := by rw [hq_eq, Walk.length_append]
    have hz12 : z ∈ p₁.support ∨ z ∈ p₂.support :=
      (Walk.mem_support_append_iff p₁ p₂).mp (hp_app.symm ▸ hz_mem)
    rcases hz12 with hz1 | hz2
    · obtain ⟨a, b, ha, hb, hp1_eq⟩ := hp1.mem_support_iff_exists_append.mp hz1
      let pR : T.Walk z xd := b.append p₂
      have hp_decomp : p = a.append pR := by rw [← hp_app, hp1_eq, Walk.append_assoc]
      have hpR : pR.IsPath := (hp_decomp ▸ hp).of_append_right
      have hb_eq : q₂ = b := isTree_path_eq T hT hq2 hb
      have hpR_len : pR.length = q₂.length + r := by rw [Walk.length_append, hp2_len, hb_eq]
      have hmeet : ∀ u ∈ q₁.support, u ∈ pR.support.tail → u = z := by
        intro u huq hus
        exact hq_first u huq (hp_decomp ▸ Walk.support_subset_support_append_right a pR (List.mem_of_mem_tail hus))
      have hqpR : (q₁.append pR).IsPath := isPath_append_of_first_meet hq1 hpR hmeet
      have hdist : (q₁.append pR).length = T.dist y xd :=
        isTree_dist_eq_length_of_isPath T hT (q₁.append pR) hqpR
      left
      rw [Walk.length_append, hpR_len] at hdist
      omega
    · obtain ⟨a, b, ha, hb, hp2_eq⟩ := hp2.mem_support_iff_exists_append.mp hz2
      let pL : T.Walk x0 z := p₁.append a
      have hp_decomp : p = pL.append b := by rw [← hp_app, hp2_eq, ← Walk.append_assoc]
      have hpL : pL.IsPath := (hp_decomp ▸ hp).of_append_left
      have ha_eq : q₂ = a.reverse := isTree_path_eq T hT hq2 ha.reverse
      have hpL_len : pL.reverse.length = r + q₂.length := by
        rw [Walk.length_reverse, Walk.length_append, hp1_len, ha_eq, Walk.length_reverse]
      have hmeet : ∀ u ∈ q₁.support, u ∈ pL.reverse.support.tail → u = z := by
        intro u huq hus
        have hus1 : u ∈ pL.reverse.support := List.mem_of_mem_tail hus
        rw [Walk.support_reverse, List.mem_reverse] at hus1
        exact hq_first u huq (hp_decomp ▸ Walk.support_subset_support_append_left pL b hus1)
      have hqpL : (q₁.append pL.reverse).IsPath := isPath_append_of_first_meet hq1 hpL.reverse hmeet
      have hdist : (q₁.append pL.reverse).length = T.dist y x0 :=
        isTree_dist_eq_length_of_isPath T hT (q₁.append pL.reverse) hqpL
      right
      rw [Walk.length_append, hpL_len] at hdist
      omega
  have hediam : T.ediam ≠ ⊤ := connected_iff_ediam_ne_top.mp hT.connected
  have hle_r : ∀ y : U, T.dist y c ≤ r := by
    intro y
    rcases hkey y with hy | hy
    · have := dist_le_diam hediam (u := y) (v := xd); omega
    · have := dist_le_diam hediam (u := y) (v := x0); omega
  have hecc_le : T.eccent c ≤ r := by
    rw [SimpleGraph.eccent_le_iff]
    intro y
    rw [← (hT.connected c y).coe_dist_eq_edist, SimpleGraph.dist_comm]
    exact Nat.cast_le.mpr (hle_r y)
  have hecc_ge : (r : ℕ∞) ≤ T.eccent c := by
    have hcx0 : T.dist c x0 = r := by
      have h := isTree_dist_eq_length_of_isPath T hT p₁ hp1
      rw [SimpleGraph.dist_comm, ← h, hp1_len]
    rw [← hcx0, (hT.connected c x0).coe_dist_eq_edist]
    exact SimpleGraph.edist_le_eccent
  refine ⟨c, le_antisymm hecc_le hecc_ge, fun v hvc => ?_⟩
  have hpos : 0 < T.dist v c := hT.connected.pos_dist_of_ne hvc
  rcases hkey v with hv | hv
  · have hlt : (r : ℕ∞) < (T.dist v xd : ℕ∞) := Nat.cast_lt.mpr (by omega)
    rw [(hT.connected v xd).coe_dist_eq_edist] at hlt
    exact lt_of_lt_of_le hlt SimpleGraph.edist_le_eccent
  · have hlt : (r : ℕ∞) < (T.dist v x0 : ℕ∞) := Nat.cast_lt.mpr (by omega)
    rw [(hT.connected v x0).coe_dist_eq_edist] at hlt
    exact lt_of_lt_of_le hlt SimpleGraph.edist_le_eccent

private lemma iso_eccent_eq {A B : Type*} (GA : SimpleGraph A) (GB : SimpleGraph B)
    (φ : GA ≃g GB) (a : A) : GB.eccent (φ a) = GA.eccent a := by
  simp only [SimpleGraph.eccent_def]
  apply le_antisymm
  · rw [iSup_le_iff]
    intro b
    rw [← φ.apply_symm_apply b, iso_edist_eq GA GB φ a (φ.symm b)]
    exact le_iSup (GA.edist a) (φ.symm b)
  · rw [iSup_le_iff]
    intro a'
    rw [← iso_edist_eq GA GB φ a a']
    exact le_iSup (GB.edist (φ a)) (φ a')

private lemma iso_diam_eq {A B : Type*} (GA : SimpleGraph A) (GB : SimpleGraph B)
    (φ : GA ≃g GB) : GA.diam = GB.diam := by
  simp only [SimpleGraph.diam, SimpleGraph.ediam]
  congr 1
  apply le_antisymm
  · rw [iSup_le_iff]
    intro a
    rw [← iso_eccent_eq GA GB φ a]
    exact le_iSup GB.eccent (φ a)
  · rw [iSup_le_iff]
    intro b
    rw [← φ.apply_symm_apply b, iso_eccent_eq GA GB φ (φ.symm b)]
    exact le_iSup GA.eccent (φ.symm b)

private lemma ne_center_of_deg_one {U : Type} [Fintype U]
    (T : SimpleGraph U) (hT : T.IsTree) {r : ℕ} (hr : 1 ≤ r) (c : U)
    (hecc : T.eccent c = r) (huniq_c : ∀ z : U, z ≠ c → (r : ℕ∞) < T.eccent z)
    {v : U} (hdeg1 : T.degree v = 1) : v ≠ c := by
  rintro rfl
  obtain ⟨u, huv, huniq⟩ := SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp hdeg1
  have huc : u ≠ v := huv.ne.symm
  have hle : T.eccent u ≤ r := by
    rw [SimpleGraph.eccent_le_iff]
    intro y
    rw [← (hT.connected u y).coe_dist_eq_edist]
    norm_cast
    by_cases hyv : y = v
    · subst hyv
      have hd : T.dist u y = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr huv.symm
      omega
    · obtain ⟨p, hp, hplen⟩ := hT.connected.exists_path_of_dist v y
      have hnp : ¬ p.Nil := Walk.not_nil_of_ne (Ne.symm hyv)
      have hsnd : p.snd = u := huniq p.snd (p.adj_snd hnp)
      let p' : T.Walk u y := p.tail.copy hsnd rfl
      have hp' : p'.IsPath := (Walk.isPath_copy _ _ _).mpr hp.tail
      have hdist_u : T.dist u y = p'.length :=
        (isTree_dist_eq_length_of_isPath T hT p' hp').symm
      have hvy_le : T.dist v y ≤ r := by
        have h1 : (T.dist v y : ℕ∞) ≤ r := by
          rw [(hT.connected v y).coe_dist_eq_edist, ← hecc]
          exact SimpleGraph.edist_le_eccent
        exact Nat.cast_le.mp h1
      rw [hdist_u, Walk.length_copy, Walk.length_tail, hplen]
      omega
  have hlt := huniq_c u huc
  exact absurd (lt_of_lt_of_le hlt hle) (lt_irrefl _)

private lemma center_induce_compl_of_good_leaf {U : Type} [Fintype U]
    (T : SimpleGraph U) (hT : T.IsTree) {r : ℕ} (hr : 1 ≤ r)
    (c : U) (hecc : T.eccent c = r) (huniq_c : ∀ z : U, z ≠ c → (r : ℕ∞) < T.eccent z)
    {v : U} (hdeg1 : T.degree v = 1) (hdiam' : (T.induce {v}ᶜ).diam = 2 * r) :
    ∃ hc : c ∈ ({v}ᶜ : Set U),
      (T.induce {v}ᶜ).eccent ⟨c, hc⟩ = r ∧
      ∀ z' : ({v}ᶜ : Set U), z' ≠ ⟨c, hc⟩ → (r : ℕ∞) < (T.induce {v}ᶜ).eccent z' := by
  have hc : c ∈ ({v}ᶜ : Set U) := Set.mem_compl_singleton_iff.mpr (ne_center_of_deg_one T hT hr c hecc huniq_c hdeg1).symm
  refine ⟨hc, ?_⟩
  let T' := T.induce ({v}ᶜ : Set U)
  have hT' : T'.IsTree := induce_compl_singleton_isTree_of_deg_one T hT hdeg1
  let c' : ({v}ᶜ : Set U) := ⟨c, hc⟩
  have hle_r : ∀ y' : ({v}ᶜ : Set U), T'.dist c' y' ≤ r := by
    intro y'
    rw [induce_compl_singleton_dist_eq T hT hT']
    have h1 : (T.dist c y'.1 : ℕ∞) ≤ r := by
      rw [(hT.connected c y'.1).coe_dist_eq_edist, ← hecc]
      exact SimpleGraph.edist_le_eccent
    exact Nat.cast_le.mp h1
  have hecc_le : T'.eccent c' ≤ r := by
    rw [SimpleGraph.eccent_le_iff]
    intro y'
    rw [← (hT'.connected c' y').coe_dist_eq_edist]
    exact Nat.cast_le.mpr (hle_r y')
  have : Nonempty ({v}ᶜ : Set U) := hT'.connected.nonempty
  obtain ⟨a, b, hab⟩ := T'.exists_dist_eq_diam
  rw [hdiam'] at hab
  have hda : T'.dist c' a = r := by
    have htri := hT'.connected.dist_triangle (u := a) (v := c') (w := b)
    rw [SimpleGraph.dist_comm (u := a) (v := c')] at htri
    have ha := hle_r a
    have hb := hle_r b
    omega
  have hecc_ge : (r : ℕ∞) ≤ T'.eccent c' := by
    rw [← hda, (hT'.connected c' a).coe_dist_eq_edist]
    exact SimpleGraph.edist_le_eccent
  have hecc_eq : T'.eccent c' = r := le_antisymm hecc_le hecc_ge
  obtain ⟨c₀, _, huniq₀⟩ := exists_unique_center_of_diam_eq_two_mul T' hT' hr hdiam'
  have hc₀ : c' = c₀ := by
    by_contra hne
    have hlt := huniq₀ c' hne
    rw [hecc_eq] at hlt
    exact absurd hlt (lt_irrefl _)
  subst hc₀
  exact ⟨hecc_eq, huniq₀⟩

private lemma iso_map_center_of_good_leaf {V W : Type} [Fintype V] [Fintype W]
    (G : SimpleGraph V) (H : SimpleGraph W) (hTG : G.IsTree) (hTH : H.IsTree)
    {r : ℕ} (hr : 1 ≤ r) (cG : V) (cH : W)
    (heccG : G.eccent cG = r) (huG : ∀ v : V, v ≠ cG → (r : ℕ∞) < G.eccent v)
    (heccH : H.eccent cH = r) (huH : ∀ w : W, w ≠ cH → (r : ℕ∞) < H.eccent w)
    {v : V} {w : W} (hv1 : G.degree v = 1) (hw1 : H.degree w = 1)
    (hdiamG' : (G.induce {v}ᶜ).diam = 2 * r)
    (φ : G.induce {v}ᶜ ≃g H.induce {w}ᶜ) :
    ∃ (hcG : cG ∈ ({v}ᶜ : Set V)) (hcH : cH ∈ ({w}ᶜ : Set W)), φ ⟨cG, hcG⟩ = ⟨cH, hcH⟩ := by
  have hdiamH' : (H.induce {w}ᶜ).diam = 2 * r :=
    (iso_diam_eq _ _ φ).symm.trans hdiamG'
  obtain ⟨hcG, heccG', _⟩ := center_induce_compl_of_good_leaf G hTG hr cG heccG huG hv1 hdiamG'
  obtain ⟨hcH, _, huH'⟩ := center_induce_compl_of_good_leaf H hTH hr cH heccH huH hw1 hdiamH'
  refine ⟨hcG, hcH, ?_⟩
  by_contra hne
  have hlt := huH' (φ ⟨cG, hcG⟩) hne
  rw [iso_eccent_eq _ _ φ ⟨cG, hcG⟩, heccG'] at hlt
  exact absurd hlt (lt_irrefl _)


private lemma make_tree_data {V : Type} [Fintype V] (G : SimpleGraph V) (tg : G.IsTree) {c : V} {r : Nat}
    (hr : 2≤r) (dg : G.diam=2*r) (eg : G.eccent c=r) (unique : ∀ x,x≠c → (r:ℕ∞)<G.eccent x)
    (nol : ∀ v,G.Adj c v → 2≤(G.neighborSet v).ncard) : TreeData G c r := by
  have up (x : V) : G.dist c x ≤ r := by
    apply (Nat.cast_le (α:=ℕ∞)).mp
    rw [(tg.connected c x).coe_dist_eq_edist,←eg]
    exact G.edist_le_eccent
  have : Nonempty V := tg.connected.nonempty
  obtain ⟨x,y,d⟩ := G.exists_dist_eq_diam
  have far := d.trans dg
  have xc : x≠c := by intro e;rw [e] at far;have := up y;omega
  have yc : y≠c := by intro e;rw [e,G.dist_comm] at far;have := up x;omega
  let a : ({c}ᶜ : Set V) := ⟨x,xc⟩
  let b : ({c}ᶜ : Set V) := ⟨y,yc⟩
  exact ⟨tg,hr,dg,up,fun v hv => ne_center_of_deg_one G tg (by omega) c eg unique hv,nol,
    ⟨a,b,(far_pair tg up a b).mp far⟩⟩

set_option maxHeartbeats 1600000 in
private lemma deck_total_eq {V W : Type} [Fintype V] [Fintype W] {G : SimpleGraph V}
    {H : SimpleGraph W} {r : Nat} {c : V} {d : W} (D : TreeData G c r) (E : TreeData H d r)
    (L : Leaves G r ≃ Leaves H r) (isoc : ∀ v : Leaves G r,
      ∃ f : G.induce {v.val}ᶜ ≃g H.induce {(L v).val}ᶜ,
        f ⟨c,(D.center _ v.property.1).symm⟩ = ⟨d,(E.center _ (L v).property.1).symm⟩)
    (q : RootShape) : D.total q=E.total q := by
  classical
  have one (v : Leaves G r) : Fintype.card {C : Branch G c // D.displayed v C=q} =
      Fintype.card {C : Branch H d // E.displayed (L v) C=q} := by
    obtain ⟨f,root⟩ := isoc v
    have A := induce_compl_singleton_isTree_of_deg_one G D.tree v.property.1
    have B := induce_compl_singleton_isTree_of_deg_one H E.tree (L v).property.1
    obtain ⟨s,ok⟩ := iso_preserves_branches A B f root
    let matched := ((D.compEquiv v).symm.trans s).trans (E.compEquiv (L v))
    have eq (C : Branch G c) : D.displayed v C=E.displayed (L v) (matched C) := by
      unfold TreeData.displayed
      change _=branchShape B ((E.compEquiv (L v)).symm ((E.compEquiv (L v)) _))
      rw [(E.compEquiv (L v)).symm_apply_apply]
      exact ok _
    exact Fintype.card_congr (matched.subtypeEquiv (fun C => by rw [eq C]))
  unfold TreeData.total
  calc
    _ = ∑ v:Leaves G r,Fintype.card {C : Branch H d // E.displayed (L v) C=q} := Finset.sum_congr rfl (fun v _ => one v)
    _ = _ := by
      have sum := L.sum_comp (fun v : Leaves H r => Fintype.card {C : Branch H d // E.displayed v C=q})
      refine Eq.trans ?_ (sum.trans ?_)
      · apply Finset.sum_congr rfl
        intro v _
        exact any_card _ _ _
      · apply Finset.sum_congr rfl
        intro v _
        exact any_card _ _ _


end TreeArms
end OMA
namespace LargeBranchCase1

section Solution
open SimpleGraph OMA.TreeArms Classical

set_option maxHeartbeats 1600000 in
theorem result : OMA.R_ReconstructionConjecture_reconstruction_conjecture_variants_tree_R1_H3_R1_H4_R1.H1 := by
  intro V W _ _ G H σ tg th cards degrees _ r c d hr dg dh eg eh ug uh _ nlG nlH
  dsimp only
  intro coversG coversH
  let D := make_tree_data G tg hr dg eg ug nlG
  let E := make_tree_data H th hr dh eh uh nlH
  let f (v) := (cards v).some
  have deg (v) : G.degree v=H.degree (σ v) := by
    simpa only [ncard_neighborSet_eq_degree] using degrees v
  have card_diam (v) : (G.induce {v}ᶜ).diam=(H.induce {σ v}ᶜ).diam := iso_diam_eq _ _ (f v)
  have flag : badFlag G r = badFlag H r := by
    apply propext
    constructor
    · rintro ⟨v,hv,bad⟩
      exact ⟨σ v,(deg v).symm.trans hv,fun eq => bad ((card_diam v).trans eq)⟩
    · rintro ⟨w,hw,bad⟩
      obtain ⟨v,rfl⟩ := σ.surjective w
      exact ⟨v,(deg v).trans hw,fun eq => bad ((card_diam v).symm.trans eq)⟩
  let L : Leaves G r ≃ Leaves H r := σ.subtypeEquiv (fun v => by
    rw [deg,card_diam])
  apply recover_shapes D E coversG coversH flag (Fintype.card_congr L)
  apply deck_total_eq D E L
  intro v
  have leaf : H.degree (σ v.val)=1 := (deg v.val).symm.trans v.property.1
  obtain ⟨_,_,eq⟩ := iso_map_center_of_good_leaf G H tg th (by omega) c d eg ug eh uh
    v.property.1 leaf v.property.2 (f v.val)
  exact ⟨f v.val,eq⟩

end Solution

end LargeBranchCase1

namespace LargeBranchCase2

/-
# A tree with all diameter-preserving leaves in one branch

The lemmas in `OMA.GreenNotes` are from @green-notes' solution of
`ReconstructionConjecture.reconstruction_conjecture.variants.tree.R1.H3.R1.H2`.
The two indicated auxiliary arguments adapt that solution. The single-tree
classification and its remaining auxiliary results are by @Deldor14.
-/

open SimpleGraph

namespace OMA.GreenNotes

open Classical

lemma isTree_dist_eq_length_of_isPath {U : Type} (T : SimpleGraph U) (hT : T.IsTree)
    {x y : U} (p : T.Walk x y) (hp : p.IsPath) :
    p.length = T.dist x y := by
  obtain ⟨q, hq, hqlen⟩ := hT.connected.exists_path_of_dist x y
  have hsub : (⟨p, hp⟩ : T.Path x y) = ⟨q, hq⟩ := (hT.isAcyclic.subsingleton_path x y).elim _ _
  have hpq : p = q := congrArg Subtype.val hsub
  rw [hpq, hqlen]

lemma isTree_path_eq {U : Type} (T : SimpleGraph U) (hT : T.IsTree)
    {x y : U} {p q : T.Walk x y} (hp : p.IsPath) (hq : q.IsPath) :
    p = q :=
  congrArg Subtype.val ((hT.isAcyclic.subsingleton_path x y).elim ⟨p, hp⟩ ⟨q, hq⟩)

lemma ncard_neighborSet_eq_degree {U : Type} [Fintype U] (T : SimpleGraph U) (u : U) :
    (T.neighborSet u).ncard = T.degree u := by
  rw [← T.card_neighborSet_eq_degree, Set.ncard_eq_toFinset_card' (T.neighborSet u)]
  simp [Set.toFinset_card]

lemma split_walk_first_mem {U : Type} (T : SimpleGraph U) (P : Set U)
    [DecidablePred (· ∈ P)] {y c : U} (q : T.Walk y c) (hc : c ∈ P) :
    ∃ (z : U) (q₁ : T.Walk y z) (q₂ : T.Walk z c),
      z ∈ P ∧ q = q₁.append q₂ ∧ (∀ u ∈ q₁.support, u ∈ P → u = z) := by
  induction q with
  | nil =>
    exact ⟨_, Walk.nil, Walk.nil, hc, rfl, fun u hu _ => by simp only [Walk.support_nil, List.mem_singleton] at hu; exact hu⟩
  | @cons a b c h q' ih =>
    by_cases ha : a ∈ P
    · exact ⟨a, Walk.nil, Walk.cons h q', ha, rfl, fun u hu _ => by simp only [Walk.support_nil, List.mem_singleton] at hu; exact hu⟩
    · obtain ⟨z, q₁, q₂, hz, hq', huniq⟩ := ih hc
      refine ⟨z, Walk.cons h q₁, q₂, hz, by rw [hq']; rfl, fun u hu huP => ?_⟩
      simp only [Walk.support_cons, List.mem_cons] at hu
      rcases hu with rfl | hu
      · exact False.elim (ha huP)
      · exact huniq u hu huP

lemma start_notMem_tail_support_of_isPath {U : Type} {T : SimpleGraph U} {a b : U}
    {w : T.Walk a b} (hw : w.IsPath) : a ∉ w.support.tail := by
  cases w <;> simp_all [Walk.isPath_def]

lemma length_walk_induce {U : Type*} (T : SimpleGraph U) (S : Set U) {a b : U}
    (p : T.Walk a b) (hp : ∀ x ∈ p.support, x ∈ S) :
    (p.induce S hp).length = p.length := by
  have h := congrArg Walk.length (Walk.map_induce p hp)
  rwa [Walk.length_map] at h

lemma degree_induce_compl_singleton_of_adj {U : Type} [Fintype U]
    (T : SimpleGraph U) {a v : U} (hav : a ∈ ({v}ᶜ : Set U)) (hadj : T.Adj a v) :
    (T.induce {v}ᶜ).degree ⟨a, hav⟩ + 1 = T.degree a := by
  let f : ({v}ᶜ : Set U) ↪ U := ⟨Subtype.val, Subtype.val_injective⟩
  have hmap_not : v ∉ ((T.induce {v}ᶜ).neighborFinset ⟨a, hav⟩).map f := by
    intro h
    rw [Finset.mem_map] at h
    obtain ⟨x, _, hxv⟩ := h
    exact x.2 hxv
  have heq : insert v (((T.induce {v}ᶜ).neighborFinset ⟨a, hav⟩).map f) = T.neighborFinset a := by
    ext y
    rw [Finset.mem_insert, Finset.mem_map, SimpleGraph.mem_neighborFinset]
    constructor
    · rintro (rfl | ⟨x, hx, rfl⟩)
      · exact hadj
      · rw [SimpleGraph.mem_neighborFinset] at hx
        exact hx
    · intro hay
      by_cases hyv : y = v
      · exact Or.inl hyv
      · refine Or.inr ⟨⟨y, hyv⟩, ?_, rfl⟩
        rw [SimpleGraph.mem_neighborFinset]
        exact hay
  have hcard := congrArg Finset.card heq
  rw [Finset.card_insert_of_notMem hmap_not, Finset.card_map,
    (T.induce {v}ᶜ).card_neighborFinset_eq_degree, T.card_neighborFinset_eq_degree] at hcard
  omega

lemma degree_induce_compl_singleton_of_not_adj {U : Type} [Fintype U]
    (T : SimpleGraph U) {a v : U} (hav : a ∈ ({v}ᶜ : Set U)) (hnadj : ¬ T.Adj a v) :
    (T.induce {v}ᶜ).degree ⟨a, hav⟩ = T.degree a := by
  let f : ({v}ᶜ : Set U) ↪ U := ⟨Subtype.val, Subtype.val_injective⟩
  have heq : ((T.induce {v}ᶜ).neighborFinset ⟨a, hav⟩).map f = T.neighborFinset a := by
    ext y
    rw [Finset.mem_map, SimpleGraph.mem_neighborFinset]
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [SimpleGraph.mem_neighborFinset] at hx
      exact hx
    · intro hay
      have hyv : y ≠ v := fun h => hnadj (h ▸ hay)
      refine ⟨⟨y, hyv⟩, ?_, rfl⟩
      rw [SimpleGraph.mem_neighborFinset]
      exact hay
  have hcard := congrArg Finset.card heq
  rw [Finset.card_map, (T.induce {v}ᶜ).card_neighborFinset_eq_degree,
    T.card_neighborFinset_eq_degree] at hcard
  exact hcard

lemma degree_induce_compl_le {U : Type} [Fintype U]
    (T : SimpleGraph U) {a v : U} (hav : a ∈ ({v}ᶜ : Set U)) :
    (T.induce {v}ᶜ).degree ⟨a, hav⟩ ≤ T.degree a := by
  by_cases hadj : T.Adj a v
  · have := degree_induce_compl_singleton_of_adj T hav hadj
    omega
  · rw [degree_induce_compl_singleton_of_not_adj T hav hadj]

lemma induce_compl_singleton_isTree_of_deg_one {U : Type} [Fintype U]
    (T : SimpleGraph U) (hT : T.IsTree) {v : U} (hdeg1 : T.degree v = 1) :
    (T.induce {v}ᶜ).IsTree :=
  ⟨hT.connected.induce_compl_singleton_of_degree_eq_one hdeg1, hT.isAcyclic.induce {v}ᶜ⟩

lemma induce_compl_singleton_dist_eq {U : Type} [Fintype U]
    (T : SimpleGraph U) (hT : T.IsTree) {v : U} (hT' : (T.induce {v}ᶜ).IsTree)
    (a b : ({v}ᶜ : Set U)) :
    (T.induce {v}ᶜ).dist a b = T.dist a.1 b.1 := by
  obtain ⟨p, hp, hplen⟩ := hT'.connected.exists_path_of_dist a b
  let g : T.induce {v}ᶜ →g T := (SimpleGraph.Embedding.induce ({v}ᶜ : Set U)).toHom
  have hmap : (p.map g).IsPath := hp.map Subtype.val_injective
  have hdist := isTree_dist_eq_length_of_isPath T hT (p.map g) hmap
  rw [Walk.length_map, hplen] at hdist
  exact hdist

lemma induce_compl_singleton_diam_le {U : Type} [Fintype U]
    (T : SimpleGraph U) (hT : T.IsTree) {v : U} (hdeg1 : T.degree v = 1) :
    (T.induce {v}ᶜ).diam ≤ T.diam := by
  have : Nonempty U := hT.connected.nonempty
  have hT' : (T.induce {v}ᶜ).IsTree := induce_compl_singleton_isTree_of_deg_one T hT hdeg1
  have : Nonempty ({v}ᶜ : Set U) := hT'.connected.nonempty
  obtain ⟨a, b, hab⟩ := (T.induce {v}ᶜ).exists_dist_eq_diam
  rw [← hab, induce_compl_singleton_dist_eq T hT hT']
  exact dist_le_diam (connected_iff_ediam_ne_top.mp hT.connected)

lemma good_leaf_of_ne_diam_ends {U : Type} [Fintype U] (T : SimpleGraph U) (hT : T.IsTree)
    {r : ℕ} (_hr : 2 ≤ r) (hdiam : T.diam = 2 * r) {x0 xd : U} (hxd : T.dist x0 xd = 2 * r)
    {v : U} (hv1 : T.degree v = 1) (hx0 : v ≠ x0) (hxd_ne : v ≠ xd) :
    (T.induce {v}ᶜ).diam = 2 * r := by
  obtain ⟨p, hp, hplen⟩ := hT.connected.exists_path_of_dist x0 xd
  have hnot : v ∉ p.support := by
    intro hv_mem
    obtain ⟨q, s, hq, hs, hp_eq⟩ := hp.mem_support_iff_exists_append.mp hv_mem
    have hq_nn : ¬ q.Nil := Walk.not_nil_of_ne hx0.symm
    have hs_nn : ¬ s.Nil := Walk.not_nil_of_ne hxd_ne
    have hadj1 : T.Adj v q.penultimate := (q.adj_penultimate hq_nn).symm
    have hadj2 : T.Adj v s.snd := s.adj_snd hs_nn
    have hne12 : q.penultimate ≠ s.snd := by
      have hdisj : q.support.Disjoint s.tail.support := by
        have h1 := (hp_eq ▸ hp).support_nodup
        rw [Walk.support_append, List.nodup_append', ← Walk.support_tail_of_not_nil s hs_nn] at h1
        exact h1.2.2
      have hm1 : q.penultimate ∈ q.support := Walk.getVert_mem_support q (q.length - 1)
      have hm2 : s.snd ∈ s.tail.support := by
        rw [Walk.support_tail_of_not_nil s hs_nn]
        exact s.snd_mem_tail_support hs_nn
      intro heq
      rw [heq] at hm1
      exact hdisj hm1 hm2
    have h2 : 2 ≤ T.degree v := by
      rw [← T.card_neighborFinset_eq_degree]
      have hsub : {q.penultimate, s.snd} ⊆ T.neighborFinset v := by
        intro z hz
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rw [SimpleGraph.mem_neighborFinset]
        rcases hz with rfl | rfl <;> assumption
      calc
        2 = ({q.penultimate, s.snd} : Finset U).card := (Finset.card_pair hne12).symm
        _ ≤ (T.neighborFinset v).card := Finset.card_le_card hsub
    omega
  have hw_supp : ∀ x ∈ p.support, x ∈ ({v}ᶜ : Set U) := fun x hx =>
    Set.mem_compl_singleton_iff.mpr fun heq => hnot (heq ▸ hx)
  let p' := p.induce ({v}ᶜ : Set U) hw_supp
  have hp' : p'.IsPath := by
    refine Walk.IsPath.of_map (f := (SimpleGraph.Embedding.induce ({v}ᶜ : Set U)).toHom) ?_
    rw [Walk.map_induce]
    exact hp
  have hT' : (T.induce {v}ᶜ).IsTree := induce_compl_singleton_isTree_of_deg_one T hT hv1
  have : Nonempty ({v}ᶜ : Set U) := hT'.connected.nonempty
  have hdist : (T.induce {v}ᶜ).dist ⟨x0, hw_supp x0 p.start_mem_support⟩
      ⟨xd, hw_supp xd p.end_mem_support⟩ = 2 * r := by
    have h1 := isTree_dist_eq_length_of_isPath (T.induce {v}ᶜ) hT' p' hp'
    rw [← h1, length_walk_induce, hplen, hxd]
  have hediam' : (T.induce {v}ᶜ).ediam ≠ ⊤ := connected_iff_ediam_ne_top.mp hT'.connected
  have hge : 2 * r ≤ (T.induce {v}ᶜ).diam := hdist ▸ dist_le_diam hediam'
  have hle : (T.induce {v}ᶜ).diam ≤ 2 * r := hdiam ▸ induce_compl_singleton_diam_le T hT hv1
  omega

lemma existsUnique_root_of_component {U : Type} [Fintype U]
    (T : SimpleGraph U) (hT : T.IsTree) (c : U)
    (C : (T.induce {c}ᶜ).ConnectedComponent) :
    ∃! u : ({c}ᶜ : Set U), u ∈ C.supp ∧ T.Adj c u.1 := by
  obtain ⟨z, hz⟩ := C.nonempty_supp
  have hzc : z.1 ≠ c := z.2
  obtain ⟨p, hp, _⟩ := hT.connected.exists_path_of_dist c z.1
  have hnp : ¬ p.Nil := Walk.not_nil_of_ne hzc.symm
  let uVal : U := p.snd
  have hadj : T.Adj c uVal := p.adj_snd hnp
  have huc : uVal ∈ ({c}ᶜ : Set U) := Set.mem_compl_singleton_iff.mpr hadj.ne.symm
  let u : ({c}ᶜ : Set U) := ⟨uVal, huc⟩
  have hsupp_tail : ∀ x ∈ p.tail.support, x ∈ ({c}ᶜ : Set U) := by
    intro x hx
    rw [Walk.support_tail_of_not_nil p hnp] at hx
    exact Set.mem_compl_singleton_iff.mpr fun hxc =>
      start_notMem_tail_support_of_isPath hp (hxc ▸ hx)
  let p' : (T.induce {c}ᶜ).Walk u z :=
    (p.tail.induce ({c}ᶜ : Set U) hsupp_tail).copy rfl (Subtype.ext rfl)
  have hreach : (T.induce {c}ᶜ).Reachable u z := ⟨p'⟩
  have hu_mem : u ∈ C.supp := by
    rw [ConnectedComponent.mem_supp_iff] at hz ⊢
    exact (ConnectedComponent.sound hreach).trans hz
  refine ⟨u, ⟨hu_mem, hadj⟩, fun u' ⟨hu'_mem, hadj'⟩ => ?_⟩
  by_contra hne
  have hne_val : uVal ≠ u'.1 := fun h => hne (Subtype.ext h).symm
  obtain ⟨q⟩ := C.reachable_of_mem_supp hu_mem hu'_mem
  let q_path := q.toPath
  let g : T.induce {c}ᶜ →g T := (SimpleGraph.Embedding.induce ({c}ᶜ : Set U)).toHom
  have hqG : (q_path.val.map g).IsPath := q_path.isPath.map Subtype.val_injective
  have hc_not_q : c ∉ (q_path.val.map g).support := by
    rw [Walk.support_map, List.mem_map]
    rintro ⟨x, _, hxc⟩
    exact x.2 hxc
  let two_step : T.Walk uVal u'.1 := Walk.cons hadj.symm (Walk.cons hadj' Walk.nil)
  have htwo_path : two_step.IsPath := by
    simp [two_step, Walk.cons_isPath_iff, hne_val, hadj.ne.symm, hadj'.ne]
  have heq := isTree_path_eq T hT hqG htwo_path
  have hc_in : c ∈ two_step.support := by simp [two_step]
  rw [← heq] at hc_in
  exact hc_not_q hc_in

lemma component_toSimpleGraph_degree {U : Type} [Fintype U]
    (T : SimpleGraph U) (c : U) (C : (T.induce {c}ᶜ).ConnectedComponent) (x : C.supp) :
    C.toSimpleGraph.degree x = (T.induce {c}ᶜ).degree x.1 := by
  let f : C.supp ↪ ({c}ᶜ : Set U) := ⟨Subtype.val, Subtype.val_injective⟩
  have heq : (C.toSimpleGraph.neighborFinset x).map f = (T.induce {c}ᶜ).neighborFinset x.1 := by
    ext y
    rw [Finset.mem_map, SimpleGraph.mem_neighborFinset]
    constructor
    · rintro ⟨z, hz, rfl⟩
      rw [SimpleGraph.mem_neighborFinset] at hz
      exact hz
    · intro hxy
      have hy : y ∈ C.supp := C.mem_supp_of_adj_mem_supp x.2 hxy
      refine ⟨⟨y, hy⟩, ?_, rfl⟩
      rw [SimpleGraph.mem_neighborFinset]
      exact hxy
  have hcard := congrArg Finset.card heq
  rw [Finset.card_map, C.toSimpleGraph.card_neighborFinset_eq_degree,
    (T.induce {c}ᶜ).card_neighborFinset_eq_degree] at hcard
  exact hcard

lemma component_degree_sum {U : Type} [Fintype U]
    (T : SimpleGraph U) (hT : T.IsTree) (c : U)
    (C : (T.induce {c}ᶜ).ConnectedComponent) :
    ∑ x : C.supp, T.degree x.1.1 = 2 * Fintype.card C.supp - 1 := by
  obtain ⟨u, ⟨hu_mem, hu_adj⟩, hu_uniq⟩ := existsUnique_root_of_component T hT c C
  let uC : C.supp := ⟨u, hu_mem⟩
  have hdeg_eq : ∀ x : C.supp,
      T.degree x.1.1 = C.toSimpleGraph.degree x + (if x = uC then 1 else 0) := by
    intro x
    rw [component_toSimpleGraph_degree T c C x]
    split_ifs with hxu
    · subst hxu
      exact (degree_induce_compl_singleton_of_adj T u.2 hu_adj.symm).symm
    · have hnadj : ¬ T.Adj x.1.1 c := by
        intro hadj
        have hxeq : x.1 = u := hu_uniq x.1 ⟨x.2, hadj.symm⟩
        exact hxu (Subtype.ext hxeq)
      exact (degree_induce_compl_singleton_of_not_adj T x.1.2 hnadj).symm
  have hsum : ∑ x : C.supp, T.degree x.1.1 =
      (∑ x : C.supp, C.toSimpleGraph.degree x) + ∑ x : C.supp, (if x = uC then 1 else 0) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun x _ => hdeg_eq x
  have hC_tree : C.toSimpleGraph.IsTree :=
    (hT.isAcyclic.induce {c}ᶜ).isTree_connectedComponent C
  have hdeg_sum : (∑ x : C.supp, C.toSimpleGraph.degree x) = 2 * C.toSimpleGraph.edgeFinset.card := by
    convert C.toSimpleGraph.sum_degrees_eq_twice_card_edges
    all_goals exact Iff.rfl
  rw [hdeg_sum] at hsum
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte] at hsum
  have hC_edges : C.toSimpleGraph.edgeFinset.card + 1 = Fintype.card C.supp := by
    convert hC_tree.card_edgeFinset
    all_goals exact Iff.rfl
  have hC_pos : 1 ≤ Fintype.card C.supp := Fintype.card_pos_iff.mpr ⟨uC⟩
  omega

lemma component_leaves_formula {U : Type} [Fintype U]
    (T : SimpleGraph U) (hT : T.IsTree) (c : U)
    (C : (T.induce {c}ᶜ).ConnectedComponent) :
    let LC := Finset.univ.filter fun x : C.supp => T.degree x.1.1 = 1
    LC.card = 1 + ∑ x ∈ LCᶜ, (T.degree x.1.1 - 2) ∧
      ∀ x ∈ LCᶜ, 2 ≤ T.degree x.1.1 := by
  have hT_pos : ∀ v : U, 1 ≤ T.degree v := by
    intro v
    obtain ⟨w, _⟩ := C.nonempty_supp
    have hwc : c ≠ w.1 := fun h => w.2 (h.symm)
    have : Nontrivial U := ⟨⟨c, w.1, hwc⟩⟩
    exact hT.preconnected.degree_pos_of_nontrivial v
  let LC : Finset C.supp := Finset.univ.filter fun x : C.supp => T.degree x.1.1 = 1
  have hge2 : ∀ x ∈ LCᶜ, 2 ≤ T.degree x.1.1 := by
    intro x hx
    simp only [LC, Finset.mem_compl, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    have := hT_pos x.1.1
    omega
  have hsum := component_degree_sum T hT c C
  have hsplit : (∑ x ∈ LC, T.degree x.1.1) + ∑ x ∈ LCᶜ, T.degree x.1.1 = ∑ x : C.supp, T.degree x.1.1 :=
    Finset.sum_add_sum_compl LC (fun x => T.degree x.1.1)
  have hsum_L : ∑ x ∈ LC, T.degree x.1.1 = LC.card := by
    calc
      ∑ x ∈ LC, T.degree x.1.1 = ∑ _x ∈ LC, 1 := Finset.sum_congr rfl fun x hx => (Finset.mem_filter.mp hx).2
      _ = LC.card := by simp
  have hsum_Lc : ∑ x ∈ LCᶜ, T.degree x.1.1 = 2 * LCᶜ.card + ∑ x ∈ LCᶜ, (T.degree x.1.1 - 2) := by
    calc
      ∑ x ∈ LCᶜ, T.degree x.1.1 = ∑ x ∈ LCᶜ, (2 + (T.degree x.1.1 - 2)) :=
        Finset.sum_congr rfl fun x hx => by have := hge2 x hx; omega
      _ = (∑ _x ∈ LCᶜ, 2) + ∑ x ∈ LCᶜ, (T.degree x.1.1 - 2) := Finset.sum_add_distrib
      _ = 2 * LCᶜ.card + ∑ x ∈ LCᶜ, (T.degree x.1.1 - 2) := by simp [mul_comm]
  have hcard_compl : LC.card + LCᶜ.card = Fintype.card C.supp := by
    rw [Finset.card_compl]
    have : LC.card ≤ Fintype.card C.supp := Finset.card_le_univ LC
    omega
  have hC_pos : 1 ≤ Fintype.card C.supp := by
    obtain ⟨w, hw⟩ := C.nonempty_supp
    exact Fintype.card_pos_iff.mpr ⟨⟨w, hw⟩⟩
  refine ⟨?_, hge2⟩
  change LC.card = 1 + ∑ x ∈ LCᶜ, (T.degree x.1.1 - 2)
  omega

lemma diam_path_contains_center {U : Type} [Fintype U]
    (T : SimpleGraph U) (hT : T.IsTree) {r : ℕ} (c : U) (hecc : T.eccent c = r)
    {x0 xd : U} (p : T.Walk x0 xd) (hp : p.IsPath) (hplen : p.length = 2 * r) :
    c ∈ p.support ∧ T.dist c x0 = r ∧ T.dist c xd = r := by
  obtain ⟨q1, hq1, hq1len⟩ := hT.connected.exists_path_of_dist x0 c
  obtain ⟨q2, hq2, hq2len⟩ := hT.connected.exists_path_of_dist c xd
  have h1 : T.dist x0 c ≤ r := Nat.cast_le.mp (by
    rw [(hT.connected x0 c).coe_dist_eq_edist, SimpleGraph.edist_comm, ← hecc]
    exact SimpleGraph.edist_le_eccent)
  have h2 : T.dist c xd ≤ r := Nat.cast_le.mp (by
    rw [(hT.connected c xd).coe_dist_eq_edist, ← hecc]
    exact SimpleGraph.edist_le_eccent)
  have hpdist : p.length = T.dist x0 xd := isTree_dist_eq_length_of_isPath T hT p hp
  have htri := hT.connected.dist_triangle (u := x0) (v := c) (w := xd)
  have h1eq : T.dist x0 c = r := by omega
  have h2eq : T.dist c xd = r := by omega
  have hq12_len : (q1.append q2).length = T.dist x0 xd := by
    rw [Walk.length_append, hq1len, hq2len, h1eq, h2eq, ← hpdist, hplen]
    omega
  have hq12_path : (q1.append q2).IsPath :=
    (q1.append q2).isPath_of_length_eq_dist hq12_len
  have heq : q1.append q2 = p := isTree_path_eq T hT hq12_path hp
  have hc_mem : c ∈ p.support := by
    rw [← heq, Walk.mem_support_append_iff]
    exact Or.inl q1.end_mem_support
  rw [SimpleGraph.dist_comm] at h1eq
  exact ⟨hc_mem, h1eq, h2eq⟩

lemma card_component_eq_radius_of_unique_leaf {U : Type} [Fintype U]
    (T : SimpleGraph U) (hT : T.IsTree) {r : ℕ} (hr : 2 ≤ r) (c : U)
    (C : (T.induce {c}ᶜ).ConnectedComponent)
    {x_end : ({c}ᶜ : Set U)} (hx_mem : x_end ∈ C.supp)
    (hx_dist : T.dist c x_end.1 = r)
    (h_all_le2 : ∀ x : C.supp, T.degree x.1.1 ≤ 2)
    (h_uniq_leaf : ∀ x : C.supp, T.degree x.1.1 = 1 → x.1 = x_end) :
    Fintype.card C.supp = r := by
  obtain ⟨u, ⟨hu_mem, hu_adj⟩, hu_uniq⟩ := existsUnique_root_of_component T hT c C
  let uC : C.supp := ⟨u, hu_mem⟩
  let xC : C.supp := ⟨x_end, hx_mem⟩
  have hux_ne : uC ≠ xC := by
    intro h
    have hval : u.1 = x_end.1 := congrArg (fun y : C.supp => y.1.1) h
    have hd : T.dist c u.1 = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hu_adj
    rw [hval, hx_dist] at hd
    omega
  obtain ⟨p, hp, hplen⟩ := hT.connected.exists_path_of_dist c x_end.1
  have hp_len : p.length = r := hplen.trans hx_dist
  have hnp : ¬ p.Nil := Walk.not_nil_of_ne (fun h => by rw [← h, SimpleGraph.dist_self] at hx_dist; omega)
  have p_tail_supp : ∀ y ∈ p.tail.support, y ∈ ({c}ᶜ : Set U) := by
    intro y hy
    rw [Walk.support_tail_of_not_nil p hnp] at hy
    exact Set.mem_compl_singleton_iff.mpr fun hyc =>
      start_notMem_tail_support_of_isPath hp (hyc ▸ hy)
  have hsnd : (⟨p.snd, p_tail_supp p.snd (Walk.start_mem_support _)⟩ : ({c}ᶜ : Set U)) = u := by
    have hreach : (T.induce {c}ᶜ).Reachable ⟨p.snd, p_tail_supp p.snd (Walk.start_mem_support _)⟩ x_end :=
      ⟨(p.tail.induce ({c}ᶜ : Set U) p_tail_supp).copy rfl (Subtype.ext rfl)⟩
    have hsnd_mem : (⟨p.snd, p_tail_supp p.snd (Walk.start_mem_support _)⟩ : ({c}ᶜ : Set U)) ∈ C.supp := by
      rw [ConnectedComponent.mem_supp_iff] at hx_mem ⊢
      exact (ConnectedComponent.sound hreach).trans hx_mem
    exact hu_uniq ⟨p.snd, _⟩ ⟨hsnd_mem, p.adj_snd hnp⟩
  let p' : (T.induce {c}ᶜ).Walk u x_end :=
    (p.tail.induce ({c}ᶜ : Set U) p_tail_supp).copy hsnd (Subtype.ext rfl)
  have hp' : p'.IsPath := by
    rw [Walk.isPath_copy]
    refine Walk.IsPath.of_map (f := (SimpleGraph.Embedding.induce ({c}ᶜ : Set U)).toHom) ?_
    rw [Walk.map_induce]
    exact hp.tail
  have hp'_len : p'.length = r - 1 := by
    rw [Walk.length_copy, length_walk_induce, Walk.length_tail, hp_len]
  have hC_tree : C.toSimpleGraph.IsTree :=
    (hT.isAcyclic.induce {c}ᶜ).isTree_connectedComponent C
  have hp'_mem_C : ∀ z ∈ p'.support, z ∈ C.supp := by
    intro z hz
    obtain ⟨q1, _, _, _, _⟩ := hp'.mem_support_iff_exists_append.mp hz
    have hreach : (T.induce {c}ᶜ).Reachable u z := ⟨q1⟩
    rw [ConnectedComponent.mem_supp_iff] at hu_mem ⊢
    exact (ConnectedComponent.sound hreach).symm.trans hu_mem
  let pC_ind : ((T.induce {c}ᶜ).induce C.supp).Walk uC xC := p'.induce C.supp hp'_mem_C
  have hpC_ind : pC_ind.IsPath := by
    refine Walk.IsPath.of_map (f := (SimpleGraph.Embedding.induce C.supp).toHom) ?_
    rw [Walk.map_induce]
    exact hp'
  have hpC_ind_len : pC_ind.length = r - 1 :=
    (length_walk_induce (T.induce {c}ᶜ) C.supp p' hp'_mem_C).trans hp'_len
  let pC : C.toSimpleGraph.Walk uC xC := pC_ind
  have hpC : pC.IsPath := hpC_ind
  have hpC_len : pC.length = r - 1 := hpC_ind_len
  have hdeg_uC : C.toSimpleGraph.degree uC = 1 := by
    rw [component_toSimpleGraph_degree T c C uC]
    dsimp only [uC]
    have h1 := degree_induce_compl_singleton_of_adj T u.2 hu_adj.symm
    rw [Subtype.coe_eta] at h1
    have hge1 : 1 ≤ (T.induce {c}ᶜ).degree u := by
      rw [← component_toSimpleGraph_degree T c C uC]
      have : Nontrivial C.supp := ⟨⟨uC, xC, hux_ne⟩⟩
      exact hC_tree.preconnected.degree_pos_of_nontrivial uC
    have hle2 : T.degree u.1 ≤ 2 := h_all_le2 uC
    omega
  have hdeg_xC : C.toSimpleGraph.degree xC = 1 := by
    rw [component_toSimpleGraph_degree T c C xC]
    have hx_nadj : ¬ T.Adj x_end.1 c := by
      intro hadj
      have hd : T.dist c x_end.1 = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hadj.symm
      rw [hx_dist] at hd
      omega
    rw [degree_induce_compl_singleton_of_not_adj T x_end.2 hx_nadj]
    have : Nontrivial C.supp := ⟨⟨uC, xC, hux_ne⟩⟩
    have hge1 : 1 ≤ T.degree x_end.1 := by
      rw [← degree_induce_compl_singleton_of_not_adj T x_end.2 hx_nadj,
        ← component_toSimpleGraph_degree T c C xC]
      exact hC_tree.preconnected.degree_pos_of_nontrivial xC
    have hle1 : ¬ 2 ≤ T.degree x_end.1 := by
      intro h2
      obtain ⟨hLC_eq, _⟩ := component_leaves_formula T hT c C
      let LC : Finset C.supp := Finset.univ.filter fun x : C.supp => T.degree x.1.1 = 1
      have hpos : 0 < LC.card := by dsimp [LC] at hLC_eq ⊢; omega
      obtain ⟨w, hw⟩ := Finset.card_pos.mp hpos
      simp only [LC, Finset.mem_filter, Finset.mem_univ, true_and] at hw
      have hwx : w.1 = x_end := h_uniq_leaf w hw
      rw [hwx] at hw
      omega
    omega
  have hdeg_int : ∀ y : C.supp, y ≠ uC → y ≠ xC → C.toSimpleGraph.degree y ≤ 2 := by
    intro y _ _
    rw [component_toSimpleGraph_degree T c C y]
    exact (degree_induce_compl_le T y.1.2).trans (h_all_le2 y)
  have hsupp_eq : ∀ y : C.supp, y ∈ pC.support := by
    intro y
    by_contra hy
    obtain ⟨q, hq, _⟩ := hC_tree.connected.exists_path_of_dist y uC
    obtain ⟨z, q₁, _, hz_mem, hq_eq, hq_first⟩ :=
      split_walk_first_mem C.toSimpleGraph {w | w ∈ pC.support} q pC.start_mem_support
    have hq1_nn : ¬ q₁.Nil := Walk.not_nil_of_ne (fun h => hy (h ▸ hz_mem))
    have hadj_z : C.toSimpleGraph.Adj z q₁.penultimate := (q₁.adj_penultimate hq1_nn).symm
    have hpen_not : q₁.penultimate ∉ pC.support := by
      intro hm
      have hmem1 : q₁.penultimate ∈ q₁.support := Walk.getVert_mem_support q₁ (q₁.length - 1)
      have heq : q₁.penultimate = z := hq_first q₁.penultimate hmem1 hm
      exact C.toSimpleGraph.ne_of_adj hadj_z heq.symm
    by_cases hzu : z = uC
    · subst hzu
      have hpC_nn : ¬ pC.Nil := Walk.not_nil_of_ne hux_ne
      have hadj_p : C.toSimpleGraph.Adj uC pC.snd := pC.adj_snd hpC_nn
      have hsnd_mem : pC.snd ∈ pC.support := List.mem_of_mem_tail (pC.snd_mem_tail_support hpC_nn)
      have hne : pC.snd ≠ q₁.penultimate := fun h => hpen_not (h ▸ hsnd_mem)
      have h2 : 2 ≤ C.toSimpleGraph.degree uC := by
        rw [← C.toSimpleGraph.card_neighborFinset_eq_degree]
        have hsub : {pC.snd, q₁.penultimate} ⊆ C.toSimpleGraph.neighborFinset uC := by
          intro a ha
          simp only [Finset.mem_insert, Finset.mem_singleton] at ha
          rw [SimpleGraph.mem_neighborFinset]
          rcases ha with rfl | rfl <;> assumption
        calc
          2 = ({pC.snd, q₁.penultimate} : Finset C.supp).card := (Finset.card_pair hne).symm
          _ ≤ (C.toSimpleGraph.neighborFinset uC).card := Finset.card_le_card hsub
      omega
    · by_cases hzx : z = xC
      · subst hzx
        have hpC_nn : ¬ pC.Nil := Walk.not_nil_of_ne hux_ne
        have hadj_p : C.toSimpleGraph.Adj xC pC.penultimate := (pC.adj_penultimate hpC_nn).symm
        have hpen_p_mem : pC.penultimate ∈ pC.support := Walk.getVert_mem_support pC (pC.length - 1)
        have hne : pC.penultimate ≠ q₁.penultimate := fun h => hpen_not (h ▸ hpen_p_mem)
        have h2 : 2 ≤ C.toSimpleGraph.degree xC := by
          rw [← C.toSimpleGraph.card_neighborFinset_eq_degree]
          have hsub : {pC.penultimate, q₁.penultimate} ⊆ C.toSimpleGraph.neighborFinset xC := by
            intro a ha
            simp only [Finset.mem_insert, Finset.mem_singleton] at ha
            rw [SimpleGraph.mem_neighborFinset]
            rcases ha with rfl | rfl <;> assumption
          calc
            2 = ({pC.penultimate, q₁.penultimate} : Finset C.supp).card := (Finset.card_pair hne).symm
            _ ≤ (C.toSimpleGraph.neighborFinset xC).card := Finset.card_le_card hsub
        omega
      · obtain ⟨a, b, ha, hb, hpC_eq⟩ := hpC.mem_support_iff_exists_append.mp hz_mem
        have ha_nn : ¬ a.Nil := Walk.not_nil_of_ne (fun h => hzu h.symm)
        have hb_nn : ¬ b.Nil := Walk.not_nil_of_ne hzx
        have hadj1 : C.toSimpleGraph.Adj z a.penultimate := (a.adj_penultimate ha_nn).symm
        have hadj2 : C.toSimpleGraph.Adj z b.snd := b.adj_snd hb_nn
        have ha_pen_mem : a.penultimate ∈ a.support := Walk.getVert_mem_support a (a.length - 1)
        have hm1 : a.penultimate ∈ pC.support := hpC_eq ▸ Walk.support_subset_support_append_left a b ha_pen_mem
        have hm2 : b.snd ∈ pC.support := hpC_eq ▸ Walk.support_subset_support_append_right a b (List.mem_of_mem_tail (b.snd_mem_tail_support hb_nn))
        have hne12 : a.penultimate ≠ b.snd := by
          have hdisj : a.support.Disjoint b.tail.support := by
            have h1 := (hpC_eq ▸ hpC).support_nodup
            rw [Walk.support_append, List.nodup_append', ← Walk.support_tail_of_not_nil b hb_nn] at h1
            exact h1.2.2
          have hb_snd : b.snd ∈ b.tail.support := by
            rw [Walk.support_tail_of_not_nil b hb_nn]
            exact b.snd_mem_tail_support hb_nn
          intro heq
          rw [heq] at ha_pen_mem
          exact hdisj ha_pen_mem hb_snd
        have hne13 : a.penultimate ≠ q₁.penultimate := fun h => hpen_not (h ▸ hm1)
        have hne23 : b.snd ≠ q₁.penultimate := fun h => hpen_not (h ▸ hm2)
        have h3 : 3 ≤ C.toSimpleGraph.degree z := by
          rw [← C.toSimpleGraph.card_neighborFinset_eq_degree]
          have hsub : {a.penultimate, b.snd, q₁.penultimate} ⊆ C.toSimpleGraph.neighborFinset z := by
            intro w hw
            simp only [Finset.mem_insert, Finset.mem_singleton] at hw
            rw [SimpleGraph.mem_neighborFinset]
            rcases hw with rfl | rfl | rfl <;> assumption
          have hc3 : ({a.penultimate, b.snd, q₁.penultimate} : Finset C.supp).card = 3 := by
            rw [Finset.card_insert_of_notMem, Finset.card_pair hne23]
            simp [hne12, hne13]
          exact hc3 ▸ Finset.card_le_card hsub
        have := hdeg_int z hzu hzx
        omega
  have hsupp_ind : ∀ y : C.supp, y ∈ pC_ind.support := hsupp_eq
  have hcard_eq : Fintype.card C.supp = pC_ind.support.toFinset.card := by
    have huniv : pC_ind.support.toFinset = Finset.univ :=
      Finset.eq_univ_iff_forall.mpr fun y => List.mem_toFinset.mpr (hsupp_ind y)
    rw [huniv, Finset.card_univ]
  rw [hcard_eq, List.toFinset_card_of_nodup hpC_ind.support_nodup, pC_ind.length_support, hpC_ind_len]
  omega

lemma card_connectedComponent_eq_degree {U : Type} [Fintype U]
    (T : SimpleGraph U) (hT : T.IsTree) (c : U) :
    Fintype.card (T.induce {c}ᶜ).ConnectedComponent = T.degree c := by
  let f : (T.induce {c}ᶜ).ConnectedComponent → T.neighborFinset c := fun C =>
    let u := (existsUnique_root_of_component T hT c C).choose
    ⟨u.1, (T.mem_neighborFinset c u.1).mpr (existsUnique_root_of_component T hT c C).choose_spec.1.2⟩
  let g : T.neighborFinset c → (T.induce {c}ᶜ).ConnectedComponent := fun u =>
    (T.induce {c}ᶜ).connectedComponentMk ⟨u.1, Set.mem_compl_singleton_iff.mpr ((T.mem_neighborFinset c u.1).mp u.2).ne.symm⟩
  have hleft : Function.LeftInverse g f := by
    intro C
    dsimp only [f, g]
    have hu := (existsUnique_root_of_component T hT c C).choose_spec.1.1
    exact (ConnectedComponent.mem_supp_iff C _).mp hu
  have hright : Function.RightInverse g f := by
    intro u
    dsimp only [f, g]
    apply Subtype.ext
    have hadj : T.Adj c u.1 := (T.mem_neighborFinset c u.1).mp u.2
    have huc : u.1 ∈ ({c}ᶜ : Set U) := Set.mem_compl_singleton_iff.mpr hadj.ne.symm
    let u_sub : ({c}ᶜ : Set U) := ⟨u.1, huc⟩
    let C := (T.induce {c}ᶜ).connectedComponentMk u_sub
    have hu_mem : u_sub ∈ C.supp := rfl
    have h_eq := ((existsUnique_root_of_component T hT c C).choose_spec.2 u_sub ⟨hu_mem, hadj⟩).symm
    exact congrArg (fun z : ({c}ᶜ : Set U) => z.1) h_eq
  rw [Fintype.card_congr ⟨f, g, hleft, hright⟩, Fintype.card_coe, T.card_neighborFinset_eq_degree]

end OMA.GreenNotes

namespace OMA.TreeSingle

open SimpleGraph Classical

open OMA.GreenNotes

lemma dist_through_center {V : Type} (T : SimpleGraph V) (hT : T.IsTree)
    (c : V) {a b : ({c}ᶜ : Set V)}
    (hne : (T.induce {c}ᶜ).connectedComponentMk a ≠ (T.induce {c}ᶜ).connectedComponentMk b) :
    T.dist a.val b.val = T.dist c a.val + T.dist c b.val := by
  obtain ⟨p, hp, hlen⟩ := hT.connected.exists_path_of_dist a.val b.val
  have hcmem : c ∈ p.support := by
    by_contra h
    have hs : ∀ x ∈ p.support, x ∈ ({c}ᶜ : Set V) := by
      rintro x hx rfl
      exact h hx
    exact hne (ConnectedComponent.sound ⟨p.induce _ hs⟩)
  obtain ⟨q, s, hq, hs, hqs⟩ := hp.mem_support_iff_exists_append.mp hcmem
  rw [← hlen, hqs, Walk.length_append, isTree_dist_eq_length_of_isPath T hT q hq,
    isTree_dist_eq_length_of_isPath T hT s hs, (T.dist_comm (u := a.val) (v := c))]

-- The endpoint construction follows @green-notes, tree.R1.H3.R1.H2.
lemma center_pair {V : Type} [Fintype V] (T : SimpleGraph V) (hT : T.IsTree)
    {r : ℕ} (hr : 2 ≤ r) (hd : T.diam = 2*r) (c : V) (he : T.eccent c = r) :
    ∃ a b : ({c}ᶜ : Set V), T.dist a.val b.val = 2*r ∧ T.dist c a.val = r ∧
      T.dist c b.val = r ∧
      (T.induce {c}ᶜ).connectedComponentMk a ≠ (T.induce {c}ᶜ).connectedComponentMk b := by
  have : Nonempty V := hT.connected.nonempty
  obtain ⟨x, y, hxy⟩ := T.exists_dist_eq_diam
  obtain ⟨p, hp, hplen⟩ := hT.connected.exists_path_of_dist x y
  obtain ⟨hcm, hcx, hcy⟩ := diam_path_contains_center T hT c he p hp (hplen.trans (hxy.trans hd))
  have hx : x ≠ c := fun h => by rw [← h, SimpleGraph.dist_self] at hcx; omega
  have hy : y ≠ c := fun h => by rw [← h, SimpleGraph.dist_self] at hcy; omega
  let a : ({c}ᶜ : Set V) := ⟨x, hx⟩
  let b : ({c}ᶜ : Set V) := ⟨y, hy⟩
  refine ⟨a,b,hxy.trans hd,hcx,hcy,?_⟩
  intro h
  obtain ⟨q⟩ := ConnectedComponent.exact h
  let g : T.induce {c}ᶜ →g T := (SimpleGraph.Embedding.induce ({c}ᶜ : Set V)).toHom
  have hqp : q.toPath.val.map g = p :=
    isTree_path_eq T hT (q.toPath.isPath.map Subtype.val_injective) hp
  have hc : c ∉ (q.toPath.val.map g).support := by
    rw [Walk.support_map, List.mem_map]
    rintro ⟨z, _, hz⟩
    exact z.2 hz
  exact hc (hqp ▸ hcm)

lemma branch_leaf {V : Type} [Fintype V] (T : SimpleGraph V) (hT : T.IsTree)
    (c : V) (C : (T.induce {c}ᶜ).ConnectedComponent) : ∃ x : C.supp, T.degree x.1.1 = 1 := by
  obtain ⟨heq, _⟩ := component_leaves_formula T hT c C
  have pos : 0 < (Finset.univ.filter fun x : C.supp => T.degree x.1.1 = 1).card := by omega
  obtain ⟨x, hx⟩ := Finset.card_pos.mp pos
  exact ⟨x, (Finset.mem_filter.mp hx).2⟩

-- The leaf count and cardinality argument is adapted from @green-notes.
lemma unique_arm_card {V : Type} [Fintype V] (T : SimpleGraph V) (hT : T.IsTree)
    {r : ℕ} (hr : 2 ≤ r) (c : V) (C : (T.induce {c}ᶜ).ConnectedComponent)
    (a : ({c}ᶜ : Set V)) (ha : a ∈ C.supp) (hd : T.dist c a.val = r)
    (hu : ∀ x : C.supp, T.degree x.1.1 = 1 → x.1 = a) : C.supp.ncard ≤ r := by
  obtain ⟨heq, _⟩ := component_leaves_formula T hT c C
  let L := Finset.univ.filter fun x : C.supp => T.degree x.1.1 = 1
  have hsub : L ⊆ {⟨a,ha⟩} := by
    intro x hx
    exact Finset.mem_singleton.mpr (Subtype.ext (hu x (Finset.mem_filter.mp hx).2))
  have hle : L.card ≤ 1 := (Finset.card_le_card hsub).trans (by simp)
  have hsum : ∑ x ∈ Lᶜ, (T.degree x.1.1 - 2) = 0 := by
    dsimp [L] at hle heq ⊢
    omega
  have hdeg : ∀ x : C.supp, T.degree x.1.1 ≤ 2 := by
    intro x
    by_cases hx : x ∈ L
    · exact (Finset.mem_filter.mp hx).2.le.trans (by decide)
    · have hle' : T.degree x.1.1 - 2 ≤ ∑ y ∈ Lᶜ, (T.degree y.1.1 - 2) :=
        Finset.single_le_sum (f := fun y : C.supp => T.degree y.1.1 - 2)
          (fun _ _ => Nat.zero_le _) (Finset.mem_compl.mpr hx)
      omega
  rw [Set.ncard_eq_toFinset_card', Set.toFinset_card,
    card_component_eq_radius_of_unique_leaf T hT hr c C ha hd hdeg hu]

end OMA.TreeSingle

namespace OMA.TreeSingle

open SimpleGraph Classical

open OMA.GreenNotes

def Covers {V : Type} [Fintype V] (r : ℕ) (T : SimpleGraph V) (c : V) : Prop :=
  ∀ C : (T.induce {c}ᶜ).ConnectedComponent, ∃ v : ({c}ᶜ : Set V),
    v ∉ C.supp ∧ (T.neighborSet v.val).ncard=1 ∧ (T.induce {v.val}ᶜ).diam=2*r

def Long {V : Type} [Fintype V] (r : ℕ) (T : SimpleGraph V) (c : V) : Prop :=
  (T.neighborSet c).ncard=2 ∧ ∃ C : (T.induce {c}ᶜ).ConnectedComponent,
    (∃ v : C.supp, T.dist c v.val.val=r) ∧ C.supp.ncard ≤ r

def Pure {V : Type} [Fintype V] (r : ℕ) (T : SimpleGraph V) (c : V) : Prop :=
  ∀ C : (T.induce {c}ᶜ).ConnectedComponent, (∃ v : C.supp, T.dist c v.val.val=r) → C.supp.ncard ≤ r

theorem classify_single {V : Type} [Fintype V] (T : SimpleGraph V) (hT : T.IsTree)
    {r : ℕ} (hr : 2 ≤ r) (hdiam : T.diam = 2*r) (c : V) (hecc : T.eccent c = r)
    (hnc : ¬ Covers r T c) : Long r T c ∨ Pure r T c := by
  classical
  obtain ⟨E, hE⟩ := Classical.not_forall.mp hnc
  obtain ⟨a, b, hab, hca, hcb, hAB⟩ := center_pair T hT hr hdiam c hecc
  let A := (T.induce {c}ᶜ).connectedComponentMk a
  let B := (T.induce {c}ᶜ).connectedComponentMk b
  change A ≠ B at hAB
  have hmk {C : (T.induce {c}ᶜ).ConnectedComponent} (x : C.supp) :
      (T.induce {c}ᶜ).connectedComponentMk x.val = C := x.property
  have hends {C : (T.induce {c}ᶜ).ConnectedComponent} (hne : C ≠ E)
      (x : C.supp) (hx : T.degree x.val.val = 1) : x.val=a ∨ x.val=b := by
    by_contra! hn
    exact hE ⟨x.val, fun hxE => hne ((hmk x).symm.trans hxE),
      (ncard_neighborSet_eq_degree T _).trans hx,
      good_leaf_of_ne_diam_ends T hT hr hdiam hab hx
        (fun h => hn.1 (Subtype.ext h)) (fun h => hn.2 (Subtype.ext h))⟩
  have hclass (C : (T.induce {c}ᶜ).ConnectedComponent) : C=E ∨ C=A ∨ C=B := by
    by_cases h : C=E
    · exact Or.inl h
    obtain ⟨x,hx⟩ := branch_leaf T hT c C
    rcases hends h x hx with ha | hb
    · exact Or.inr (Or.inl ((hmk x).symm.trans (congrArg _ ha)))
    · exact Or.inr (Or.inr ((hmk x).symm.trans (congrArg _ hb)))
  have hua (h : A ≠ E) (x : A.supp) (hx : T.degree x.val.val=1) : x.val=a :=
    (hends h x hx).resolve_right (fun hb => hAB ((hmk x).symm.trans (congrArg _ hb)))
  have hub (h : B ≠ E) (x : B.supp) (hx : T.degree x.val.val=1) : x.val=b :=
    (hends h x hx).resolve_left (fun ha => hAB ((hmk x).symm.trans (congrArg _ ha)).symm)
  have hsmallA (h : A ≠ E) : A.supp.ncard ≤ r := unique_arm_card T hT hr c A a rfl hca (hua h)
  have hsmallB (h : B ≠ E) : B.supp.ncard ≤ r := unique_arm_card T hT hr c B b rfl hcb (hub h)
  have two (h : E=A ∨ E=B) : (T.neighborSet c).ncard=2 := by
    have hh : (Finset.univ : Finset (T.induce {c}ᶜ).ConnectedComponent) = {A,B} := by
      ext C
      simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
      rcases hclass C with h'|h'
      · exact h'.symm ▸ h
      · exact h'
    rw [ncard_neighborSet_eq_degree, ← card_connectedComponent_eq_degree T hT c,
      ← Finset.card_univ, hh, Finset.card_pair hAB]
  by_cases hEA : E=A
  · exact Or.inl ⟨two (Or.inl hEA), B, ⟨⟨b,rfl⟩,hcb⟩, hsmallB (fun h => hAB (hEA.symm.trans h.symm))⟩
  by_cases hEB : E=B
  · exact Or.inl ⟨two (Or.inr hEB), A, ⟨⟨a,rfl⟩,hca⟩, hsmallA (fun h => hAB (h.trans hEB))⟩
  right
  intro C hrad
  rcases hclass C with h | h | h
  · subst C
    obtain ⟨y,hy⟩ := hrad
    have hcross : T.dist y.val.val a.val=2*r := by
      rw [dist_through_center T hT c (fun h => hEA ((hmk y).symm.trans h)), hy, hca]
      omega
    obtain ⟨x,hx⟩ := branch_leaf T hT c B
    have hbx := hub (Ne.symm hEB) x hx
    have hbdeg : T.degree b.val=1 := by rw [← hbx]; exact hx
    have hgood := good_leaf_of_ne_diam_ends T hT hr hdiam hcross hbdeg
      (fun h => hEB ((hmk y).symm.trans (congrArg _ ((Subtype.ext h : b=y.val).symm))))
      (fun h => hAB (congrArg _ ((Subtype.ext h : b=a).symm)))
    exact False.elim (hE ⟨b,fun h => hEB (Eq.symm h),
      (ncard_neighborSet_eq_degree T _).trans hbdeg,hgood⟩)
  · exact h.symm ▸ hsmallA (Ne.symm hEA)
  · exact h.symm ▸ hsmallB (Ne.symm hEB)

end OMA.TreeSingle


/- Transporting rooted branches across a leaf-deleted card

The lemmas on distances and centers of cards below are adapted from the
Left to Solve contribution by @green-notes for tree.R1.H3.R1.H2. The branch
injection and transport of the cardinality bound are due to @Deldor14.
-/
open SimpleGraph
section
open Classical OMA.GreenNotes
private lemma isPath_append_of_first_meet {U : Type} {T : SimpleGraph U}
    {y z x : U} {q₁ : T.Walk y z} {s : T.Walk z x}
    (hq₁ : q₁.IsPath) (hs : s.IsPath)
    (hmeet : ∀ u ∈ q₁.support, u ∈ s.support.tail → u = z) :
    (q₁.append s).IsPath := by
  rw [Walk.isPath_def, Walk.support_append, List.nodup_append']
  refine ⟨hq₁.support_nodup, hs.support_nodup.tail, fun u huq hus => ?_⟩
  have huz : u = z := hmeet u huq hus
  subst huz
  exact start_notMem_tail_support_of_isPath hs hus

private lemma exists_unique_center_of_diam_eq_two_mul {U : Type} [Fintype U]
    (T : SimpleGraph U) (hT : T.IsTree) {r : ℕ} (hr : 1 ≤ r) (hdiam : T.diam = 2 * r) :
    ∃ c : U, T.eccent c = r ∧ ∀ v : U, v ≠ c → (r : ℕ∞) < T.eccent v := by
  have : Nonempty U := hT.connected.nonempty
  obtain ⟨x0, xd, hxd⟩ := T.exists_dist_eq_diam
  obtain ⟨p, hp, hplen⟩ := hT.connected.exists_path_of_dist x0 xd
  have hplen_r : p.length = 2 * r := hplen.trans (hxd.trans hdiam)
  let c : U := p.getVert r
  let p₁ : T.Walk x0 c := p.take r
  let p₂ : T.Walk c xd := p.drop r
  have hp1 : p₁.IsPath := hp.take r
  have hp2 : p₂.IsPath := hp.drop r
  have hp1_len : p₁.length = r := by rw [Walk.take_length]; omega
  have hp2_len : p₂.length = r := by rw [Walk.drop_length]; omega
  have hp_app : p₁.append p₂ = p := p.append_take_drop_eq r
  have hkey : ∀ y : U, (T.dist y xd = T.dist y c + r ∨ T.dist y x0 = T.dist y c + r) := by
    intro y
    obtain ⟨q, hq, hqlen⟩ := hT.connected.exists_path_of_dist y c
    obtain ⟨z, q₁, q₂, hz_mem, hq_eq, hq_first⟩ :=
      split_walk_first_mem T {u | u ∈ p.support} q (p.getVert_mem_support r)
    have hq_app : (q₁.append q₂).IsPath := hq_eq ▸ hq
    have hq1 : q₁.IsPath := hq_app.of_append_left
    have hq2 : q₂.IsPath := hq_app.of_append_right
    have hq_len : q.length = q₁.length + q₂.length := by rw [hq_eq, Walk.length_append]
    have hz12 : z ∈ p₁.support ∨ z ∈ p₂.support :=
      (Walk.mem_support_append_iff p₁ p₂).mp (hp_app.symm ▸ hz_mem)
    rcases hz12 with hz1 | hz2
    · obtain ⟨a, b, ha, hb, hp1_eq⟩ := hp1.mem_support_iff_exists_append.mp hz1
      let pR : T.Walk z xd := b.append p₂
      have hp_decomp : p = a.append pR := by rw [← hp_app, hp1_eq, Walk.append_assoc]
      have hpR : pR.IsPath := (hp_decomp ▸ hp).of_append_right
      have hb_eq : q₂ = b := isTree_path_eq T hT hq2 hb
      have hpR_len : pR.length = q₂.length + r := by rw [Walk.length_append, hp2_len, hb_eq]
      have hmeet : ∀ u ∈ q₁.support, u ∈ pR.support.tail → u = z := by
        intro u huq hus
        exact hq_first u huq (hp_decomp ▸ Walk.support_subset_support_append_right a pR (List.mem_of_mem_tail hus))
      have hqpR : (q₁.append pR).IsPath := isPath_append_of_first_meet hq1 hpR hmeet
      have hdist : (q₁.append pR).length = T.dist y xd :=
        isTree_dist_eq_length_of_isPath T hT (q₁.append pR) hqpR
      left
      rw [Walk.length_append, hpR_len] at hdist
      omega
    · obtain ⟨a, b, ha, hb, hp2_eq⟩ := hp2.mem_support_iff_exists_append.mp hz2
      let pL : T.Walk x0 z := p₁.append a
      have hp_decomp : p = pL.append b := by rw [← hp_app, hp2_eq, ← Walk.append_assoc]
      have hpL : pL.IsPath := (hp_decomp ▸ hp).of_append_left
      have ha_eq : q₂ = a.reverse := isTree_path_eq T hT hq2 ha.reverse
      have hpL_len : pL.reverse.length = r + q₂.length := by
        rw [Walk.length_reverse, Walk.length_append, hp1_len, ha_eq, Walk.length_reverse]
      have hmeet : ∀ u ∈ q₁.support, u ∈ pL.reverse.support.tail → u = z := by
        intro u huq hus
        have hus1 : u ∈ pL.reverse.support := List.mem_of_mem_tail hus
        rw [Walk.support_reverse, List.mem_reverse] at hus1
        exact hq_first u huq (hp_decomp ▸ Walk.support_subset_support_append_left pL b hus1)
      have hqpL : (q₁.append pL.reverse).IsPath := isPath_append_of_first_meet hq1 hpL.reverse hmeet
      have hdist : (q₁.append pL.reverse).length = T.dist y x0 :=
        isTree_dist_eq_length_of_isPath T hT (q₁.append pL.reverse) hqpL
      right
      rw [Walk.length_append, hpL_len] at hdist
      omega
  have hediam : T.ediam ≠ ⊤ := connected_iff_ediam_ne_top.mp hT.connected
  have hle_r : ∀ y : U, T.dist y c ≤ r := by
    intro y
    rcases hkey y with hy | hy
    · have := dist_le_diam hediam (u := y) (v := xd); omega
    · have := dist_le_diam hediam (u := y) (v := x0); omega
  have hecc_le : T.eccent c ≤ r := by
    rw [SimpleGraph.eccent_le_iff]
    intro y
    rw [← (hT.connected c y).coe_dist_eq_edist, SimpleGraph.dist_comm]
    exact Nat.cast_le.mpr (hle_r y)
  have hecc_ge : (r : ℕ∞) ≤ T.eccent c := by
    have hcx0 : T.dist c x0 = r := by
      have h := isTree_dist_eq_length_of_isPath T hT p₁ hp1
      rw [SimpleGraph.dist_comm, ← h, hp1_len]
    rw [← hcx0, (hT.connected c x0).coe_dist_eq_edist]
    exact SimpleGraph.edist_le_eccent
  refine ⟨c, le_antisymm hecc_le hecc_ge, fun v hvc => ?_⟩
  have hpos : 0 < T.dist v c := hT.connected.pos_dist_of_ne hvc
  rcases hkey v with hv | hv
  · have hlt : (r : ℕ∞) < (T.dist v xd : ℕ∞) := Nat.cast_lt.mpr (by omega)
    rw [(hT.connected v xd).coe_dist_eq_edist] at hlt
    exact lt_of_lt_of_le hlt SimpleGraph.edist_le_eccent
  · have hlt : (r : ℕ∞) < (T.dist v x0 : ℕ∞) := Nat.cast_lt.mpr (by omega)
    rw [(hT.connected v x0).coe_dist_eq_edist] at hlt
    exact lt_of_lt_of_le hlt SimpleGraph.edist_le_eccent

private lemma iso_edist_eq {A B : Type*} (GA : SimpleGraph A) (GB : SimpleGraph B)
    (φ : GA ≃g GB) (a₁ a₂ : A) : GB.edist (φ a₁) (φ a₂) = GA.edist a₁ a₂ := by
  apply le_antisymm
  · dsimp only [SimpleGraph.edist]
    rw [le_iInf_iff]
    intro w
    exact (SimpleGraph.edist_le (w.map φ.toHom)).trans (by simp)
  · dsimp only [SimpleGraph.edist]
    rw [le_iInf_iff]
    intro w
    exact (SimpleGraph.edist_le ((w.map φ.symm.toHom).copy (φ.symm_apply_apply a₁) (φ.symm_apply_apply a₂))).trans
      (by rw [Nat.cast_le, Walk.length_copy, Walk.length_map])

private lemma iso_eccent_eq {A B : Type*} (GA : SimpleGraph A) (GB : SimpleGraph B)
    (φ : GA ≃g GB) (a : A) : GB.eccent (φ a) = GA.eccent a := by
  simp only [SimpleGraph.eccent_def]
  apply le_antisymm
  · rw [iSup_le_iff]
    intro b
    rw [← φ.apply_symm_apply b, iso_edist_eq GA GB φ a (φ.symm b)]
    exact le_iSup (GA.edist a) (φ.symm b)
  · rw [iSup_le_iff]
    intro a'
    rw [← iso_edist_eq GA GB φ a a']
    exact le_iSup (GB.edist (φ a)) (φ a')

private lemma iso_diam_eq {A B : Type*} (GA : SimpleGraph A) (GB : SimpleGraph B)
    (φ : GA ≃g GB) : GA.diam = GB.diam := by
  simp only [SimpleGraph.diam, SimpleGraph.ediam]
  congr 1
  apply le_antisymm
  · rw [iSup_le_iff]
    intro a
    rw [← iso_eccent_eq GA GB φ a]
    exact le_iSup GB.eccent (φ a)
  · rw [iSup_le_iff]
    intro b
    rw [← φ.apply_symm_apply b, iso_eccent_eq GA GB φ (φ.symm b)]
    exact le_iSup GA.eccent (φ.symm b)

private lemma ne_center_of_deg_one {U : Type} [Fintype U]
    (T : SimpleGraph U) (hT : T.IsTree) {r : ℕ} (hr : 1 ≤ r) (c : U)
    (hecc : T.eccent c = r) (huniq_c : ∀ z : U, z ≠ c → (r : ℕ∞) < T.eccent z)
    {v : U} (hdeg1 : T.degree v = 1) : v ≠ c := by
  rintro rfl
  obtain ⟨u, huv, huniq⟩ := SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp hdeg1
  have huc : u ≠ v := huv.ne.symm
  have hle : T.eccent u ≤ r := by
    rw [SimpleGraph.eccent_le_iff]
    intro y
    rw [← (hT.connected u y).coe_dist_eq_edist]
    norm_cast
    by_cases hyv : y = v
    · subst hyv
      have hd : T.dist u y = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr huv.symm
      omega
    · obtain ⟨p, hp, hplen⟩ := hT.connected.exists_path_of_dist v y
      have hnp : ¬ p.Nil := Walk.not_nil_of_ne (Ne.symm hyv)
      have hsnd : p.snd = u := huniq p.snd (p.adj_snd hnp)
      let p' : T.Walk u y := p.tail.copy hsnd rfl
      have hp' : p'.IsPath := (Walk.isPath_copy _ _ _).mpr hp.tail
      have hdist_u : T.dist u y = p'.length :=
        (isTree_dist_eq_length_of_isPath T hT p' hp').symm
      have hvy_le : T.dist v y ≤ r := by
        have h1 : (T.dist v y : ℕ∞) ≤ r := by
          rw [(hT.connected v y).coe_dist_eq_edist, ← hecc]
          exact SimpleGraph.edist_le_eccent
        exact Nat.cast_le.mp h1
      rw [hdist_u, Walk.length_copy, Walk.length_tail, hplen]
      omega
  have hlt := huniq_c u huc
  exact absurd (lt_of_lt_of_le hlt hle) (lt_irrefl _)

private lemma center_induce_compl_of_good_leaf {U : Type} [Fintype U]
    (T : SimpleGraph U) (hT : T.IsTree) {r : ℕ} (hr : 1 ≤ r)
    (c : U) (hecc : T.eccent c = r) (huniq_c : ∀ z : U, z ≠ c → (r : ℕ∞) < T.eccent z)
    {v : U} (hdeg1 : T.degree v = 1) (hdiam' : (T.induce {v}ᶜ).diam = 2 * r) :
    ∃ hc : c ∈ ({v}ᶜ : Set U),
      (T.induce {v}ᶜ).eccent ⟨c, hc⟩ = r ∧
      ∀ z' : ({v}ᶜ : Set U), z' ≠ ⟨c, hc⟩ → (r : ℕ∞) < (T.induce {v}ᶜ).eccent z' := by
  have hc : c ∈ ({v}ᶜ : Set U) := Set.mem_compl_singleton_iff.mpr (ne_center_of_deg_one T hT hr c hecc huniq_c hdeg1).symm
  refine ⟨hc, ?_⟩
  let T' := T.induce ({v}ᶜ : Set U)
  have hT' : T'.IsTree := induce_compl_singleton_isTree_of_deg_one T hT hdeg1
  let c' : ({v}ᶜ : Set U) := ⟨c, hc⟩
  have hle_r : ∀ y' : ({v}ᶜ : Set U), T'.dist c' y' ≤ r := by
    intro y'
    rw [induce_compl_singleton_dist_eq T hT hT']
    have h1 : (T.dist c y'.1 : ℕ∞) ≤ r := by
      rw [(hT.connected c y'.1).coe_dist_eq_edist, ← hecc]
      exact SimpleGraph.edist_le_eccent
    exact Nat.cast_le.mp h1
  have hecc_le : T'.eccent c' ≤ r := by
    rw [SimpleGraph.eccent_le_iff]
    intro y'
    rw [← (hT'.connected c' y').coe_dist_eq_edist]
    exact Nat.cast_le.mpr (hle_r y')
  have : Nonempty ({v}ᶜ : Set U) := hT'.connected.nonempty
  obtain ⟨a, b, hab⟩ := T'.exists_dist_eq_diam
  rw [hdiam'] at hab
  have hda : T'.dist c' a = r := by
    have htri := hT'.connected.dist_triangle (u := a) (v := c') (w := b)
    rw [SimpleGraph.dist_comm (u := a) (v := c')] at htri
    have ha := hle_r a
    have hb := hle_r b
    omega
  have hecc_ge : (r : ℕ∞) ≤ T'.eccent c' := by
    rw [← hda, (hT'.connected c' a).coe_dist_eq_edist]
    exact SimpleGraph.edist_le_eccent
  have hecc_eq : T'.eccent c' = r := le_antisymm hecc_le hecc_ge
  obtain ⟨c₀, _, huniq₀⟩ := exists_unique_center_of_diam_eq_two_mul T' hT' hr hdiam'
  have hc₀ : c' = c₀ := by
    by_contra hne
    have hlt := huniq₀ c' hne
    rw [hecc_eq] at hlt
    exact absurd hlt (lt_irrefl _)
  subst hc₀
  exact ⟨hecc_eq, huniq₀⟩

private lemma iso_map_center_of_good_leaf {V W : Type} [Fintype V] [Fintype W]
    (G : SimpleGraph V) (H : SimpleGraph W) (hTG : G.IsTree) (hTH : H.IsTree)
    {r : ℕ} (hr : 1 ≤ r) (cG : V) (cH : W)
    (heccG : G.eccent cG = r) (huG : ∀ v : V, v ≠ cG → (r : ℕ∞) < G.eccent v)
    (heccH : H.eccent cH = r) (huH : ∀ w : W, w ≠ cH → (r : ℕ∞) < H.eccent w)
    {v : V} {w : W} (hv1 : G.degree v = 1) (hw1 : H.degree w = 1)
    (hdiamG' : (G.induce {v}ᶜ).diam = 2 * r)
    (φ : G.induce {v}ᶜ ≃g H.induce {w}ᶜ) :
    ∃ (hcG : cG ∈ ({v}ᶜ : Set V)) (hcH : cH ∈ ({w}ᶜ : Set W)), φ ⟨cG, hcG⟩ = ⟨cH, hcH⟩ := by
  have hdiamH' : (H.induce {w}ᶜ).diam = 2 * r :=
    (iso_diam_eq _ _ φ).symm.trans hdiamG'
  obtain ⟨hcG, heccG', _⟩ := center_induce_compl_of_good_leaf G hTG hr cG heccG huG hv1 hdiamG'
  obtain ⟨hcH, _, huH'⟩ := center_induce_compl_of_good_leaf H hTH hr cH heccH huH hw1 hdiamH'
  refine ⟨hcG, hcH, ?_⟩
  by_contra hne
  have hlt := huH' (φ ⟨cG, hcG⟩) hne
  rw [iso_eccent_eq _ _ φ ⟨cG, hcG⟩, heccG'] at hlt
  exact absurd hlt (lt_irrefl _)



private theorem lift_branch {V W : Type} [Fintype V] [Fintype W]
    (T : SimpleGraph V) (S : SimpleGraph W) (treeT : T.IsTree) (treeS : S.IsTree)
    (a : V) (d : W) (v : ({a}ᶜ : Set V)) (w : W)
    (leafT : T.degree v.val = 1) (leafS : S.degree w = 1)
    (ca : a ∈ ({v.val}ᶜ : Set V)) (cd : d ∈ ({w}ᶜ : Set W))
    (φ : T.induce {v.val}ᶜ ≃g S.induce {w}ᶜ) (center : φ ⟨a,ca⟩ = ⟨d,cd⟩)
    (C : (T.induce {a}ᶜ).ConnectedComponent) (outside : v ∉ C.supp) :
    ∃ E : (S.induce {d}ᶜ).ConnectedComponent, C.supp.ncard ≤ E.supp.ncard ∧
      ∀ x : C.supp, ∃ y : E.supp, T.dist a x.val.val = S.dist d y.val.val := by
  classical
  let f (x : C.supp) : ({v.val}ᶜ : Set V) := ⟨x.val.val, by
    change x.val.val ≠ v.val
    intro he
    exact outside ((Subtype.ext he : x.val=v) ▸ x.property)⟩
  let g (x : C.supp) : ({d}ᶜ : Set W) := ⟨(φ (f x)).val, by
    change (φ (f x)).val ≠ d
    intro he
    have eq : φ (f x) = φ ⟨a,ca⟩ := by rw [center]; exact Subtype.ext he
    exact x.val.property (congrArg Subtype.val (φ.injective eq))⟩
  let hom : C.toSimpleGraph →g S.induce {d}ᶜ := {
    toFun := g
    map_rel' := fun {x y} h => φ.map_adj_iff.mpr (show (T.induce {v.val}ᶜ).Adj (f x) (f y) from h) }
  have inj : Function.Injective g := by
    intro x y eq
    have ge : (g x).val = (g y).val := congrArg (fun z : ({d}ᶜ : Set W) => z.val) eq
    have fg : φ (f x) = φ (f y) := Subtype.ext ge
    have fe : (f x).val = (f y).val := congrArg (fun z : ({v.val}ᶜ : Set V) => z.val) (φ.injective fg)
    exact Subtype.ext (Subtype.ext fe)
  obtain ⟨x0⟩ := C.connected_toSimpleGraph.nonempty
  let E := (S.induce {d}ᶜ).connectedComponentMk (g x0)
  have mem (x : C.supp) : g x ∈ E.supp := by
    apply ConnectedComponent.eq.mpr
    exact (C.connected_toSimpleGraph.preconnected x x0).map hom
  refine ⟨E, ?_, ?_⟩
  · let F (x : C.supp) : E.supp := ⟨g x, mem x⟩
    rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
    exact Nat.card_le_card_of_injective F (fun x y eq => inj (congrArg Subtype.val eq))
  · intro x
    refine ⟨⟨g x,mem x⟩, ?_⟩
    have dT := induce_compl_singleton_dist_eq T treeT (induce_compl_singleton_isTree_of_deg_one T treeT leafT) ⟨a,ca⟩ (f x)
    have dS := induce_compl_singleton_dist_eq S treeS (induce_compl_singleton_isTree_of_deg_one S treeS leafS) ⟨d,cd⟩ (φ (f x))
    have same := congrArg ENat.toNat (iso_edist_eq _ _ φ ⟨a,ca⟩ (f x))
    rw [center] at same
    exact dT.symm.trans (same.symm.trans dS)


private theorem pure_of_covers {V W : Type} [Fintype V] [Fintype W]
    (T : SimpleGraph V) (S : SimpleGraph W) (σ : V ≃ W) (treeT : T.IsTree) (treeS : S.IsTree)
    (cards : ∀ x, Nonempty (T.induce {x}ᶜ ≃g S.induce {σ x}ᶜ))
    (degrees : ∀ x, (T.neighborSet x).ncard = (S.neighborSet (σ x)).ncard)
    (r : ℕ) (a : V) (d : W) (hr : 2 ≤ r)
    (eccT : T.eccent a = r) (eccS : S.eccent d = r)
    (uniqueT : ∀ x, x ≠ a → (r : ℕ∞) < T.eccent x)
    (uniqueS : ∀ x, x ≠ d → (r : ℕ∞) < S.eccent x)
    (covers : ∀ C : (T.induce {a}ᶜ).ConnectedComponent, ∃ v : ({a}ᶜ : Set V),
       v ∉ C.supp ∧ (T.neighborSet v.val).ncard=1 ∧ (T.induce {v.val}ᶜ).diam=2*r)
    (pure : ∀ E : (S.induce {d}ᶜ).ConnectedComponent, (∃ z : E.supp, S.dist d z.val.val=r) → E.supp.ncard ≤ r) :
       ∀ C : (T.induce {a}ᶜ).ConnectedComponent, (∃ x : C.supp, T.dist a x.val.val=r) → C.supp.ncard ≤ r := by
  classical
  rintro C ⟨x,hx⟩
  obtain ⟨v,hout,hv,hdiam⟩ := covers C
  obtain ⟨φ⟩ := cards v.val
  have ht : T.degree v.val = 1 := (ncard_neighborSet_eq_degree T _).symm.trans hv
  have hs : S.degree (σ v.val) = 1 := (ncard_neighborSet_eq_degree S _).symm.trans ((degrees _).symm.trans hv)
  obtain ⟨ca,cd,eq⟩ := iso_map_center_of_good_leaf T S treeT treeS (by omega : 1 ≤ r) a d
    eccT uniqueT eccS uniqueS ht hs hdiam φ
  obtain ⟨E,hle,map⟩ := lift_branch T S treeT treeS a d v (σ v.val) ht hs ca cd φ eq C hout
  obtain ⟨y,hy⟩ := map x
  exact hle.trans (pure E ⟨y,hy.symm.trans hx⟩)

end

theorem result :
    OMA.R_ReconstructionConjecture_reconstruction_conjecture_variants_tree_R1_H3_R1_H4_R1.H2 := by
  classical
  intro V W _ _ G H σ tG tH cards degree _ r c d hr dg dh eg eh ug uh _ _ _
  change (¬ OMA.TreeSingle.Covers r G c ∨ ¬ OMA.TreeSingle.Covers r H d) →
    OMA.TreeSingle.Long r G c ∨ OMA.TreeSingle.Long r H d ∨
    (OMA.TreeSingle.Pure r G c ∧ OMA.TreeSingle.Pure r H d)
  intro missing
  by_cases cg : OMA.TreeSingle.Covers r G c
  · have nh := missing.resolve_left (fun h => h cg)
    rcases OMA.TreeSingle.classify_single H tH hr dh d eh nh with long | p
    · exact .inr (.inl long)
    · exact .inr (.inr ⟨pure_of_covers G H σ tG tH cards degree r c d hr eg eh ug uh cg p, p⟩)
  · rcases OMA.TreeSingle.classify_single G tG hr dg c eg cg with long | p
    · exact .inl long
    · by_cases ch : OMA.TreeSingle.Covers r H d
      · have back (w : W) : Nonempty (H.induce {w}ᶜ ≃g G.induce {σ.symm w}ᶜ) := by
          obtain ⟨e⟩ := cards (σ.symm w)
          rw [Equiv.apply_symm_apply] at e
          exact ⟨e.symm⟩
        have degrees (w : W) : (H.neighborSet w).ncard = (G.neighborSet (σ.symm w)).ncard := by
          simpa only [Equiv.apply_symm_apply] using (degree (σ.symm w)).symm
        exact .inr (.inr ⟨p,pure_of_covers H G σ.symm tH tG back degrees r d c hr eh eg uh ug ch p⟩)
      · rcases OMA.TreeSingle.classify_single H tH hr dh d eh ch with long | q
        · exact .inr (.inl long)
        · exact .inr (.inr ⟨p,q⟩)

end LargeBranchCase2

namespace LargeBranchCase3

/- A full-radius arm at a center of degree two extends past the center. Leaf cards and counts of the neighbors of each degree then reconstruct this long arm.
Credit: @Deldor14. Tree deletion and distance lemmas adapted from @green-notes. -/
end LargeBranchCase3
namespace OMA
namespace TreeArms
open SimpleGraph
open Classical
variable {V : Type*} {G : SimpleGraph V} {c : V} {n : Nat}

private lemma shorten_diameter_LargeBranchCase3 {V : Type} [Fintype V] {G : SimpleGraph V} {c : V}
    (tree : G.IsTree) (a : Arm G c (n+2)) (r : Nat) (big : r+1 ≤ n+2) (diam : G.diam ≤ 2*r+1) :
    (G.induce {a.vertex (Fin.last (n+1))}ᶜ).diam ≤ 2*r := by
  classical
  let v := a.vertex (Fin.last (n+1))
  let K := G.induce {v}ᶜ
  let d : ({v}ᶜ : Set V) := ⟨c,(a.away _).symm⟩
  let b := a.shorten
  have kt := induce_compl_singleton_isTree_of_deg_one G tree a.tip_deg
  have dist := induce_compl_singleton_dist_eq G tree kt
  have long : G.dist v c = n+2 := G.dist_comm.trans (a.tip_dist tree)
  have len := dist_bound tree.connected v c
  have out (x : ({v}ᶜ : Set V)) (hx : x∉Set.range b.vertex) : K.dist d x + (n+2) ≤ 2*r+1 := by
    have notA : x.val ∉ Set.range a.vertex := by
      rintro ⟨j,e⟩
      refine Fin.lastCases (motive := fun j => a.vertex j=x.val → False) ?_ ?_ j e
      · intro e;exact x.property e.symm
      · intro i e;exact hx ⟨i,Subtype.ext e⟩
    have bound := dist_bound tree.connected v x.val
    have split := a.dist_outside tree.connected (Set.mem_range_self _) notA (x:=v)
    change (G.induce {v}ᶜ).dist d x + (n+2) ≤ 2*r+1
    rw [dist]
    change G.dist c x.val + (n+2) ≤ 2*r+1
    omega
  have : Nonempty ({v}ᶜ : Set V) := ⟨d⟩
  obtain ⟨x,y,ed⟩ := K.exists_dist_eq_diam
  have tri := (kt.connected x d).dist_triangle_left y
  rw [K.dist_comm (u:=x) (v:=d)] at tri
  change K.dist x y ≤ K.dist d x + K.dist d y at tri
  change K.diam ≤ 2*r
  by_cases hx : x∈Set.range b.vertex <;> by_cases hy : y∈Set.range b.vertex
  · obtain ⟨i,rfl⟩ := hx
    obtain ⟨j,rfl⟩ := hy
    have inside := b.internalNear i j
    change K.dist _ _ < n+1 at inside
    omega
  · obtain ⟨i,rfl⟩ := hx
    have l := b.radius_bound kt.connected i
    change K.dist d _ ≤ n+1 at l
    have := out y hy
    omega
  · obtain ⟨j,rfl⟩ := hy
    have l := b.radius_bound kt.connected j
    change K.dist d _ ≤ n+1 at l
    have := out x hx
    omega
  · have := out x hx;have := out y hy;omega

private lemma glue_unrooted_LargeBranchCase3 {V W : Type} [Fintype V] [Fintype W] {G : SimpleGraph V}
    {H : SimpleGraph W} {c : V} {d : W} {r n : Nat} (a : Arm G c (n+2)) (b : Arm H d (n+2))
    (tg : G.IsTree) (dg : G.diam ≤ 2*r+1) (big : r+1 ≤ n+2) (cg : 3 ≤ G.degree c) (dh : 3 ≤ H.degree d)
    (f : G.induce {a.vertex (Fin.last (n+1))}ᶜ ≃g H.induce {b.vertex (Fin.last (n+1))}ᶜ) :
    Nonempty (G ≃g H) := by
  let A := a.shorten
  let B := b.shorten.map f.symm
  have tree := induce_compl_singleton_isTree_of_deg_one G tg a.tip_deg
  have dims := shorten_diameter_LargeBranchCase3 tg a r big dg
  have highA := root_high_shorten a cg
  have highB : 3 ≤ (G.induce {a.vertex (Fin.last (n+1))}ᶜ).degree (f.symm ⟨d,(b.away _).symm⟩) :=
    (root_high_shorten b dh).trans (f.symm.degree_eq _).ge
  obtain ⟨g,im⟩ := can_match tree A B highA highB (by omega : r ≤ n+1) dims
  let e := g.trans f
  apply extend_card e
  intro x
  rw [a.tip_only,b.tip_only]
  let s := A.vertex (Fin.last n)
  let t := b.shorten.vertex (Fin.last n)
  have ee : e s=t := by
    change f (g s)=t
    change g s = f.symm t at im
    rw [im,f.apply_symm_apply]
  change x.val=s.val ↔ (e x).val=t.val
  rw [←Subtype.ext_iff,←Subtype.ext_iff,←ee]
  exact e.injective.eq_iff.symm

private lemma match_after_cut_LargeBranchCase3 {V W : Type} [Fintype V] [Fintype W] {G : SimpleGraph V}
    {H : SimpleGraph W} {c : V} {d w : W} {r n m : Nat} (a : Arm G c (n+2)) (b : Arm H d (m+2))
    (tg : G.IsTree) (dg : G.diam ≤ 2*r+1) (big : r+1 ≤ n+2) (more : n ≤ m)
    (cg : 3 ≤ G.degree c) (dh : 3 ≤ H.degree d) (leaf : H.degree w=1)
    (f : G.induce {a.vertex (Fin.last (n+1))}ᶜ ≃g H.induce {w}ᶜ) :
    Nonempty (G ≃g H) := by
  let K := G.induce {a.vertex (Fin.last (n+1))}ᶜ
  let h := (⟨c,(a.away _).symm⟩ : ({a.vertex (Fin.last (n+1))}ᶜ : Set V))
  have tree : K.IsTree := induce_compl_singleton_isTree_of_deg_one G tg a.tip_deg
  have D : K.diam ≤ 2*r := shorten_diameter_LargeBranchCase3 tg a r big dg
  have hhi : 3 ≤ K.degree h := root_high_shorten a cg
  have brK : ∃ x,3 ≤ (K.neighborSet x).ncard := ⟨h,by rwa [ncard_neighborSet_eq_degree]⟩
  have bound {L} {z} (B : Arm K z (L+1)) (high : 3 ≤ K.degree z) : L ≤ n :=
    no_longer tree a.shorten B hhi high (by omega : r ≤ n+1) D
  have same : w=b.vertex (Fin.last (m+1)) := by
    by_contra diff
    have out : w∉Set.range b.vertex := by
      rintro ⟨i,e⟩
      have hl : (H.neighborSet (b.vertex i)).ncard=1 := by rw [ncard_neighborSet_eq_degree,e,leaf]
      exact diff (e.symm.trans (congrArg b.vertex (b.low_tip i hl)))
    have nc : w ≠ d := by intro e;rw [e] at leaf;omega
    let kept := (b.keep nc out).map f.symm
    obtain ⟨L,le,z,high,B⟩ := large_anchored tree.connected brK (by omega : 1 ≤ m+2) ⟨_,⟨kept⟩⟩
    obtain ⟨j,rfl⟩ : ∃ j,L=j+1 := ⟨L-1,by omega⟩
    obtain ⟨B⟩ := B
    have := bound B high
    omega
  subst w
  let B := b.shorten.map f.symm
  have high : 3 ≤ K.degree (f.symm ⟨d,(b.away _).symm⟩) :=
    (root_high_shorten b dh).trans (f.symm.degree_eq _).ge
  have eq : m=n := Nat.le_antisymm (bound B high) more
  subst m
  exact glue_unrooted_LargeBranchCase3 a b tg dg big cg dh f

private lemma one_sided_LargeBranchCase3 {V W : Type} [Fintype V] [Fintype W] {G : SimpleGraph V}
    {H : SimpleGraph W} (tg : G.IsTree) (th : H.IsTree) (σ : V ≃ W)
    (cards : ∀ v, Nonempty (G.induce {v}ᶜ ≃g H.induce {σ v}ᶜ))
    (deg : ∀ v, G.degree v=H.degree (σ v)) (bg : ∃ x,3 ≤ (G.neighborSet x).ncard)
    (bh : ∃ x,3 ≤ (H.neighborSet x).ncard) {r} (ge : 1 ≤ r) (dg : G.diam ≤ 2*r+1)
    (long : ∃ c,Nonempty (Arm G c (r+1))) : Nonempty (G ≃g H) := by
  obtain ⟨L,large,c,cg,As⟩ := large_anchored tg.connected bg (by omega : 1 ≤ r+1) long
  obtain ⟨n,rfl⟩ : ∃ n, L=n+2 := ⟨L-2,by omega⟩
  obtain ⟨A⟩ := As
  have existsH := transfer_any th σ cards deg bh A
  obtain ⟨M,more,d,dh,Bs⟩ := large_anchored th.connected bh (by omega : 1 ≤ n+2) existsH
  obtain ⟨m,rfl⟩ : ∃ m,M=m+2 := ⟨M-2,by omega⟩
  obtain ⟨B⟩ := Bs
  let v := A.vertex (Fin.last (n+1))
  have hl : H.degree (σ v)=1 := (deg v).symm.trans A.tip_deg
  exact match_after_cut_LargeBranchCase3 A B tg dg large (by omega) cg dh hl (cards v).some

private lemma arm_local_component {V : Type*} [Fintype V] (G : SimpleGraph V) (c : V)
    {n : Nat} (hn : 0<n) (f : Fin (n+1) ↪ V) (start : f 0 = c)
    (induced : ∀ i j, G.Adj (f i) (f j) ↔ i.val+1=j.val ∨ j.val+1=i.val)
    (target : Fin n) (small : ∀ C : (G.induce {c}ᶜ).ConnectedComponent,
      (∃ y : C.supp, y.val.val=f target.succ) → C.supp.ncard ≤ n) :
    ∃ a : Arm G c n, ∀ i, a.vertex i = f i.succ := by
  classical
  have away (i : Fin n) : f i.succ ≠ c := by
    rw [← start]; exact fun h => Fin.succ_ne_zero _ (f.injective h)
  let g (i : Fin n) : ({c}ᶜ : Set V) := ⟨f i.succ,away i⟩
  let u : Fin n := ⟨0,hn⟩
  let graph := G.induce {c}ᶜ
  let hom : pathGraph n →g graph :=
    { toFun := g
      map_rel' := fun {i j} h => (induced i.succ j.succ).mpr (by
        have := pathGraph_adj.mp h
        simp only [Fin.val_succ]
        omega) }
  let C := graph.connectedComponentMk (g u)
  have mem (i : Fin n) : g i ∈ C.supp :=
    ConnectedComponent.sound (((pathGraph_preconnected n) i u).map hom)
  let emb (i : Fin n) : C.supp := ⟨g i,mem i⟩
  have inj : Function.Injective emb := by
    intro i j e
    exact Fin.succ_injective n (f.injective (congrArg (fun z : C.supp => z.1.1) e))
  have box : Fintype.card C.supp ≤ n := by rw [Set.fintypeCard_eq_ncard]; exact small C ⟨⟨g target,mem target⟩,rfl⟩
  have counter := Fintype.card_le_of_injective emb inj
  have onto : Function.Surjective emb :=
    ((Fintype.bijective_iff_injective_and_card emb).mpr ⟨inj,by simpa using le_antisymm counter (by simpa using box)⟩).2
  let tail : Fin n ↪ V := ⟨fun i => f i.succ,fun _ _ h => Fin.succ_injective n (f.injective h)⟩
  refine ⟨⟨tail,away,?_,?_⟩,fun _ => rfl⟩
  · intro i j
    change G.Adj (f i.succ) (f j.succ) ↔ _
    rw [induced]
    simp only [Fin.val_succ]
    omega
  · intro i y out
    by_cases eq : y=c
    · subst y
      change G.Adj (f i.succ) c ↔ _
      rw [← start,induced]
      simp [Fin.val_succ]
    · suffices ¬ G.Adj (tail i) y by simp [this,eq]
      intro ad
      let z : ({c}ᶜ : Set V) := ⟨y,eq⟩
      have adj : graph.Adj (g i) z := ad
      have zz := (C.mem_supp_congr_adj adj).mp (mem i)
      obtain ⟨j,hj⟩ := onto ⟨z,zz⟩
      exact out ⟨j,congrArg (fun z : C.supp => z.1.1) hj⟩
private lemma max_local_arm {V : Type*} [Fintype V] (G : SimpleGraph V) (conn : G.Connected)
    (c x : V) (k : ℕ) (hx : G.dist c x = k+1)
    (small : ∀ C : (G.induce {c}ᶜ).ConnectedComponent,
      (∃ y : C.supp, y.val.val=x) → C.supp.ncard ≤ k+1) :
    ∃ a : Arm G c (k+1), a.vertex (Fin.last k) = x := by
  classical
  obtain ⟨p,path,hlen⟩ := conn.exists_path_of_dist c x
  have len : p.length = k+1 := hlen.trans hx
  let f : Fin (k+1+1) ↪ V :=
    ⟨fun i => p.getVert i.val,fun i j h => Fin.ext (path.getVert_injOn (show i.val ≤ p.length by omega) (show j.val ≤ p.length by omega) h)⟩
  have ad (i j : Fin (k+1+1)) :
      G.Adj (f i) (f j) ↔ i.val+1=j.val ∨ j.val+1=i.val := by
    let cv (i : Fin (k+1+1)) : Fin p.support.length :=
      ⟨i.val,by rw [p.length_support,len];exact i.isLt⟩
    have eq (i : Fin (k+1+1)) : p.support.get (cv i) = f i :=
      p.support_getElem_eq_getVert (cv i).isLt
    simpa only [eq,cv] using (shortest_induced p hlen).2 (cv i) (cv j)
  obtain ⟨a,ha⟩ := arm_local_component G c (by omega) f (by change p.getVert 0 = c; exact p.getVert_zero) ad (Fin.last k) (fun C ⟨y,hy⟩ => small C ⟨y,by
    change y.val.val = p.getVert (k+1) at hy
    rwa [←len,p.getVert_length] at hy⟩)
  refine ⟨a,?_⟩
  rw [ha]
  change p.getVert (k+1) = x
  rw [←len,p.getVert_length]


private lemma component_arm {V : Type} [Fintype V] (G : SimpleGraph V) (tree : G.IsTree) (c : V)
    (k : Nat) (br : ∃ x,3 ≤ (G.neighborSet x).ncard)
    (low : (G.neighborSet c).ncard=2)
    (C : (G.induce {c}ᶜ).ConnectedComponent)
    (far : ∃ x : C.supp,G.dist c x.val.val=k+1) (small : C.supp.ncard ≤ k+1) :
    ∃ z,Nonempty (Arm G z (k+2)) := by
  obtain ⟨x,rad⟩ := far
  obtain ⟨a,_⟩ := max_local_arm G tree.connected c x.val.val k rad (fun D ⟨y,e⟩ => by
    have xy : x.val=y.val := Subtype.ext e.symm
    have hC := x.property
    have hD := y.property
    rw [ConnectedComponent.mem_supp_iff] at hC hD
    rw [←xy] at hD
    rwa [←hD,hC])
  obtain ⟨z,_,b,_,_⟩ := a.extend tree.connected br low.le
  exact ⟨z,⟨b⟩⟩


end TreeArms
end OMA
namespace LargeBranchCase3

section Solution
open SimpleGraph OMA.TreeArms Classical

theorem result : OMA.R_ReconstructionConjecture_reconstruction_conjecture_variants_tree_R1_H3_R1_H4_R1.H3 := by
  intro V W _ _ G H σ tg th cards degrees bg r c d hr dG dH _ _
  dsimp only
  intro long
  have deg (v) : G.degree v = H.degree (σ v) := by
    simpa only [ncard_neighborSet_eq_degree] using degrees v
  have bh : ∃ w,3 ≤ (H.neighborSet w).ncard := by
    obtain ⟨v,hi⟩ := bg
    exact ⟨σ v,by rwa [←degrees]⟩
  obtain ⟨k,rfl⟩ : ∃ k,r=k+1 := ⟨r-1,by omega⟩
  rcases long with ⟨low,C,far,small⟩|⟨low,C,far,small⟩
  · exact one_sided_LargeBranchCase3 tg th σ cards deg bg bh (by omega : 1 ≤ k+1) (by omega)
      (component_arm G tg c k bg low C far small)
  · have rcards (w) : Nonempty (H.induce {w}ᶜ ≃g G.induce {σ.symm w}ᶜ) := by
      obtain ⟨v,rfl⟩ := σ.surjective w
      rw [σ.symm_apply_apply]
      exact ⟨(cards v).some.symm⟩
    have rdeg (w) : H.degree w = G.degree (σ.symm w) := by
      obtain ⟨v,rfl⟩ := σ.surjective w
      rw [σ.symm_apply_apply]
      exact (deg v).symm
    obtain ⟨f⟩ := one_sided_LargeBranchCase3 th tg σ.symm rcards rdeg bh bg (by omega : 1 ≤ k+1) (by omega)
      (component_arm H th d k bh low C far small)
    exact ⟨f.symm⟩

end Solution

end LargeBranchCase3

namespace LargeBranchCase4

/- Only branches attaining the radius need be paths. Deleting a terminal leaf preserves another full arm, which identifies the center in its card.
Credit: @Deldor14. Tree deletion and distance lemmas adapted from @green-notes. -/
end LargeBranchCase4
namespace OMA
namespace TreeArms
open SimpleGraph
open Classical
variable {V : Type*} {G : SimpleGraph V} {c : V} {n : Nat}

private lemma pure_arm {V : Type} [Fintype V] (G : SimpleGraph V) (conn : G.Connected)
    (c x : V) (k : Nat) (far : G.dist c x=k+1)
    (pure : ∀ C : (G.induce {c}ᶜ).ConnectedComponent,
      (∃ y : C.supp,G.dist c y.val.val=k+1) → C.supp.ncard ≤ k+1) :
    ∃ a : Arm G c (k+1), a.vertex (Fin.last k) = x :=
  max_local_arm G conn c x k far (fun C ⟨y,e⟩ => pure C ⟨y,by rwa [e]⟩)

private lemma hub_and_tips_LargeBranchCase4 {V : Type} [Fintype V] (G : SimpleGraph V) (tree : G.IsTree)
    (c : V) (k : Nat) (hd : G.diam = 2*(k+2)) (he : G.eccent c = k+2)
    (small : ∀ C : (G.induce {c}ᶜ).ConnectedComponent,
       (∃ y:C.supp,G.dist c y.val.val=k+2) → C.supp.ncard ≤ k+2)
    (br : ∃ x, 3 ≤ (G.neighborSet x).ncard) :
    3 ≤ G.degree c ∧ (∀ x, G.dist c x ≤ k+2) ∧
      ∀ v, ∃ a : Arm G c (k+2), a.vertex (Fin.last (k+1)) ≠ v ∧
        G.dist c (a.vertex (Fin.last (k+1))) = k+2 := by
  classical
  have : Nonempty V := tree.connected.nonempty
  have upper (x : V) : G.dist c x ≤ k+2 := by
    apply (Nat.cast_le (α := ℕ∞)).mp
    rw [(tree.connected c x).coe_dist_eq_edist]
    have h := @edist_le_eccent _ G c x
    simpa [he] using h
  obtain ⟨u,w,e⟩ := G.exists_dist_eq_diam
  have far := e.trans hd
  have tr := (tree.connected u c).dist_triangle_left w
  rw [(G.dist_comm (u:=u) (v:=c))] at tr
  have uc : G.dist c u = k+2 := by have := upper u; have := upper w; omega
  have wc : G.dist c w = k+2 := by have := upper w; omega
  obtain ⟨a,au⟩ := pure_arm G tree.connected c u (k+1) uc small
  obtain ⟨b,bw⟩ := pure_arm G tree.connected c w (k+1) wc small
  have far' : 2*(k+2) ≤ G.dist (a.vertex (Fin.last (k+1))) (b.vertex (Fin.last (k+1))) := by
    rw [au,bw,far]
  have dg := degree_center tree.connected a b (arms_disjoint_of_far a b tree.connected far') br
  rw [ncard_neighborSet_eq_degree] at dg
  refine ⟨dg,upper,?_⟩
  intro v
  by_cases eq : u=v
  · refine ⟨b,?_,by rwa [bw]⟩
    rw [bw,←eq]
    intro h
    rw [h,G.dist_self] at far
    omega
  · exact ⟨a,by rwa [au],by rwa [au]⟩


end TreeArms
end OMA
namespace LargeBranchCase4

section Solution
open SimpleGraph OMA.TreeArms Classical

theorem result : OMA.R_ReconstructionConjecture_reconstruction_conjecture_variants_tree_R1_H3_R1_H4_R1.H4 := by
  intro V W _ _ G H σ tg th cards deg bg r c d hr dg dh eg eh _ _ _ nlG nlH
  dsimp only
  intro smallG smallH
  obtain ⟨k,rfl⟩ : ∃ k, r=k+2 := ⟨r-2,by omega⟩
  have bh : ∃ w, 3 ≤ (H.neighborSet w).ncard := by
    obtain ⟨v,bv⟩ := bg
    exact ⟨σ v,by rwa [←deg]⟩
  obtain ⟨dc,upG,tipG⟩ := hub_and_tips_LargeBranchCase4 G tg c k dg eg smallG bg
  obtain ⟨dd,upH,tipH⟩ := hub_and_tips_LargeBranchCase4 H th d k dh eh smallH bh
  have deg' (v) : G.degree v = H.degree (σ v) := by
    simpa only [ncard_neighborSet_eq_degree] using deg v
  let f (v) := (cards v).some
  have neqG (v) (leaf : G.degree v=1) : c ≠ v := by rintro rfl;omega
  have neqH (v) (leaf : G.degree v=1) : d ≠ σ v := by
    have := deg' v
    intro eq
    rw [eq] at dd
    omega
  have rooted (v) (leaf : G.degree v=1) :
      f v ⟨c,neqG v leaf⟩ = ⟨d,neqH v leaf⟩ := by
    apply iso_hubs _ _ (f v)
    · exact hub_card G tg c v k dc leaf nlG upG (tipG v)
    · exact hub_card H th d (σ v) k dd ((deg' v).symm.trans leaf) nlH upH (tipH (σ v))
  have bal (v) (leaf : G.degree v=1) :
      (level G c (k+2)).card + (if H.dist d (σ v)=k+2 then 1 else 0)
      = (level H d (k+2)).card + (if G.dist c v=k+2 then 1 else 0) := by
    have l := level_card_delete G tg leaf (neqG v leaf) (k+2)
    have r := level_card_delete H th ((deg' v).symm.trans leaf) (neqH v leaf) (k+2)
    have s := size_level_iso (f v) (⟨c,neqG v leaf⟩ : ({v}ᶜ : Set V)) (k+2)
    rw [rooted v leaf] at s
    omega
  obtain ⟨a,_,far⟩ := tipG c
  let v := a.vertex (Fin.last (k+1))
  change G.dist c v=k+2 at far
  obtain ⟨b,_,far'⟩ := tipH d
  let u := σ.symm (b.vertex (Fin.last (k+1)))
  have eu : σ u = b.vertex (Fin.last (k+1)) := σ.apply_symm_apply _
  have ul : G.degree u=1 := by rw [deg',eu,b.tip_deg]
  have balG := bal v a.tip_deg
  have balH := bal u ul
  rw [if_pos far] at balG
  rw [eu,if_pos far'] at balH
  have radial : H.dist d (σ v) = k+2 := by
    by_contra bad
    rw [if_neg bad] at balG
    split at balH <;> omega
  obtain ⟨arm,endpt⟩ := pure_arm H th.connected d (σ v) (k+1) radial smallH
  exact match_radial a arm rfl endpt (f v) (rooted v a.tip_deg)

end Solution

end LargeBranchCase4

private theorem remainingEven : OMA.R_ReconstructionConjecture_reconstruction_conjecture_variants_tree_R1_H3_R1.H4 := by
  exact OMA.R_ReconstructionConjecture_reconstruction_conjecture_variants_tree_R1_H3_R1_H4_R1.main
    LargeBranchCase1.result LargeBranchCase2.result LargeBranchCase3.result LargeBranchCase4.result

theorem OMA.solution : type_of% @ReconstructionConjecture.reconstruction_conjecture.variants.tree := by
  exact OMA.R_ReconstructionConjecture_reconstruction_conjecture_variants_tree_R1.main KellyStep1.result KellyStep2.result
    (OMA.R_ReconstructionConjecture_reconstruction_conjecture_variants_tree_R1_H3_R1.main KellyStep3.result KellyStep4.result KellyStep5.result remainingEven)
    (OMA.R_ReconstructionConjecture_reconstruction_conjecture_variants_tree_R1_H4_R1.main KellyStep6.result KellyStep7.result KellyStep8.result KellyStep9.result)
