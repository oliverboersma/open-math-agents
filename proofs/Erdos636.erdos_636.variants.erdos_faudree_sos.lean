import FormalConjectures.ErdosProblems.«636»

/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/


/-!
# Erdős Problem 88: foundational definitions

This file fixes the exact finite-graph predicates and elementary bookkeeping
used by the formalization of Erdős Problem 88.
-/

open SimpleGraph

namespace Erdos88

universe u

/-- A graph on `Fin n` has no homogeneous set of size at least
`ε * log n`, with `log` the natural logarithm.  A homogeneous set is either
a clique or an independent set. -/
def HomogeneousFree {n : ℕ} (ε : ℝ) (G : SimpleGraph (Fin n)) : Prop :=
  ∀ S : Finset (Fin n),
    (G.IsClique (S : Set (Fin n)) ∨ G.IsIndepSet (S : Set (Fin n))) →
      (S.card : ℝ) < ε * Real.log n

/-- The base-two version of `HomogeneousFree`, matching the `C`-Ramsey
terminology in Kwan--Sah--Sauermann--Sawhney. -/
def RamseyFree {n : ℕ} (C : ℝ) (G : SimpleGraph (Fin n)) : Prop :=
  ∀ S : Finset (Fin n),
    (G.IsClique (S : Set (Fin n)) ∨ G.IsIndepSet (S : Set (Fin n))) →
      (S.card : ℝ) < C * Real.logb 2 n

/-- The number of edges of `G` having both endpoints in `S`. -/
noncomputable def inducedEdges {V : Type u} [Fintype V]
    (G : SimpleGraph V) (S : Finset V) : ℕ :=
  Nat.card (G.induce (S : Set V)).edgeSet

@[simp] lemma inducedEdges_empty {V : Type u} [Fintype V]
    (G : SimpleGraph V) : inducedEdges G ∅ = 0 := by
  classical
  have hbot : G.induce ((↑(∅ : Finset V) : Set V)) = ⊥ := by
    rw [SimpleGraph.eq_bot_iff_forall_not_adj]
    intro x _y _hxy
    simpa using x.property
  rw [inducedEdges, hbot]
  simp

/-- `inducedEdges` is exactly the edge count of Mathlib's induced graph. -/
lemma inducedEdges_eq_card_edgeFinset_induce {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) :
    inducedEdges G S = (G.induce (S : Set V)).edgeFinset.card := by
  classical
  rw [inducedEdges, Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card]

/-- The induced-edge count is also the cardinality of the edge finset
filtered by the condition that both endpoints lie in `S`. -/
lemma inducedEdges_eq_card_filter {V : Type u} [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) :
    inducedEdges G S =
      (G.edgeFinset.filter fun e ↦ e.toFinset ⊆ S).card := by
  rw [inducedEdges_eq_card_edgeFinset_induce]
  exact (G.card_filter_edgeFinset_toFinset_subset S).symm

@[simp] lemma inducedEdges_univ {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    inducedEdges G Finset.univ = G.edgeFinset.card := by
  classical
  rw [inducedEdges, SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card]
  have hU : (↑(Finset.univ : Finset V) : Set V) = Set.univ := by ext; simp
  rw [hU]
  exact Nat.card_congr G.induceUnivIso.mapEdgeSet

/-- A clique in an induced graph is the same clique after forgetting the
subtype proof. -/
lemma isClique_induce_iff {V : Type u} (G : SimpleGraph V) {U : Set V}
    {T : Set U} :
    (G.induce U).IsClique T ↔ G.IsClique (Subtype.val '' T) :=
  SimpleGraph.isClique_induce_iff

/-- An independent set in an induced graph is the same independent set after
forgetting the subtype proof. -/
lemma isIndepSet_induce_iff {V : Type u} (G : SimpleGraph V) {U : Set V}
    {T : Set U} :
    (G.induce U).IsIndepSet T ↔ G.IsIndepSet (Subtype.val '' T) := by
  constructor
  · intro h x hx y hy hxy
    obtain ⟨x, hx, rfl⟩ := hx
    obtain ⟨y, hy, rfl⟩ := hy
    exact h hx hy (fun hxy' ↦ hxy (congrArg Subtype.val hxy'))
  · intro h x hx y hy hxy
    exact h ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩ (fun hxy' ↦ hxy (Subtype.ext hxy'))

/-- Inducing commutes with graph complementation. -/
@[simp] lemma induce_compl {V : Type u} (G : SimpleGraph V) (U : Set V) :
    Gᶜ.induce U = (G.induce U)ᶜ := by
  ext x y
  simp only [SimpleGraph.induce_adj, SimpleGraph.compl_adj]
  exact and_congr (not_congr Subtype.val_injective.eq_iff) Iff.rfl

/-- The natural-log homogeneous-set condition is invariant under graph
complementation. -/
@[simp] lemma homogeneousFree_compl {n : ℕ} {ε : ℝ}
    (G : SimpleGraph (Fin n)) : HomogeneousFree ε Gᶜ ↔ HomogeneousFree ε G := by
  simp only [HomogeneousFree, G.isClique_compl, G.isIndepSet_compl]
  aesop

/-- The base-two Ramsey condition is invariant under graph complementation. -/
@[simp] lemma ramseyFree_compl {n : ℕ} {C : ℝ}
    (G : SimpleGraph (Fin n)) : RamseyFree C Gᶜ ↔ RamseyFree C G := by
  simp only [RamseyFree, G.isClique_compl, G.isIndepSet_compl]
  aesop

/-- Exact conversion between the natural logarithm and the base-two logarithm. -/
lemma log_mul_logb_two (x : ℝ) : Real.log 2 * Real.logb 2 x = Real.log x := by
  rw [← Real.log_div_log]
  field_simp [ne_of_gt (Real.log_pos (by norm_num : (1 : ℝ) < 2))]

/-- The threshold used in `HomogeneousFree` is exactly the KSSS base-two
threshold with constant `ε * log 2`. -/
lemma mul_logb_two_eq_mul_log (ε x : ℝ) :
    (ε * Real.log 2) * Real.logb 2 x = ε * Real.log x := by
  rw [mul_assoc, log_mul_logb_two]

/-- The natural-log and base-two formulations of the homogeneous-set
condition are definitionally equivalent after rescaling the constant. -/
lemma homogeneousFree_iff_ramseyFree {n : ℕ} (ε : ℝ)
    (G : SimpleGraph (Fin n)) :
    HomogeneousFree ε G ↔ RamseyFree (ε * Real.log 2) G := by
  simp only [HomogeneousFree, RamseyFree, mul_logb_two_eq_mul_log]

@[simp] lemma card_fin (n : ℕ) : Fintype.card (Fin n) = n := Fintype.card_fin n

/-- A finset and its corresponding subtype have the same cardinality. -/
lemma card_subtype_coe_finset {V : Type u} (S : Finset V) :
    Fintype.card (S : Set V) = S.card := by
  simp

/-- Forgetting subtype proofs preserves the cardinality of a finite set. -/
lemma card_image_subtype_val {V : Type u} [DecidableEq V] {U : Set V} (T : Finset U) :
    (T.image Subtype.val).card = T.card := by
  exact Finset.card_image_of_injective T Subtype.val_injective

end Erdos88

/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

/-!
# Finite Ramsey theory utilities

This file contains the finite two-color Ramsey definitions and elementary bounds shared by
multiple developments.
-/

open Finset

noncomputable section

namespace SimpleGraph

theorem IndepSetFree.comap {α β : Type*} {G : SimpleGraph α} {H : SimpleGraph β} {n : ℕ}
    (f : H ↪g G) : G.IndepSetFree n → H.IndepSetFree n := by
  intro h
  rw [← cliqueFree_compl] at h ⊢
  exact CliqueFree.comap
    (((Embedding.complEquiv (G := H) (H := G)).toFun f).isContained) h

def Iso.compl {α β : Type*} {G : SimpleGraph α} {H : SimpleGraph β}
    (e : G ≃g H) : Gᶜ ≃g Hᶜ where
  toEquiv := e.toEquiv
  map_rel_iff' := by
    intro v w
    by_cases hvw : v = w
    · subst hvw
      simp
    · simpa [compl_adj, hvw, e.injective.ne_iff] using
        not_congr (e.map_adj_iff (v := v) (w := w))

theorem Iso.cliqueFree_iff {α β : Type*} {G : SimpleGraph α} {H : SimpleGraph β} {n : ℕ}
    (e : G ≃g H) : G.CliqueFree n ↔ H.CliqueFree n := by
  constructor
  · intro h
    exact CliqueFree.comap e.symm.toEmbedding.isContained h
  · intro h
    exact CliqueFree.comap e.toEmbedding.isContained h

theorem Iso.indepSetFree_iff {α β : Type*} {G : SimpleGraph α} {H : SimpleGraph β} {n : ℕ}
    (e : G ≃g H) : G.IndepSetFree n ↔ H.IndepSetFree n := by
  simpa [indepSetFree_compl] using
    (Iso.cliqueFree_iff (n := n) (e := Iso.compl e))

end SimpleGraph

namespace Ramsey

/--
The Ramsey property on `n` vertices: every finite simple graph on `n` vertices contains
either a `k`-clique or an independent set of size `l`.
-/
def RamseyProperty (k l n : ℕ) : Prop :=
  ∀ G : SimpleGraph (Fin n), ¬ (G.CliqueFree k ∧ G.IndepSetFree l)

lemma ramseyProperty_of_card {k l n : ℕ} {α : Type*} [Fintype α]
    (hcard : Fintype.card α = n) (hprop : RamseyProperty k l n) :
    ∀ G : SimpleGraph α, ¬ (G.CliqueFree k ∧ G.IndepSetFree l) := by
  intro G hbad
  let H : SimpleGraph (Fin n) := G.overFin hcard
  let e : G ≃g H := SimpleGraph.overFinIso (G := G) hcard
  have hcf : H.CliqueFree k := hbad.1.comap e.symm.toEmbedding.isContained
  have hcfCompl : Hᶜ.CliqueFree l := by
    have hGCompl : Gᶜ.CliqueFree l := by
      simpa [SimpleGraph.cliqueFree_compl] using hbad.2
    exact hGCompl.comap
      (((SimpleGraph.Embedding.complEquiv (G := H) (H := G)).toFun e.symm.toEmbedding).isContained)
  have hif : H.IndepSetFree l := by
    simpa [SimpleGraph.cliqueFree_compl] using hcfCompl
  exact hprop H ⟨hcf, hif⟩

lemma ramseyProperty_mono {k l n m : ℕ} (hnm : n ≤ m) :
    RamseyProperty k l n → RamseyProperty k l m := by
  intro h G hbad
  let f : Fin n ↪ Fin m := Fin.castLEEmb hnm
  have hcf : (G.comap f).CliqueFree k :=
    hbad.1.comap (SimpleGraph.Embedding.comap f G).isContained
  have hif : (G.comap f).IndepSetFree l :=
    SimpleGraph.IndepSetFree.comap (SimpleGraph.Embedding.comap f G) hbad.2
  exact h (G.comap f) ⟨hcf, hif⟩

/-- Finite Ramsey's theorem, packaged as the existence of a size satisfying `RamseyProperty`. -/
theorem ramseyProperty_exists (k l : ℕ) : ∃ n, RamseyProperty k l n := by
  revert l
  induction k with
  | zero =>
      intro l
      refine ⟨0, ?_⟩
      intro G hbad
      simpa using hbad.1
  | succ k ih =>
      intro l
      induction l with
      | zero =>
          refine ⟨0, ?_⟩
          intro G hbad
          exact hbad.2 ∅ (by simp [SimpleGraph.isNIndepSet_iff])
      | succ l ihl =>
          rcases ih (l + 1) with ⟨m, hm⟩
          rcases ihl with ⟨n, hn⟩
          refine ⟨m + n + 1, ?_⟩
          intro G hbad
          classical
          let v : Fin (m + n + 1) := 0
          by_cases hdeg : m ≤ G.degree v
          · let H : SimpleGraph (G.neighborSet v) := G.induce (G.neighborSet v)
            have hprop : RamseyProperty k (l + 1) (G.degree v) := ramseyProperty_mono hdeg hm
            have hcf : H.CliqueFree k := by
              intro t ht
              let t' : Finset (Fin (m + n + 1)) :=
                Finset.map ⟨Subtype.val, Subtype.val_injective⟩ t
              have htInd :
                  (((⊤ : SimpleGraph.Subgraph G).induce (G.neighborSet v)).coe).IsNClique k t := by
                rw [← SimpleGraph.induce_eq_coe_induce_top]
                exact ht
              have ht' : G.IsNClique k t' := by
                simpa [H, t'] using
                  (SimpleGraph.IsNClique.of_induce
                    (S := (⊤ : SimpleGraph.Subgraph G)) (F := G.neighborSet v) (cc := htInd))
              have hvt : ∀ b ∈ t', G.Adj v b := by
                intro b hb
                rcases Finset.mem_map.mp hb with ⟨x, hx, rfl⟩
                exact x.property
              exact hbad.1 _ (ht'.insert hvt)
            have hif : H.IndepSetFree (l + 1) := by
              exact SimpleGraph.IndepSetFree.comap
                (SimpleGraph.Embedding.induce (G := G) (s := G.neighborSet v)) hbad.2
            exact ramseyProperty_of_card (G.card_neighborSet_eq_degree v) hprop H ⟨hcf, hif⟩
          · let H : SimpleGraph (Gᶜ.neighborSet v) := G.induce (Gᶜ.neighborSet v)
            have hcompdeg : n ≤ Gᶜ.degree v := by
              rw [G.degree_compl (v := v), Fintype.card_fin]
              omega
            have hprop : RamseyProperty (k + 1) l (Gᶜ.degree v) :=
              ramseyProperty_mono hcompdeg hn
            have hcf : H.CliqueFree (k + 1) := by
              exact hbad.1.comap
                (SimpleGraph.Embedding.induce (G := G) (s := Gᶜ.neighborSet v)).isContained
            have hif : H.IndepSetFree l := by
              intro t ht
              let t' : Finset (Fin (m + n + 1)) :=
                Finset.map ⟨Subtype.val, Subtype.val_injective⟩ t
              have htInd :
                  (((⊤ : SimpleGraph.Subgraph G).induce
                    (Gᶜ.neighborSet v)).coe).IsNIndepSet l t := by
                rw [← SimpleGraph.induce_eq_coe_induce_top]
                exact ht
              have ht' : G.IsNIndepSet l t' := by
                simpa [H, t'] using
                  (SimpleGraph.isNIndepSet_induce
                    (G := G) (F := Gᶜ.neighborSet v) (s := t) (n := l)).1 htInd
              have ht'compl : Gᶜ.IsNClique l t' := by
                simpa using ht'
              have hvt : ∀ b ∈ t', Gᶜ.Adj v b := by
                intro b hb
                rcases Finset.mem_map.mp hb with ⟨x, hx, rfl⟩
                exact x.property
              have ht'' : G.IsNIndepSet (l + 1) (insert v t') := by
                simpa using ht'compl.insert hvt
              exact hbad.2 _ ht''
            exact ramseyProperty_of_card (Gᶜ.card_neighborSet_eq_degree v) hprop H ⟨hcf, hif⟩

/-- The off-diagonal Ramsey number `R(k, l)`. -/
def ramseyNumber (k l : ℕ) : ℕ :=
  by
    classical
    exact Nat.find (ramseyProperty_exists k l)

lemma ramseyNumber_spec (k l : ℕ) : RamseyProperty k l (ramseyNumber k l) :=
  by
    classical
    exact Nat.find_spec (ramseyProperty_exists k l)

lemma ramseyProperty_one_left (l : ℕ) : RamseyProperty 1 l 1 := by
  intro G hbad
  simpa [SimpleGraph.cliqueFree_one] using hbad.1

lemma ramseyProperty_mono_vertices {k l n m : ℕ} (hnm : n ≤ m) :
    RamseyProperty k l n → RamseyProperty k l m := by
  intro h G hbad
  let f : Fin n ↪ Fin m := Fin.castLEEmb hnm
  have hcf : (G.comap f).CliqueFree k :=
    hbad.1.comap (SimpleGraph.Embedding.comap f G).isContained
  have hif : (G.comap f).IndepSetFree l :=
    SimpleGraph.IndepSetFree.comap (SimpleGraph.Embedding.comap f G) hbad.2
  exact h (G.comap f) ⟨hcf, hif⟩

lemma ramseyNumber_le_of_property {k l n : ℕ} (hn : RamseyProperty k l n) :
    ramseyNumber k l ≤ n := by
  classical
  exact Nat.find_min' (ramseyProperty_exists k l) hn

lemma ramseyProperty_of_ramseyNumber_le {k l n : ℕ} (hn : ramseyNumber k l ≤ n) :
    RamseyProperty k l n :=
  ramseyProperty_mono_vertices hn (ramseyNumber_spec k l)

lemma ramseyProperty_zero_right (k : ℕ) : RamseyProperty k 0 0 := by
  intro G hbad
  have hnil : G.IsNIndepSet 0 (∅ : Finset (Fin 0)) := by
    simp [SimpleGraph.isNIndepSet_iff]
  exact hbad.2 _ hnil

lemma ramseyNumber_zero_right (k : ℕ) : ramseyNumber k 0 = 0 := by
  exact le_antisymm (ramseyNumber_le_of_property (ramseyProperty_zero_right k)) (Nat.zero_le _)

lemma ramseyNumber_pos {u m : ℕ} (hu : 1 ≤ u) (hm : 1 ≤ m) : 0 < ramseyNumber u m := by
  by_contra hpos
  have hz : ramseyNumber u m = 0 := Nat.eq_zero_of_not_pos hpos
  have hprop : RamseyProperty u m 0 := by
    simpa [hz] using ramseyNumber_spec u m
  let G : SimpleGraph (Fin 0) := ⊥
  have hcf : G.CliqueFree u := by
    have hcard : Fintype.card (Fin 0) < u := by
      simpa [Fintype.card_fin] using (Nat.succ_le_iff.mp hu)
    exact SimpleGraph.cliqueFree_of_card_lt (G := G) hcard
  have hif : G.IndepSetFree m := by
    rw [← SimpleGraph.cliqueFree_compl]
    have hcard : Fintype.card (Fin 0) < m := by
      simpa [Fintype.card_fin] using (Nat.succ_le_iff.mp hm)
    exact SimpleGraph.cliqueFree_of_card_lt (G := Gᶜ) hcard
  exact hprop G ⟨hcf, hif⟩

lemma ramseyProperty_one_right (k : ℕ) : RamseyProperty k 1 1 := by
  intro G hbad
  have hs : G.IsNIndepSet 1 (Finset.univ : Finset (Fin 1)) := by
    refine ⟨?_, by simp⟩
    simp [SimpleGraph.isIndepSet_iff]
  exact hbad.2 _ hs

lemma ramseyProperty_succ_succ_of_sum {k l m n : ℕ}
    (hm : RamseyProperty k (l + 1) m)
    (hn : RamseyProperty (k + 1) l n)
    (hpos : 0 < m + n) :
    RamseyProperty (k + 1) (l + 1) (m + n) := by
  intro G hbad
  classical
  let v : Fin (m + n) := ⟨0, hpos⟩
  by_cases hdeg : m ≤ G.degree v
  · let H : SimpleGraph (G.neighborSet v) := G.induce (G.neighborSet v)
    have hprop : RamseyProperty k (l + 1) (G.degree v) := ramseyProperty_mono hdeg hm
    have hcf : H.CliqueFree k := by
      intro t ht
      let t' : Finset (Fin (m + n)) := Finset.map ⟨Subtype.val, Subtype.val_injective⟩ t
      have htInd :
          (((⊤ : SimpleGraph.Subgraph G).induce (G.neighborSet v)).coe).IsNClique k t := by
        rw [← SimpleGraph.induce_eq_coe_induce_top]
        exact ht
      have ht' : G.IsNClique k t' := by
        simpa [H, t'] using
          (SimpleGraph.IsNClique.of_induce
            (S := (⊤ : SimpleGraph.Subgraph G)) (F := G.neighborSet v) (cc := htInd))
      have hvt : ∀ b ∈ t', G.Adj v b := by
        intro b hb
        rcases Finset.mem_map.mp hb with ⟨x, hx, rfl⟩
        exact x.property
      exact hbad.1 _ (ht'.insert hvt)
    have hif : H.IndepSetFree (l + 1) := by
      exact SimpleGraph.IndepSetFree.comap
        (SimpleGraph.Embedding.induce (G := G) (s := G.neighborSet v)) hbad.2
    exact ramseyProperty_of_card (G.card_neighborSet_eq_degree v) hprop H ⟨hcf, hif⟩
  · let H : SimpleGraph (Gᶜ.neighborSet v) := G.induce (Gᶜ.neighborSet v)
    have hcompdeg : n ≤ Gᶜ.degree v := by
      rw [G.degree_compl (v := v), Fintype.card_fin]
      omega
    have hprop : RamseyProperty (k + 1) l (Gᶜ.degree v) := ramseyProperty_mono hcompdeg hn
    have hcf : H.CliqueFree (k + 1) := by
      exact hbad.1.comap
        (SimpleGraph.Embedding.induce (G := G) (s := Gᶜ.neighborSet v)).isContained
    have hif : H.IndepSetFree l := by
      intro t ht
      let t' : Finset (Fin (m + n)) := Finset.map ⟨Subtype.val, Subtype.val_injective⟩ t
      have htInd :
          (((⊤ : SimpleGraph.Subgraph G).induce
            (Gᶜ.neighborSet v)).coe).IsNIndepSet l t := by
        rw [← SimpleGraph.induce_eq_coe_induce_top]
        exact ht
      have ht' : G.IsNIndepSet l t' := by
        simpa [H, t'] using
          (SimpleGraph.isNIndepSet_induce
            (G := G) (F := Gᶜ.neighborSet v) (s := t) (n := l)).1 htInd
      have ht'compl : Gᶜ.IsNClique l t' := by
        simpa using ht'
      have hvt : ∀ b ∈ t', Gᶜ.Adj v b := by
        intro b hb
        rcases Finset.mem_map.mp hb with ⟨x, hx, rfl⟩
        exact x.property
      have ht'' : G.IsNIndepSet (l + 1) (insert v t') := by
        simpa using ht'compl.insert hvt
      exact hbad.2 _ ht''
    exact ramseyProperty_of_card (Gᶜ.card_neighborSet_eq_degree v) hprop H ⟨hcf, hif⟩

lemma ramseyNumber_recurrence (u m : ℕ) (hu : 1 ≤ u) :
    ramseyNumber (u + 1) (m + 1) ≤ ramseyNumber u (m + 1) + ramseyNumber (u + 1) m := by
  apply ramseyNumber_le_of_property
  have hpos : 0 < ramseyNumber u (m + 1) + ramseyNumber (u + 1) m := by
    exact Nat.add_pos_left (ramseyNumber_pos hu (by omega)) _
  exact ramseyProperty_succ_succ_of_sum
    (ramseyNumber_spec u (m + 1))
    (ramseyNumber_spec (u + 1) m)
    hpos

lemma ramseyNumber_le_choose (u : ℕ) :
    ∀ m, ramseyNumber (u + 1) m ≤ Nat.choose (u + m - 1) u := by
  induction u with
  | zero =>
      intro m
      cases m with
      | zero =>
          simp [ramseyNumber_zero_right]
      | succ m =>
          have hle : ramseyNumber 1 (m + 1) ≤ 1 := by
            exact ramseyNumber_le_of_property (ramseyProperty_one_left (m + 1))
          simpa using hle
  | succ u ihu =>
      intro m
      induction m with
      | zero =>
          rw [ramseyNumber_zero_right]
          simp
      | succ m ihm =>
          have hrec : ramseyNumber (u + 2) (m + 1) ≤
              ramseyNumber (u + 1) (m + 1) + ramseyNumber (u + 2) m := by
            exact ramseyNumber_recurrence (u + 1) m (by omega)
          have hleft : ramseyNumber (u + 1) (m + 1) ≤ Nat.choose (u + m) u := by
            simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using ihu (m + 1)
          have hright : ramseyNumber (u + 2) m ≤ Nat.choose (u + m) (u + 1) := by
            simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using ihm
          calc
            ramseyNumber (u + 2) (m + 1)
                ≤ ramseyNumber (u + 1) (m + 1) + ramseyNumber (u + 2) m := hrec
            _ ≤ Nat.choose (u + m) u + Nat.choose (u + m) (u + 1) := by
              exact Nat.add_le_add hleft hright
            _ = Nat.choose (u + m + 1) (u + 1) := by
              rw [Nat.choose_succ_succ' (u + m) u]
            _ = Nat.choose (u + 1 + (m + 1) - 1) (u + 1) := by
              simp [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

end Ramsey

/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/


/-!
# The finite Erdős--Szemerédi density argument

This file contains the finite graph-combinatorial core of the 1972
Erdős--Szemerédi density theorem.  The proof follows the explicit
neighbourhood-pattern argument recorded in `tex/88.tex`.
-/

open scoped BigOperators
open Filter Finset SimpleGraph

noncomputable section

namespace Erdos88.FiniteES

/-- The edge count, packaged noncomputably so downstream theorem statements
do not carry implementation-level decidability instances. -/
noncomputable def edgeCount {α : Type*} [Fintype α]
    (G : SimpleGraph α) : ℕ := by
  classical
  exact G.edgeFinset.card

/-- The degree of a vertex, similarly packaged without exposing the
decidability instance for its neighbor set. -/
noncomputable def vertexDegree {α : Type*} [Fintype α]
    (G : SimpleGraph α) (v : α) : ℕ :=
  Nat.card (G.neighborSet v)

lemma vertexDegree_eq_degree {α : Type*} [Fintype α]
    (G : SimpleGraph α) [DecidableRel G.Adj] (v : α) :
    vertexDegree G v = G.degree v := by
  rw [vertexDegree, Nat.card_eq_fintype_card, G.card_neighborSet_eq_degree]

/-- A homogeneous set of order `r` means an `r`-clique or an
`r`-vertex independent set. -/
def HasHomogeneousSet (G : SimpleGraph (Fin n)) (r : ℕ) : Prop :=
  ¬ (G.CliqueFree r ∧ G.IndepSetFree r)

/-- The target order in the explicit finite Erdős--Szemerédi lemma. -/
noncomputable def esTarget (k n : ℕ) : ℕ :=
  ⌊(k : ℝ) * Real.logb 2 n / (512 * Real.logb 2 k)⌋₊

/-- The family of subsets of `L` having at most `s` elements. -/
def smallSubsets (L : Finset α) (s : ℕ) : Finset (Finset α) :=
  L.powerset.filter fun Y ↦ Y.card ≤ s

@[simp] lemma mem_smallSubsets {Y L : Finset α} {s : ℕ} :
    Y ∈ smallSubsets L s ↔ Y ⊆ L ∧ Y.card ≤ s := by
  simp [smallSubsets]

/-- The weighted-powerset estimate used in the neighborhood-pattern
argument.  It is the integral, division-free consequence of
`x^s P ≤ (1+x)^l ≤ exp(s)` with `x=s/l`: if `s ≤ l` and
`16l ≤ ks`, then the number of subsets of an `l`-set of size at most
`s` is at most `k^s`. -/
lemma card_smallSubsets_le_pow {L : Finset α} {s k : ℕ}
    (hspos : 0 < s) (hsl : s ≤ L.card)
    (hscale : 16 * L.card ≤ k * s) :
    ((smallSubsets L s).card : ℝ) ≤ (k : ℝ) ^ s := by
  classical
  let x : ℝ := (s : ℝ) / L.card
  have hlpos : 0 < L.card := hspos.trans_le hsl
  have hxpos : 0 < x := by
    exact div_pos (by exact_mod_cast hspos) (by exact_mod_cast hlpos)
  have hxle : x ≤ 1 := by
    dsimp [x]
    rw [div_le_one (by exact_mod_cast hlpos)]
    exact_mod_cast hsl
  have hweighted :
      ((smallSubsets L s).card : ℝ) * x ^ s ≤ (x + 1) ^ L.card := by
    calc
      ((smallSubsets L s).card : ℝ) * x ^ s =
          ∑ Y ∈ smallSubsets L s, x ^ s := by simp [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ Y ∈ smallSubsets L s, x ^ Y.card := by
        apply Finset.sum_le_sum
        intro Y hY
        exact pow_le_pow_of_le_one hxpos.le hxle (mem_smallSubsets.mp hY).2
      _ ≤ ∑ Y ∈ L.powerset, x ^ Y.card := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro Y hY
          exact Finset.mem_powerset.mpr (mem_smallSubsets.mp hY).1
        · intro Y _hYL _hYsmall
          positivity
      _ = (x + 1) ^ L.card := by
        simpa using Finset.sum_pow_mul_eq_add_pow x 1 L
  have hexp : (x + 1) ^ L.card ≤ Real.exp 1 ^ s := by
    calc
      (x + 1) ^ L.card ≤ Real.exp x ^ L.card := by
        exact pow_le_pow_left₀ (by positivity) (Real.add_one_le_exp x) _
      _ = Real.exp ((L.card : ℝ) * x) := by
        rw [← Real.exp_nat_mul]
      _ = Real.exp (s : ℝ) := by
        congr 1
        dsimp [x]
        field_simp
      _ = Real.exp 1 ^ s := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring
  have hbase : Real.exp 1 ≤ (k : ℝ) * x := by
    have hscaleReal : (16 : ℝ) * L.card ≤ (k : ℝ) * s := by
      exact_mod_cast hscale
    have hsixteen : (16 : ℝ) ≤ (k : ℝ) * x := by
      dsimp [x]
      calc
        (16 : ℝ) ≤ ((k : ℝ) * s) / L.card := by
          apply (le_div_iff₀ (by exact_mod_cast hlpos)).2
          simpa [mul_comm, mul_left_comm] using hscaleReal
        _ = (k : ℝ) * ((s : ℝ) / L.card) := by ring
    exact Real.exp_one_lt_three.le.trans ((by norm_num : (3 : ℝ) ≤ 16).trans hsixteen)
  have hupper :
      ((smallSubsets L s).card : ℝ) * x ^ s ≤
        (k : ℝ) ^ s * x ^ s := by
    calc
      ((smallSubsets L s).card : ℝ) * x ^ s ≤ (x + 1) ^ L.card := hweighted
      _ ≤ Real.exp 1 ^ s := hexp
      _ ≤ ((k : ℝ) * x) ^ s := pow_le_pow_left₀ (Real.exp_pos 1).le hbase _
      _ = (k : ℝ) ^ s * x ^ s := by rw [mul_pow]
  exact le_of_mul_le_mul_right hupper (pow_pos hxpos s)

/-- The same weighted-powerset estimate bounds the asymmetric Ramsey
number.  The deliberately cross-multiplied hypothesis is the exact fact
needed about the auxiliary parameter `t`. -/
lemma ramseyNumber_le_pow_of_scale {h t k : ℕ}
    (hhpos : 0 < h) (htpos : 0 < t)
    (hscale : 16 * (h + t - 1) ≤ k * t) :
    (Ramsey.ramseyNumber h (t + 1) : ℝ) ≤ (k : ℝ) ^ t := by
  let N := h + t - 1
  have hramsey : Ramsey.ramseyNumber h (t + 1) ≤ Nat.choose N t := by
    have hraw := Ramsey.ramseyNumber_le_choose (h - 1) (t + 1)
    have hfirst : h - 1 + 1 = h := by omega
    have hindex : h - 1 + (t + 1) - 1 = N := by omega
    have hsum : N = (h - 1) + t := by omega
    calc
      Ramsey.ramseyNumber h (t + 1) =
          Ramsey.ramseyNumber (h - 1 + 1) (t + 1) := by rw [hfirst]
      _ ≤ Nat.choose (h - 1 + (t + 1) - 1) (h - 1) := hraw
      _ = Nat.choose N (h - 1) := by rw [hindex]
      _ = Nat.choose N t := by rw [hsum, Nat.choose_symm_add]
  have htN : t ≤ N := by simp [N]; omega
  let L : Finset (Fin N) := Finset.univ
  have hchoose : Nat.choose N t ≤ (smallSubsets L t).card := by
    calc
      Nat.choose N t = (L.powersetCard t).card := by simp [L]
      _ ≤ (smallSubsets L t).card := by
        apply Finset.card_le_card
        intro Y hY
        exact mem_smallSubsets.mpr ⟨(Finset.mem_powersetCard.mp hY).1,
          (Finset.mem_powersetCard.mp hY).2.le⟩
  have hsmall : ((smallSubsets L t).card : ℝ) ≤ (k : ℝ) ^ t := by
    apply card_smallSubsets_le_pow htpos
    · simpa [L] using htN
    · simpa [L, N] using hscale
  exact (by exact_mod_cast hramsey.trans hchoose :
    (Ramsey.ramseyNumber h (t + 1) : ℝ) ≤ (smallSubsets L t).card).trans hsmall

/-- The two binomial estimates in the explicit finite proof, with only the
final comparison of a power of `k` with `n` left as a hypothesis.  This is
the useful purely-natural interface for the later logarithmic calculation. -/
lemma pattern_bound_of_power {n k h : ℕ} (L : Finset (Fin n))
    (hk : 64 ≤ k) (_hkh : k < 16 * h)
    (hLh : L.card < h) (hscaleL : k ≤ 16 * L.card)
    (hpower :
      let s := (16 * L.card) ⌈/⌉ k
      let t := (32 * h) ⌈/⌉ k
      8 * k ^ (s + t) ≤ n) :
    let s := (16 * L.card) ⌈/⌉ k
    8 * ((smallSubsets L s).card * Ramsey.ramseyNumber h (s + 1)) ≤ n := by
  have hkpos : 0 < k := by omega
  let s := (16 * L.card) ⌈/⌉ k
  let t := (32 * h) ⌈/⌉ k
  have hLpos : 0 < L.card := by nlinarith
  have hspos : 0 < s := by
    have hsLower : 16 * L.card ≤ k * s := by
      exact (ceilDiv_le_iff_le_mul hkpos).mp le_rfl
    nlinarith
  have htpos : 0 < t := by
    have htLower : 32 * h ≤ k * t := by
      exact (ceilDiv_le_iff_le_mul hkpos).mp le_rfl
    have hhpos : 0 < h := by omega
    nlinarith
  have hsUpper : k * s ≤ 32 * L.card := by
    have hdiv := Nat.div_mul_le_self (16 * L.card + k - 1) k
    have hraw : s * k ≤ 16 * L.card + k - 1 := by
      simpa [s, Nat.ceilDiv_eq_add_pred_div, mul_comm] using hdiv
    have hraw' : s * k ≤ 16 * L.card + k :=
      hraw.trans (Nat.sub_le _ _)
    nlinarith
  have htLower : 32 * h ≤ k * t := by
    exact (ceilDiv_le_iff_le_mul hkpos).mp le_rfl
  have htUpper : k * t ≤ 64 * h := by
    have hdiv := Nat.div_mul_le_self (32 * h + k - 1) k
    have hraw : t * k ≤ 32 * h + k - 1 := by
      simpa [t, Nat.ceilDiv_eq_add_pred_div, mul_comm] using hdiv
    have hraw' : t * k ≤ 32 * h + k :=
      hraw.trans (Nat.sub_le _ _)
    nlinarith
  have hst : s ≤ t := by
    nlinarith
  have hsl : s ≤ L.card := by
    nlinarith
  have hsScale : 16 * L.card ≤ k * s := by
    exact (ceilDiv_le_iff_le_mul hkpos).mp le_rfl
  have hramseyScale : 16 * (h + t - 1) ≤ k * t := by
    have hkt : 32 * t ≤ k * t := Nat.mul_le_mul_right t (by omega)
    omega
  have hsmall := card_smallSubsets_le_pow hspos hsl hsScale
  have hramseyT := ramseyNumber_le_pow_of_scale (by omega) htpos hramseyScale
  have hramseyMono :
      (Ramsey.ramseyNumber h (s + 1) : ℝ) ≤
        Ramsey.ramseyNumber h (t + 1) := by
    have hmonoNat : Ramsey.ramseyNumber h (s + 1) ≤
        Ramsey.ramseyNumber h (t + 1) := by
      apply Ramsey.ramseyNumber_le_of_property
      intro G hbad
      have htprop := Ramsey.ramseyNumber_spec h (t + 1)
      apply htprop G
      refine ⟨hbad.1, ?_⟩
      rw [← SimpleGraph.cliqueFree_compl] at hbad ⊢
      exact hbad.2.mono (Nat.add_le_add_right hst 1)
    exact_mod_cast hmonoNat
  have hproduct :
      (((smallSubsets L s).card * Ramsey.ramseyNumber h (s + 1) : ℕ) : ℝ) ≤
        (k : ℝ) ^ (s + t) := by
    rw [Nat.cast_mul, pow_add]
    exact mul_le_mul hsmall (hramseyMono.trans hramseyT) (Nat.cast_nonneg _) (by positivity)
  have hpowerReal : (8 : ℝ) * (k : ℝ) ^ (s + t) ≤ n := by
    exact_mod_cast hpower
  have hresultReal :
      (((8 * ((smallSubsets L s).card * Ramsey.ramseyNumber h (s + 1))) : ℕ) : ℝ) ≤ n := by
    rw [Nat.cast_mul]
    exact (mul_le_mul_of_nonneg_left hproduct (by norm_num)).trans hpowerReal
  exact_mod_cast hresultReal

/-- The logarithmic calculation behind the final power comparison in the
finite Erdős--Szemerédi lemma. -/
lemma eight_mul_pow_le_of_log_scale {n k h r : ℕ}
    (hn : 16 ≤ n) (hk : 64 ≤ k) (hr : k * r ≤ 96 * h)
    (hhlog : (512 : ℝ) * h * Real.log k ≤ (k : ℝ) * Real.log n) :
    8 * k ^ r ≤ n := by
  have hkReal : (0 : ℝ) < k := by positivity
  have hnReal : (0 : ℝ) < n := by positivity
  have hlogk : 0 ≤ Real.log (k : ℝ) := Real.log_natCast_nonneg k
  have hlogn : 0 ≤ Real.log (n : ℝ) := Real.log_natCast_nonneg n
  have hrReal : (k : ℝ) * r ≤ 96 * h := by exact_mod_cast hr
  have hscaled :
      ((512 : ℝ) * h * Real.log k) / k ≤ Real.log n := by
    exact (div_le_iff₀ hkReal).2 (by simpa [mul_comm, mul_left_comm] using hhlog)
  have hrlog : (r : ℝ) * Real.log k ≤ (3 / 16 : ℝ) * Real.log n := by
    calc
      (r : ℝ) * Real.log k =
          ((k : ℝ) * r) * (Real.log k / k) := by field_simp
      _ ≤ ((96 : ℝ) * h) * (Real.log k / k) := by
        exact mul_le_mul_of_nonneg_right hrReal (div_nonneg hlogk hkReal.le)
      _ = (3 / 16 : ℝ) * (((512 : ℝ) * h * Real.log k) / k) := by ring
      _ ≤ (3 / 16 : ℝ) * Real.log n := by gcongr
  have hlogEight : Real.log (8 : ℝ) ≤ (3 / 4 : ℝ) * Real.log n := by
    have hlogMono : Real.log (16 : ℝ) ≤ Real.log n := by
      exact Real.log_le_log (by norm_num) (by exact_mod_cast hn)
    have h8 : Real.log (8 : ℝ) = 3 * Real.log 2 := by
      calc
        Real.log (8 : ℝ) = Real.log ((2 : ℝ) ^ 3) := by norm_num
        _ = (3 : ℝ) * Real.log 2 := Real.log_pow 2 3
    have h16 : Real.log (16 : ℝ) = 4 * Real.log 2 := by
      calc
        Real.log (16 : ℝ) = Real.log ((2 : ℝ) ^ 4) := by norm_num
        _ = (4 : ℝ) * Real.log 2 := Real.log_pow 2 4
    rw [h8]
    nlinarith [hlogMono, h16]
  have htotal :
      Real.log ((8 : ℝ) * (k : ℝ) ^ r) ≤ Real.log n := by
    rw [Real.log_mul (by norm_num) (pow_ne_zero _ (by positivity)), Real.log_pow]
    nlinarith
  have hreal : (8 : ℝ) * (k : ℝ) ^ r ≤ n :=
    (Real.log_le_log_iff (by positivity) hnReal).mp htotal
  exact_mod_cast hreal

/-- The complete numerical pattern estimate from the logarithmic upper
bound on `h`.  This packages (2.2)--(2.5) of the writeup. -/
lemma pattern_bound_of_log_scale {n k h : ℕ} (L : Finset (Fin n))
    (hn : 16 ≤ n) (hk : 64 ≤ k) (hkh : k < 16 * h)
    (hhlog : (512 : ℝ) * h * Real.log k ≤ (k : ℝ) * Real.log n)
    (hLh : L.card < h) (hscaleL : k ≤ 16 * L.card) :
    let s := (16 * L.card) ⌈/⌉ k
    8 * ((smallSubsets L s).card * Ramsey.ramseyNumber h (s + 1)) ≤ n := by
  apply pattern_bound_of_power L hk hkh hLh hscaleL
  let s := (16 * L.card) ⌈/⌉ k
  let t := (32 * h) ⌈/⌉ k
  have hkpos : 0 < k := by omega
  have hsUpper : k * s ≤ 32 * L.card := by
    have hdiv := Nat.div_mul_le_self (16 * L.card + k - 1) k
    have hraw : s * k ≤ 16 * L.card + k - 1 := by
      simpa [s, Nat.ceilDiv_eq_add_pred_div, mul_comm] using hdiv
    have hraw' : s * k ≤ 16 * L.card + k := hraw.trans (Nat.sub_le _ _)
    calc
      k * s = s * k := Nat.mul_comm _ _
      _ ≤ 16 * L.card + k := hraw'
      _ ≤ 32 * L.card := by omega
  have htUpper : k * t ≤ 64 * h := by
    have hdiv := Nat.div_mul_le_self (32 * h + k - 1) k
    have hraw : t * k ≤ 32 * h + k - 1 := by
      simpa [t, Nat.ceilDiv_eq_add_pred_div, mul_comm] using hdiv
    have hraw' : t * k ≤ 32 * h + k := hraw.trans (Nat.sub_le _ _)
    calc
      k * t = t * k := Nat.mul_comm _ _
      _ ≤ 32 * h + k := hraw'
      _ ≤ 64 * h := by omega
  apply eight_mul_pow_le_of_log_scale hn hk
  · rw [mul_add]
    calc
      k * s + k * t ≤ 32 * L.card + 64 * h := Nat.add_le_add hsUpper htUpper
      _ ≤ 96 * h := by omega
  · exact hhlog

/-- The floor defining `esTarget` satisfies exactly the cross-multiplied
logarithmic upper bound used by the finite argument. -/
lemma esTarget_log_scale {n k : ℕ} (_hn : 2 ≤ n) (hk : 2 ≤ k) :
    (512 : ℝ) * esTarget k n * Real.log k ≤
      (k : ℝ) * Real.log n := by
  have hlogTwo : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hlogn : 0 ≤ Real.log (n : ℝ) := Real.log_natCast_nonneg n
  have hlogk : 0 < Real.log (k : ℝ) := Real.log_pos (by exact_mod_cast hk)
  have hlogbn : 0 ≤ Real.logb 2 (n : ℝ) :=
    div_nonneg hlogn hlogTwo.le
  have hlogbk : 0 < Real.logb 2 (k : ℝ) :=
    div_pos hlogk hlogTwo
  have harg : 0 ≤
      (k : ℝ) * Real.logb 2 n / (512 * Real.logb 2 k) := by positivity
  have hfloor : (esTarget k n : ℝ) ≤
      (k : ℝ) * Real.logb 2 n / (512 * Real.logb 2 k) := by
    exact Nat.floor_le harg
  have hmul : (esTarget k n : ℝ) * (512 * Real.logb 2 k) ≤
      (k : ℝ) * Real.logb 2 n :=
    (le_div_iff₀ (mul_pos (by norm_num) hlogbk)).mp hfloor
  have hquot :
      ((512 : ℝ) * esTarget k n * Real.log k) / Real.log 2 ≤
        ((k : ℝ) * Real.log n) / Real.log 2 := by
    rw [Real.logb, Real.logb] at hmul
    convert hmul using 1 <;> ring
  exact (div_le_div_iff_of_pos_right hlogTwo).mp hquot

/-- For every positive Ramsey constant one can choose the fixed density
parameter `k` so that the coefficient in `esTarget` is at least `2C`.
This is the only parameter-selection use of `log x = o(x)`. -/
lemma exists_density_parameter (C : ℝ) (hC : 0 < C) :
    ∃ k : ℕ, 64 ≤ k ∧
      2 * C ≤ (k : ℝ) / (512 * Real.logb 2 k) := by
  have hlogTwo : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  let K : ℝ := 1024 * C / Real.log 2
  have hK : 0 < K := by dsimp [K]; positivity
  have heps : 0 < K⁻¹ := inv_pos.mpr hK
  have hreal := Real.isLittleO_log_id_atTop.bound heps
  have hnat := tendsto_natCast_atTop_atTop.eventually hreal
  obtain ⟨k, hkBound, hk⟩ := (hnat.and (eventually_ge_atTop 64)).exists
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.log_natCast_nonneg k), id_eq,
    Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg k)] at hkBound
  have hKlog : K * Real.log (k : ℝ) ≤ k := by
    calc
      K * Real.log (k : ℝ) ≤ K * (K⁻¹ * (k : ℝ)) :=
        mul_le_mul_of_nonneg_left hkBound hK.le
      _ = (k : ℝ) := by field_simp
  have hkpos : (0 : ℝ) < k := by positivity
  have hlogk : 0 < Real.log (k : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < k by omega))
  have hlogbk : 0 < Real.logb 2 (k : ℝ) := div_pos hlogk hlogTwo
  refine ⟨k, hk, ?_⟩
  rw [le_div_iff₀ (mul_pos (by norm_num) hlogbk)]
  dsimp [K] at hKlog
  rw [Real.logb]
  calc
    2 * C * (512 * (Real.log k / Real.log 2)) =
        (1024 * C / Real.log 2) * Real.log k := by ring
    _ ≤ k := hKlog

/-- Eventual side conditions for the explicit finite lemma. -/
lemma exists_density_side_conditions (C : ℝ) (hC : 0 < C) :
    ∃ k N : ℕ, 64 ≤ k ∧ ∀ n : ℕ, N ≤ n →
      let h := esTarget k n
      16 ≤ n ∧ k < 16 * h ∧ 8 * h ≤ n ∧
        C * Real.logb 2 n ≤ (h : ℝ) := by
  obtain ⟨k, hk, hcoeff⟩ := exists_density_parameter C hC
  have hlogTwo : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hlogk : 0 < Real.log (k : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < k by omega))
  let a : ℝ := (k : ℝ) / (512 * Real.log k)
  let c : ℝ := C / Real.log 2
  have ha : 0 < a := by dsimp [a]; positivity
  have hc : 0 < c := by dsimp [c]; positivity
  have hcoeffNat : 2 * c ≤ a := by
    dsimp [a, c]
    rw [Real.logb] at hcoeff
    field_simp at hcoeff ⊢
    nlinarith
  have hlogTendsto : Tendsto (fun n : ℕ ↦ Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlarge : ∀ᶠ n : ℕ in atTop,
      max c⁻¹ (((k : ℝ) / 16 + 1) / a) ≤ Real.log n :=
    hlogTendsto.eventually (eventually_ge_atTop _)
  have heps : 0 < (8 * a)⁻¹ := by positivity
  have hsmallReal := Real.isLittleO_log_id_atTop.bound heps
  have hsmallNat := tendsto_natCast_atTop_atTop.eventually hsmallReal
  have heventually : ∀ᶠ n : ℕ in atTop,
      16 ≤ n ∧
      let h := esTarget k n
      k < 16 * h ∧ 8 * h ≤ n ∧ C * Real.logb 2 n ≤ (h : ℝ) := by
    filter_upwards [eventually_ge_atTop 16, hlarge, hsmallNat] with n hn hnlarge hnsmall
    have hnpos : (0 : ℝ) < n := by positivity
    have hlogn : 0 ≤ Real.log (n : ℝ) := Real.log_natCast_nonneg n
    rw [Real.norm_eq_abs, abs_of_nonneg hlogn, id_eq, Real.norm_eq_abs,
      abs_of_nonneg (Nat.cast_nonneg n)] at hnsmall
    have hsmall : 8 * a * Real.log (n : ℝ) ≤ n := by
      calc
        8 * a * Real.log (n : ℝ) ≤
            8 * a * ((8 * a)⁻¹ * (n : ℝ)) := by gcongr
        _ = (n : ℝ) := by field_simp
    have hcLarge : 1 ≤ c * Real.log (n : ℝ) := by
      have := le_trans (le_max_left c⁻¹ (((k : ℝ) / 16 + 1) / a)) hnlarge
      calc
        (1 : ℝ) = c * c⁻¹ := by field_simp
        _ ≤ c * Real.log (n : ℝ) := mul_le_mul_of_nonneg_left this hc.le
    have haLarge : (k : ℝ) / 16 + 1 ≤ a * Real.log (n : ℝ) := by
      have := le_trans (le_max_right c⁻¹ (((k : ℝ) / 16 + 1) / a)) hnlarge
      calc
        (k : ℝ) / 16 + 1 = a * (((k : ℝ) / 16 + 1) / a) := by field_simp
        _ ≤ a * Real.log (n : ℝ) := mul_le_mul_of_nonneg_left this ha.le
    have hargEq :
        (k : ℝ) * Real.logb 2 n / (512 * Real.logb 2 k) =
          a * Real.log n := by
      dsimp [a]
      rw [Real.logb, Real.logb]
      field_simp
    have hargNonneg : 0 ≤ a * Real.log (n : ℝ) := mul_nonneg ha.le hlogn
    let h := esTarget k n
    have hfloorUpper : (h : ℝ) ≤ a * Real.log (n : ℝ) := by
      dsimp [h, esTarget]
      rw [hargEq]
      exact Nat.floor_le hargNonneg
    have hfloorLower : a * Real.log (n : ℝ) < (h : ℝ) + 1 := by
      dsimp [h, esTarget]
      rw [hargEq]
      exact Nat.lt_floor_add_one _
    have hthreshold : C * Real.logb 2 n ≤ (h : ℝ) := by
      have hx : C * Real.logb 2 n = c * Real.log n := by
        dsimp [c]
        rw [Real.logb]
        ring
      rw [hx]
      have htwice : 2 * (c * Real.log (n : ℝ)) ≤
          a * Real.log (n : ℝ) := by
        simpa [mul_assoc] using mul_le_mul_of_nonneg_right hcoeffNat hlogn
      nlinarith
    have hkh : k < 16 * h := by
      exact_mod_cast (show (k : ℝ) < 16 * h by nlinarith)
    have hhn : 8 * h ≤ n := by
      exact_mod_cast (show (8 : ℝ) * h ≤ n by nlinarith)
    exact ⟨hn, hkh, hhn, hthreshold⟩
  obtain ⟨N, hN⟩ := eventually_atTop.mp heventually
  refine ⟨k, N, hk, ?_⟩
  intro n hn
  exact hN n hn

/-- Vertices whose degree is strictly below `4n/k`, written without
division so that all subsequent double counting is over natural numbers. -/
noncomputable def lowDegreeSet {n : ℕ} (G : SimpleGraph (Fin n)) (k : ℕ) :
    Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun v ↦ k * vertexDegree G v < 4 * n

@[simp] lemma mem_lowDegreeSet {n k : ℕ} {G : SimpleGraph (Fin n)}
    {v : Fin n} :
    v ∈ lowDegreeSet G k ↔ k * vertexDegree G v < 4 * n := by
  classical
  simp [lowDegreeSet]

/-- More than half the vertices have degree below `4n/k` when
`e(G) < n²/k`.  Both inequalities are cross-multiplied over `ℕ`. -/
lemma card_lowDegreeSet_gt_half {n k : ℕ} (G : SimpleGraph (Fin n))
    (hedges : k * edgeCount G < n ^ 2) :
    n < 2 * (lowDegreeSet G k).card := by
  classical
  let D := lowDegreeSet G k
  let E := Finset.univ \ D
  have hDE : D.card + E.card = n := by
    change D.card + (Finset.univ \ D).card = n
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ D)]
    have hDn : D.card ≤ n := by
      simpa [D] using Finset.card_le_card (Finset.subset_univ D)
    rw [show (Finset.univ : Finset (Fin n)).card = n by simp]
    exact Nat.add_sub_of_le hDn
  have hdeg : ∀ v ∈ E, 4 * n ≤ k * vertexDegree G v := by
    intro v hv
    have hv' : v ∉ D := (Finset.mem_sdiff.mp hv).2
    have hv'' : ¬ k * vertexDegree G v < 4 * n := by
      intro h
      exact hv' (by simpa [D, lowDegreeSet] using h)
    exact Nat.le_of_not_gt hv''
  have hsumLower : E.card * (4 * n) ≤ ∑ v ∈ E, k * vertexDegree G v := by
    simpa [Finset.sum_const_nat] using Finset.sum_le_sum hdeg
  have hsumSubset : (∑ v ∈ E, vertexDegree G v) ≤ ∑ v, vertexDegree G v := by
    exact Finset.sum_le_sum_of_subset (by simp [E])
  have hhandshake : ∑ v, vertexDegree G v = 2 * edgeCount G := by
    calc
      ∑ v, vertexDegree G v = ∑ v, G.degree v := by
        apply Finset.sum_congr rfl
        intro v hv
        exact vertexDegree_eq_degree G v
      _ = 2 * edgeCount G := by
        simpa [edgeCount] using G.sum_degrees_eq_twice_card_edges
  by_contra hhalf
  change ¬ n < 2 * D.card at hhalf
  have hcard : n ≤ 2 * E.card := by omega
  have hquad : 2 * n ^ 2 ≤ E.card * (4 * n) := by nlinarith
  have hupper : (∑ v ∈ E, k * vertexDegree G v) ≤ k * (2 * edgeCount G) := by
    rw [← Finset.mul_sum, ← hhandshake]
    exact Nat.mul_le_mul_left k hsumSubset
  have hle : 2 * n ^ 2 ≤ k * (2 * edgeCount G) :=
    hquad.trans (hsumLower.trans hupper)
  have hlt : k * (2 * edgeCount G) < 2 * n ^ 2 := by
    calc
      k * (2 * edgeCount G) = 2 * (k * edgeCount G) := by ring
      _ < 2 * n ^ 2 := Nat.mul_lt_mul_of_pos_left hedges (by omega)
  omega

/-- Every neighborhood trace on `L` is a subset of `L`. -/
lemma neighborTrace_subset [Fintype α] [DecidableEq α]
    (G : SimpleGraph α) [DecidableRel G.Adj]
    (v : α) (L : Finset α) :
    G.neighborFinset v ∩ L ⊆ L :=
  inter_subset_right

/-- If all neighborhood traces have size at most `s`, their image is
contained in `smallSubsets L s`. -/
lemma neighborTrace_mem_smallSubsets [Fintype α] [DecidableEq α]
    (G : SimpleGraph α) [DecidableRel G.Adj]
    {B L : Finset α} {s : ℕ}
    (hsmall : ∀ v ∈ B, #(G.neighborFinset v ∩ L) ≤ s) :
    ∀ v ∈ B, G.neighborFinset v ∩ L ∈ smallSubsets L s := by
  intro v hv
  exact mem_smallSubsets.mpr ⟨inter_subset_right, hsmall v hv⟩

/-- Pigeonholing bounded neighborhood traces. -/
theorem exists_uniform_neighborTrace
    {n s q : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    {B L : Finset (Fin n)}
    (hsmall : ∀ v ∈ B, #(G.neighborFinset v ∩ L) ≤ s)
    (hmul : (smallSubsets L s).card * q < B.card) :
    ∃ Y Z : Finset (Fin n),
      Y ∈ smallSubsets L s ∧ Z ⊆ B ∧ q < Z.card ∧
        ∀ z ∈ Z, G.neighborFinset z ∩ L = Y := by
  classical
  obtain ⟨Y, hY, hfiber⟩ :=
    Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to
      (s := B) (t := smallSubsets L s)
      (f := fun v ↦ G.neighborFinset v ∩ L)
      (neighborTrace_mem_smallSubsets G hsmall) hmul
  let Z := B.filter fun v ↦ G.neighborFinset v ∩ L = Y
  refine ⟨Y, Z, hY, ?_, ?_, ?_⟩
  · exact filter_subset _ _
  · simpa [Z] using hfiber
  · intro z hz
    exact (mem_filter.mp hz).2

/-- Off-diagonal Ramsey numbers are monotone in the independent-set
parameter. -/
lemma ramseyNumber_mono_right {r p s : ℕ} (hps : p ≤ s) :
    Ramsey.ramseyNumber r p ≤ Ramsey.ramseyNumber r s := by
  apply Ramsey.ramseyNumber_le_of_property
  intro G hbad
  have hsprop := Ramsey.ramseyNumber_spec r s
  apply hsprop G
  refine ⟨hbad.1, ?_⟩
  rw [← SimpleGraph.cliqueFree_compl] at hbad ⊢
  exact hbad.2.mono hps

/-- Every finite vertex set has an independent subset of maximum
cardinality (maximum only among subsets of the given set). -/
theorem exists_maximum_independent_subset
    {n : ℕ} (G : SimpleGraph (Fin n)) (D : Finset (Fin n)) :
    ∃ L : Finset (Fin n),
      L ⊆ D ∧ G.IsIndepSet L ∧
        ∀ I : Finset (Fin n), I ⊆ D → G.IsIndepSet I → I.card ≤ L.card := by
  classical
  let A : Finset (Finset (Fin n)) :=
    D.powerset.filter fun I : Finset (Fin n) ↦ G.IsIndepSet (I : Set (Fin n))
  have hA : A.Nonempty := by
    refine ⟨∅, ?_⟩
    simp [A, SimpleGraph.isIndepSet_iff]
  let cards := A.image fun I ↦ I.card
  have hcards : cards.Nonempty := hA.image _
  let m := cards.max' hcards
  have hm : m ∈ cards := Finset.max'_mem cards hcards
  obtain ⟨L, hLA, hLm⟩ := Finset.mem_image.mp hm
  have hL := Finset.mem_filter.mp hLA
  refine ⟨L, Finset.mem_powerset.mp hL.1, hL.2, ?_⟩
  intro I hID hI
  have hIA : I ∈ A := Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hID, hI⟩
  have hIcard : I.card ∈ cards := Finset.mem_image.mpr ⟨I, hIA, rfl⟩
  rw [hLm]
  exact Finset.le_max' cards I.card hIcard

/-- Maximality consequence: every vertex of `D \ L` has a neighbor in a
maximum independent subset `L`. -/
lemma exists_neighbor_in_maximum_independent_subset
    {n : ℕ} {G : SimpleGraph (Fin n)}
    {D L : Finset (Fin n)} (hLD : L ⊆ D) (hL : G.IsIndepSet L)
    (hmax : ∀ I : Finset (Fin n), I ⊆ D → G.IsIndepSet I → I.card ≤ L.card)
    {v : Fin n} (hv : v ∈ D \ L) :
    ∃ x ∈ L, G.Adj x v := by
  classical
  by_contra hnone
  push Not at hnone
  have hvD : v ∈ D := (Finset.mem_sdiff.mp hv).1
  have hvL : v ∉ L := (Finset.mem_sdiff.mp hv).2
  have hindep : G.IsIndepSet (↑(insert v L) : Set (Fin n)) := by
    rw [Finset.coe_insert]
    apply Set.Pairwise.insert hL
    intro x hx _hvx
    have hnxv := hnone x (by simpa using hx)
    exact ⟨by simpa [G.adj_comm] using hnxv, hnxv⟩
  have hsub : insert v L ⊆ D := insert_subset hvD hLD
  have hle := hmax (insert v L) hsub (by
    show G.IsIndepSet (↑(insert v L) : Set (Fin n))
    exact hindep)
  rw [card_insert_of_notMem hvL] at hle
  omega

/-- The vertices outside a maximum independent subset are covered by the
neighborhoods of its vertices. -/
lemma card_sdiff_le_sum_vertexDegree
    {n : ℕ} {G : SimpleGraph (Fin n)}
    {D L : Finset (Fin n)} (hLD : L ⊆ D) (hL : G.IsIndepSet L)
    (hmax : ∀ I : Finset (Fin n), I ⊆ D → G.IsIndepSet I → I.card ≤ L.card) :
    (D \ L).card ≤ ∑ x ∈ L, vertexDegree G x := by
  classical
  have hcover : D \ L ⊆ L.biUnion fun x ↦ G.neighborFinset x := by
    intro v hv
    obtain ⟨x, hxL, hxv⟩ :=
      exists_neighbor_in_maximum_independent_subset hLD hL hmax hv
    exact Finset.mem_biUnion.mpr ⟨x, hxL, by simpa using hxv⟩
  calc
    (D \ L).card ≤ (L.biUnion fun x ↦ G.neighborFinset x).card :=
      Finset.card_le_card hcover
    _ ≤ ∑ x ∈ L, (G.neighborFinset x).card := Finset.card_biUnion_le
    _ = ∑ x ∈ L, vertexDegree G x := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [G.card_neighborFinset_eq_degree, ← vertexDegree_eq_degree]

/-- Double-counting the adjacencies between two finite vertex sets. -/
lemma sum_card_neighborFinset_inter_comm
    {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (A B : Finset (Fin n)) :
    (∑ a ∈ A, #(G.neighborFinset a ∩ B)) =
      ∑ b ∈ B, #(G.neighborFinset b ∩ A) := by
  classical
  calc
    (∑ a ∈ A, #(G.neighborFinset a ∩ B)) =
        ∑ a ∈ A, #(B.bipartiteAbove G.Adj a) := by
          apply Finset.sum_congr rfl
          intro a ha
          congr 1
          ext b
          simp [and_comm]
    _ = ∑ b ∈ B, #(A.bipartiteBelow G.Adj b) :=
      Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow G.Adj
    _ = ∑ b ∈ B, #(G.neighborFinset b ∩ A) := by
      apply Finset.sum_congr rfl
      intro b hb
      congr 1
      ext a
      simp [and_comm, G.adj_comm]

/-- Vertices outside `L` whose trace on `L` has at least `s` elements. -/
def highTraceSet {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (D L : Finset (Fin n)) (s : ℕ) : Finset (Fin n) := by
  exact (D \ L).filter fun v ↦ s ≤ #(G.neighborFinset v ∩ L)

@[simp] lemma mem_highTraceSet
    {n s : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {D L : Finset (Fin n)} {v : Fin n} :
    v ∈ highTraceSet G D L s ↔
      v ∈ D \ L ∧ s ≤ #(G.neighborFinset v ∩ L) := by
  simp only [highTraceSet, Finset.mem_filter]

/-- The high-trace set has fewer than `n/4` vertices.  This is the second
double-counting step in the finite Erdős--Szemerédi proof. -/
lemma four_mul_card_highTraceSet_lt
    {n k s : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {D L : Finset (Fin n)}
    (hD : D = lowDegreeSet G k) (hLD : L ⊆ D) (hLpos : 0 < L.card)
    (hscale : 16 * L.card ≤ k * s) :
    4 * (highTraceSet G D L s).card < n := by
  let T := highTraceSet G D L s
  have hTDL : T ⊆ D \ L := by
    intro v hv
    exact ((mem_highTraceSet (G := G)).mp hv).1
  have hlower : T.card * s ≤ ∑ v ∈ T, #(G.neighborFinset v ∩ L) := by
    have hconst : (∑ _v ∈ T, s) = T.card * s := by simp
    rw [← hconst]
    apply Finset.sum_le_sum
    intro v hv
    exact ((mem_highTraceSet (G := G) (D := D) (L := L) (s := s)).mp hv).2
  have hsumMono :
      (∑ v ∈ T, #(G.neighborFinset v ∩ L)) ≤
        ∑ v ∈ D \ L, #(G.neighborFinset v ∩ L) :=
    Finset.sum_le_sum_of_subset hTDL
  have hdouble :
      (∑ v ∈ D \ L, #(G.neighborFinset v ∩ L)) =
        ∑ x ∈ L, #(G.neighborFinset x ∩ (D \ L)) :=
    sum_card_neighborFinset_inter_comm G (D \ L) L
  have htoDegree :
      (∑ x ∈ L, #(G.neighborFinset x ∩ (D \ L))) ≤
        ∑ x ∈ L, vertexDegree G x := by
    apply Finset.sum_le_sum
    intro x hx
    calc
      #(G.neighborFinset x ∩ (D \ L)) ≤ #(G.neighborFinset x) :=
        Finset.card_le_card Finset.inter_subset_left
      _ = vertexDegree G x := by
        rw [G.card_neighborFinset_eq_degree, vertexDegree_eq_degree]
  have hincidence : T.card * s ≤ ∑ x ∈ L, vertexDegree G x := by
    exact hlower.trans (hsumMono.trans (hdouble.le.trans htoDegree))
  have hdegreeSmall :
      k * (∑ x ∈ L, vertexDegree G x) < L.card * (4 * n) := by
    rw [Finset.mul_sum]
    have hlt := Finset.sum_lt_sum_of_nonempty (Finset.card_pos.mp hLpos)
      (fun x hx ↦ (mem_lowDegreeSet.mp (by rw [← hD]; exact hLD hx)))
    simpa [Finset.sum_const_nat] using hlt
  by_contra hbad
  change ¬4 * T.card < n at hbad
  have hquarter : n ≤ 4 * T.card := Nat.le_of_not_gt hbad
  nlinarith

/-- The residual low-trace class after removing `L` and the high-trace
vertices. -/
def residualSet {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (D L : Finset (Fin n)) (s : ℕ) : Finset (Fin n) :=
  (D \ L) \ highTraceSet G D L s

@[simp] lemma mem_residualSet
    {n s : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {D L : Finset (Fin n)} {v : Fin n} :
    v ∈ residualSet G D L s ↔
      v ∈ D \ L ∧ #(G.neighborFinset v ∩ L) < s := by
  simp only [residualSet, Finset.mem_sdiff, mem_highTraceSet]
  constructor
  · rintro ⟨hvDL, hvT⟩
    exact ⟨hvDL, Nat.lt_of_not_ge (fun hs ↦ hvT ⟨hvDL, hs⟩)⟩
  · rintro ⟨hvDL, hsmall⟩
    exact ⟨hvDL, fun hvT ↦ (Nat.not_le_of_lt hsmall) hvT.2⟩

/-- Under the three cardinal estimates in the finite proof, the residual
set has more than `n/8` vertices. -/
lemma card_residualSet_gt_eighth
    {n h s : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {D L : Finset (Fin n)}
    (hLD : L ⊆ D) (hDhalf : n < 2 * D.card)
    (hLh : L.card < h) (hhn : 8 * h ≤ n)
    (hT : 4 * (highTraceSet G D L s).card < n) :
    n < 8 * (residualSet G D L s).card := by
  classical
  have hTsub : highTraceSet G D L s ⊆ D \ L := by
    intro v hv
    exact (mem_highTraceSet.mp hv).1
  have hDsplit : L.card + (D \ L).card = D.card := by
    rw [Finset.card_sdiff_of_subset hLD]
    omega
  have hBsplit :
      (highTraceSet G D L s).card + (residualSet G D L s).card =
        (D \ L).card := by
    rw [residualSet, Finset.card_sdiff_of_subset hTsub]
    omega
  omega

/-- The first numerical consequence in the finite proof: a maximum
independent subset of the low-degree set has size at least `k/16`, in the
cross-multiplied form `k ≤ 16 * |L|`. -/
lemma sixteen_mul_card_maximum_independent_ge
    {n k h : ℕ} {G : SimpleGraph (Fin n)}
    {D L : Finset (Fin n)}
    (hD : D = lowDegreeSet G k) (hk : 64 ≤ k)
    (hkh : k < 16 * h) (hhn : 8 * h ≤ n)
    (hDhalf : n < 2 * D.card)
    (hLD : L ⊆ D) (hL : G.IsIndepSet L)
    (hmax : ∀ I : Finset (Fin n), I ⊆ D → G.IsIndepSet I → I.card ≤ L.card)
    (hLh : L.card < h) :
    k ≤ 16 * L.card := by
  classical
  have hnpos : 0 < n := by omega
  have hDnonempty : D.Nonempty := by rw [← card_pos]; omega
  obtain ⟨v, hvD⟩ := hDnonempty
  have hsingleton : G.IsIndepSet ({v} : Finset (Fin n)) := by
    simp [SimpleGraph.isIndepSet_iff]
  have hLpos : 0 < L.card := by
    have := hmax {v} (by simpa using hvD) hsingleton
    simpa using this
  have hdiff := card_sdiff_le_sum_vertexDegree hLD hL hmax
  have hLDcard : L.card ≤ D.card := Finset.card_le_card hLD
  have hDsplit : L.card + (D \ L).card = D.card := by
    rw [Finset.card_sdiff_of_subset hLD]
    omega
  have hdiffLarge : n < 4 * (D \ L).card := by omega
  have hsumSmall :
      k * (∑ x ∈ L, vertexDegree G x) < L.card * (4 * n) := by
    rw [Finset.mul_sum]
    have := Finset.sum_lt_sum_of_nonempty (Finset.card_pos.mp hLpos)
      (fun x hx ↦ (mem_lowDegreeSet.mp (by rw [← hD]; exact hLD hx)))
    simpa [Finset.sum_const_nat] using this
  by_contra hbad
  have hbad' : 16 * L.card < k := Nat.lt_of_not_ge hbad
  nlinarith

/-- Ramsey's theorem applied to an induced graph.  If `B` has at least
`R(r,q)` vertices, then `B` contains an `r`-clique or a `q`-independent set
of the ambient graph. -/
theorem clique_or_independent_subset_of_ramseyNumber_le
    {n r q : ℕ} (G : SimpleGraph (Fin n)) (B : Finset (Fin n))
    (hcard : Ramsey.ramseyNumber r q ≤ B.card) :
    (∃ K : Finset (Fin n), K ⊆ B ∧ G.IsNClique r K) ∨
      (∃ I : Finset (Fin n), I ⊆ B ∧ G.IsNIndepSet q I) := by
  classical
  let H : SimpleGraph (B : Set (Fin n)) := G.induce (B : Set (Fin n))
  have hprop : Ramsey.RamseyProperty r q B.card :=
    Ramsey.ramseyProperty_of_ramseyNumber_le hcard
  have hnot : ¬ (H.CliqueFree r ∧ H.IndepSetFree q) :=
    Ramsey.ramseyProperty_of_card (by simp) hprop H
  simp only [not_and_or] at hnot
  rcases hnot with hclique | hindep
  · left
    simp only [SimpleGraph.CliqueFree, not_forall] at hclique
    obtain ⟨K, hK⟩ := hclique
    have hK' : H.IsNClique r K := by simpa using hK
    let K' : Finset (Fin n) := K.map ⟨Subtype.val, Subtype.val_injective⟩
    refine ⟨K', ?_, ?_⟩
    · intro x hx
      obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hx
      exact y.property
    · refine ⟨?_, ?_⟩
      · intro x hx y hy hxy
        obtain ⟨x', hx', rfl⟩ := Finset.mem_map.mp hx
        obtain ⟨y', hy', rfl⟩ := Finset.mem_map.mp hy
        exact hK'.isClique hx' hy' (by simpa using hxy)
      · simpa [K'] using hK'.card_eq
  · right
    simp only [SimpleGraph.IndepSetFree, not_forall] at hindep
    obtain ⟨I, hI⟩ := hindep
    have hI' : H.IsNIndepSet q I := by simpa using hI
    let I' : Finset (Fin n) := I.map ⟨Subtype.val, Subtype.val_injective⟩
    refine ⟨I', ?_, ?_⟩
    · intro x hx
      obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hx
      exact y.property
    · refine ⟨?_, ?_⟩
      · intro x hx y hy hxy
        obtain ⟨x', hx', rfl⟩ := Finset.mem_map.mp hx
        obtain ⟨y', hy', rfl⟩ := Finset.mem_map.mp hy
        exact hI'.isIndepSet hx' hy' (by simpa using hxy)
      · simpa [I'] using hI'.card_eq

/-- The Ramsey endpoint of the finite Erdős--Szemerédi argument.

If every independent set in `Z` has at most `p` vertices and `Z` has at
least `R(h,p+1)` vertices, then a graph with no `h`-clique is impossible. -/
theorem not_cliqueFree_of_large_set_indep_card_le
    {n h p : ℕ} {G : SimpleGraph (Fin n)} {Z : Finset (Fin n)}
    (hZ : Ramsey.ramseyNumber h (p + 1) ≤ Z.card)
    (hindep : ∀ I : Finset (Fin n), I ⊆ Z → G.IsIndepSet I → I.card ≤ p) :
    ¬ G.CliqueFree h := by
  intro hfree
  rcases clique_or_independent_subset_of_ramseyNumber_le G Z hZ with hK | hI
  · obtain ⟨K, -, hKr⟩ := hK
    exact hfree K hKr
  · obtain ⟨I, hIZ, hIr⟩ := hI
    have := hindep I hIZ hIr.isIndepSet
    rw [hIr.card_eq] at this
    omega

/-- Uniform neighborhood traces turn an independent set in `Z` into a
larger independent set by replacing its common neighborhood in `L`.
This is the key exchange step in the finite Erdős--Szemerédi proof. -/
lemma card_indep_le_of_uniform_trace
    {n : ℕ} {G : SimpleGraph (Fin n)} {D L Y Z : Finset (Fin n)}
    [DecidableRel G.Adj]
    (hL : G.IsIndepSet L) (hLD : L ⊆ D) (hYL : Y ⊆ L)
    (hZD : Z ⊆ D)
    (hZL : Disjoint Z L)
    (htrace : ∀ z ∈ Z, G.neighborFinset z ∩ L = Y)
    (hmax : ∀ I : Finset (Fin n), I ⊆ D → G.IsIndepSet I → I.card ≤ L.card)
    {I : Finset (Fin n)} (hIZ : I ⊆ Z) (hI : G.IsIndepSet I) :
    I.card ≤ Y.card := by
  classical
  let J := (L \ Y) ∪ I
  have hdisj : Disjoint (L \ Y) I := by
    exact (Finset.disjoint_of_subset_left sdiff_subset
      (Finset.disjoint_of_subset_right hIZ hZL.symm))
  have hJ : G.IsIndepSet J := by
    intro x hx y hy hxy
    change x ∈ (L \ Y) ∪ I at hx
    change y ∈ (L \ Y) ∪ I at hy
    rw [mem_union] at hx hy
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · exact hL (Finset.mem_sdiff.mp hx).1 (Finset.mem_sdiff.mp hy).1 hxy
    · have hxL : x ∈ L := (Finset.mem_sdiff.mp hx).1
      have hxY : x ∉ Y := (Finset.mem_sdiff.mp hx).2
      have hyZ : y ∈ Z := hIZ hy
      intro hadj
      have hxyN : x ∈ G.neighborFinset y := by
        simpa [G.adj_comm] using hadj
      apply hxY
      rw [← htrace y hyZ]
      exact mem_inter.mpr ⟨hxyN, hxL⟩
    · have hyL : y ∈ L := (Finset.mem_sdiff.mp hy).1
      have hyY : y ∉ Y := (Finset.mem_sdiff.mp hy).2
      have hxZ : x ∈ Z := hIZ hx
      intro hadj
      have hxyN : y ∈ G.neighborFinset x := by simpa using hadj
      apply hyY
      rw [← htrace x hxZ]
      exact mem_inter.mpr ⟨hxyN, hyL⟩
    · exact hI hx hy hxy
  have hJD : J ⊆ D := union_subset (sdiff_subset.trans hLD) (hIZ.trans hZD)
  have hcardJ := hmax J hJD hJ
  have hYLcard : Y.card ≤ L.card := card_le_card hYL
  change ((L \ Y) ∪ I).card ≤ L.card at hcardJ
  rw [card_union_of_disjoint hdisj, card_sdiff_of_subset hYL] at hcardJ
  omega

/-- A uniform neighborhood-trace class of Ramsey size forces an `h`-clique,
provided `L` is a maximum independent set and the class is disjoint from
`L`. -/
theorem not_cliqueFree_of_uniform_trace
    {n h p : ℕ} {G : SimpleGraph (Fin n)} {D L Y Z : Finset (Fin n)}
    [DecidableRel G.Adj]
    (hL : G.IsIndepSet L) (hLD : L ⊆ D) (hYL : Y ⊆ L) (hp : Y.card = p)
    (hZD : Z ⊆ D)
    (hZL : Disjoint Z L)
    (htrace : ∀ z ∈ Z, G.neighborFinset z ∩ L = Y)
    (hmax : ∀ I : Finset (Fin n), I ⊆ D → G.IsIndepSet I → I.card ≤ L.card)
    (hlarge : Ramsey.ramseyNumber h (p + 1) ≤ Z.card) :
    ¬ G.CliqueFree h := by
  apply not_cliqueFree_of_large_set_indep_card_le hlarge
  intro I hIZ hI
  simpa [hp] using
    card_indep_le_of_uniform_trace hL hLD hYL hZD hZL htrace hmax hIZ hI

/-- The complete neighborhood-pattern core of the finite
Erdős--Szemerédi lemma.  The remaining hypotheses in the explicit theorem
are purely numerical estimates ensuring `hmul`. -/
theorem finiteES_pattern_core
    {n h s : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {D L B : Finset (Fin n)}
    (hL : G.IsIndepSet L) (hLD : L ⊆ D)
    (hmax : ∀ I : Finset (Fin n), I ⊆ D → G.IsIndepSet I → I.card ≤ L.card)
    (hBD : B ⊆ D) (hBL : Disjoint B L)
    (hsmall : ∀ v ∈ B, #(G.neighborFinset v ∩ L) ≤ s)
    (hmul : (smallSubsets L s).card * Ramsey.ramseyNumber h (s + 1) < B.card) :
    ¬ G.CliqueFree h := by
  classical
  obtain ⟨Y, Z, hY, hZB, hZlarge, htrace⟩ :=
    exists_uniform_neighborTrace G hsmall hmul
  have hYL : Y ⊆ L := (mem_smallSubsets.mp hY).1
  have hYs : Y.card ≤ s := (mem_smallSubsets.mp hY).2
  have hramsey : Ramsey.ramseyNumber h (Y.card + 1) ≤ Z.card := by
    exact (ramseyNumber_mono_right (Nat.add_le_add_right hYs 1)).trans hZlarge.le
  exact not_cliqueFree_of_uniform_trace hL hLD hYL rfl
    (hZB.trans hBD) (hBL.mono_left hZB) htrace hmax hramsey

/-- The explicit finite Erdős--Szemerédi argument with its final binomial
and Ramsey estimates isolated as a single, purely numerical hypothesis.

The hypothesis `hpattern` is exactly the estimate proved in (2.2)--(2.5)
of `tex/88.tex`; all graph-theoretic and double-counting steps are proved
here. -/
theorem finite_erdos_szemeredi_of_pattern_bound
    {n k h : ℕ} (G : SimpleGraph (Fin n))
    (hk : 64 ≤ k) (hkh : k < 16 * h) (hhn : 8 * h ≤ n)
    (hedges : k * edgeCount G < n ^ 2)
    (hpattern : ∀ L : Finset (Fin n), L.card < h → k ≤ 16 * L.card →
      let s := (16 * L.card) ⌈/⌉ k
      8 * ((smallSubsets L s).card * Ramsey.ramseyNumber h (s + 1)) ≤ n) :
    HasHomogeneousSet G h := by
  classical
  intro hfree
  let : DecidableRel G.Adj := Classical.decRel G.Adj
  let D := lowDegreeSet G k
  have hDhalf : n < 2 * D.card := card_lowDegreeSet_gt_half G hedges
  obtain ⟨L, hLD, hL, hmax⟩ := exists_maximum_independent_subset G D
  have hLh : L.card < h := by
    by_contra hnot
    have hhL : h ≤ L.card := Nat.le_of_not_gt hnot
    obtain ⟨I, hIL, hIcard⟩ := Finset.exists_subset_card_eq hhL
    exact hfree.2 I ⟨hL.mono (by exact_mod_cast hIL), hIcard⟩
  have hscaleL : k ≤ 16 * L.card :=
    sixteen_mul_card_maximum_independent_ge rfl hk hkh hhn hDhalf
      hLD hL hmax hLh
  let s := (16 * L.card) ⌈/⌉ k
  have hkpos : 0 < k := by omega
  have hscaleS : 16 * L.card ≤ k * s := by
    exact (ceilDiv_le_iff_le_mul hkpos).mp le_rfl
  have hLpos : 0 < L.card := by nlinarith
  have hT : 4 * (highTraceSet G D L s).card < n :=
    four_mul_card_highTraceSet_lt rfl hLD hLpos hscaleS
  let B := residualSet G D L s
  have hBlarge : n < 8 * B.card :=
    card_residualSet_gt_eighth hLD hDhalf hLh hhn hT
  have hBD : B ⊆ D := by
    intro v hv
    exact (Finset.mem_sdiff.mp (mem_residualSet.mp hv).1).1
  have hBL : Disjoint B L := by
    apply Finset.disjoint_left.mpr
    intro v hvB hvL
    exact (Finset.mem_sdiff.mp (mem_residualSet.mp hvB).1).2 hvL
  have hsmall : ∀ v ∈ B, #(G.neighborFinset v ∩ L) ≤ s := by
    intro v hv
    exact (mem_residualSet.mp hv).2.le
  have hnumeric := hpattern L hLh hscaleL
  change 8 * ((smallSubsets L s).card * Ramsey.ramseyNumber h (s + 1)) ≤ n at hnumeric
  have hmul :
      (smallSubsets L s).card * Ramsey.ramseyNumber h (s + 1) < B.card := by
    nlinarith
  exact finiteES_pattern_core hL hLD hmax hBD hBL hsmall hmul hfree.1

/-- Explicit finite Erdős--Szemerédi lemma, with the constants and floor
exactly as in `tex/88.tex`. -/
theorem finite_erdos_szemeredi {n k : ℕ} (G : SimpleGraph (Fin n))
    (hn : 16 ≤ n) (hk : 64 ≤ k) :
    let h := esTarget k n
    k < 16 * h → 8 * h ≤ n → k * edgeCount G < n ^ 2 →
      HasHomogeneousSet G h := by
  dsimp only
  intro hkh hhn hedges
  apply finite_erdos_szemeredi_of_pattern_bound G hk hkh hhn hedges
  intro L hLh hscaleL
  exact pattern_bound_of_log_scale L hn hk hkh
    (esTarget_log_scale (by omega) (by omega)) hLh hscaleL

/-- The remaining purely numerical certificate needed to turn the explicit
finite lemma into the eventual Erdős--Szemerédi density theorem. -/
def DensityCertificate (C : ℝ) : Prop :=
  ∃ k N : ℕ, 64 ≤ k ∧ ∀ n : ℕ, N ≤ n →
    let h := esTarget k n
    k < 16 * h ∧ 8 * h ≤ n ∧ C * Real.logb 2 n ≤ (h : ℝ) ∧
      ∀ L : Finset (Fin n), L.card < h → k ≤ 16 * L.card →
        let s := (16 * L.card) ⌈/⌉ k
        8 * ((smallSubsets L s).card * Ramsey.ramseyNumber h (s + 1)) ≤ n

/-- A Ramsey-free graph is both clique-free and independent-set-free at
every integer order at least its real homogeneous-set threshold. -/
lemma cliqueFree_and_indepSetFree_of_ramseyFree
    {n h : ℕ} {C : ℝ} {G : SimpleGraph (Fin n)}
    (hG : RamseyFree C G) (hthreshold : C * Real.logb 2 n ≤ (h : ℝ)) :
    G.CliqueFree h ∧ G.IndepSetFree h := by
  constructor
  · intro S hS
    have hlt := hG S (Or.inl hS.isClique)
    rw [hS.card_eq] at hlt
    exact (not_lt_of_ge hthreshold) hlt
  · intro S hS
    have hlt := hG S (Or.inr hS.isIndepSet)
    rw [hS.card_eq] at hlt
    exact (not_lt_of_ge hthreshold) hlt

/-- The eventual quadratic edge-density consequence of any proved
`DensityCertificate`.  The separate numerical theorem below is the only
ingredient needed to remove the certificate hypothesis. -/
theorem ramseyFree_edgeCount_density_lower_of_certificate
    (C : ℝ) (_hC : 0 < C) (hcert : DensityCertificate C) :
    ∃ a : ℝ, 0 < a ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ G : SimpleGraph (Fin n), RamseyFree C G →
        a * (n : ℝ) ^ 2 ≤ (edgeCount G : ℝ) := by
  obtain ⟨k, N, hk, hcert⟩ := hcert
  have hkpos : 0 < k := by omega
  refine ⟨(k : ℝ)⁻¹, inv_pos.mpr (by exact_mod_cast hkpos), N, ?_⟩
  intro n hn G hG
  obtain ⟨hkh, hhn, hthreshold, hpattern⟩ := hcert n hn
  let h := esTarget k n
  have hfree : G.CliqueFree h ∧ G.IndepSetFree h :=
    cliqueFree_and_indepSetFree_of_ramseyFree hG hthreshold
  have hedgesNat : n ^ 2 ≤ k * edgeCount G := by
    by_contra hnot
    have hsparse : k * edgeCount G < n ^ 2 := Nat.lt_of_not_ge hnot
    exact (finite_erdos_szemeredi_of_pattern_bound G hk hkh hhn hsparse hpattern) hfree
  have hedgesReal : (n : ℝ) ^ 2 ≤ (edgeCount G : ℝ) * k := by
    exact_mod_cast (show n ^ 2 ≤ edgeCount G * k by simpa [mul_comm] using hedgesNat)
  rw [inv_mul_eq_div]
  exact (div_le_iff₀ (by exact_mod_cast hkpos)).2 (by simpa [mul_comm] using hedgesReal)

/-- Erdős--Szemerédi: an exact `C`-Ramsey graph has eventual positive
constant edge density. -/
theorem ramseyFree_edgeCount_density_lower (C : ℝ) (hC : 0 < C) :
    ∃ a : ℝ, 0 < a ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ G : SimpleGraph (Fin n), RamseyFree C G →
        a * (n : ℝ) ^ 2 ≤ (edgeCount G : ℝ) := by
  obtain ⟨k, N, hk, hside⟩ := exists_density_side_conditions C hC
  have hkpos : 0 < k := by omega
  refine ⟨(k : ℝ)⁻¹, inv_pos.mpr (by exact_mod_cast hkpos), N, ?_⟩
  intro n hn G hG
  obtain ⟨hn16, hkh, hhn, hthreshold⟩ := hside n hn
  let h := esTarget k n
  have hfree : G.CliqueFree h ∧ G.IndepSetFree h :=
    cliqueFree_and_indepSetFree_of_ramseyFree hG hthreshold
  have hedgesNat : n ^ 2 ≤ k * edgeCount G := by
    by_contra hnot
    have hsparse : k * edgeCount G < n ^ 2 := Nat.lt_of_not_ge hnot
    exact (finite_erdos_szemeredi G hn16 hk hkh hhn hsparse) hfree
  have hedgesReal : (n : ℝ) ^ 2 ≤ (edgeCount G : ℝ) * k := by
    exact_mod_cast (show n ^ 2 ≤ edgeCount G * k by simpa [mul_comm] using hedgesNat)
  rw [inv_mul_eq_div]
  exact (div_le_iff₀ (by exact_mod_cast hkpos)).2 (by simpa [mul_comm] using hedgesReal)

end Erdos88.FiniteES

namespace Erdos636Proof
open SimpleGraph
lemma eventual_density (C : ℝ) (hC : 0 < C) :
    ∃ a > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N, ∀ G : SimpleGraph (Fin n),
      (G.cliqueNum : ℝ) < C * Real.log n → (G.indepNum : ℝ) < C * Real.log n →
      a * (n : ℝ) ^ 2 ≤ Erdos88.FiniteES.edgeCount G ∧
      a * (n : ℝ) ^ 2 ≤ Erdos88.FiniteES.edgeCount Gᶜ := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨a, ha, N, hN⟩ := Erdos88.FiniteES.ramseyFree_edgeCount_density_lower
    (C * Real.log 2) (mul_pos hC hlog)
  refine ⟨a, ha, N, fun n hn G hcl hind => ?_⟩
  have hf : Erdos88.HomogeneousFree C G := by
    intro S hS
    rcases hS with hc | hi
    · exact lt_of_le_of_lt (by exact_mod_cast hc.card_le_cliqueNum) hcl
    · exact lt_of_le_of_lt (by exact_mod_cast hi.card_le_indepNum) hind
  have hR := (Erdos88.homogeneousFree_iff_ramseyFree C G).mp hf
  exact ⟨hN n hn G hR, hN n hn Gᶜ ((Erdos88.ramseyFree_compl G).2 hR)⟩
end Erdos636Proof

open Finset Filter SimpleGraph

namespace Erdos636Proof

noncomputable def signMean {k : ℕ} (f : (Fin k → Bool) → ℝ) : ℝ :=
  (∑ x, f x) / (2 : ℝ) ^ k

def signValue (x : Bool) : ℝ := if x then 1 else -1

noncomputable def signSum {k : ℕ} (b : Fin k → ℝ) (x : Fin k → Bool) : ℝ :=
  ∑ i, b i * signValue (x i)

lemma signMean_const {k : ℕ} (a : ℝ) :
    signMean (k := k) (fun _ => a) = a := by
  classical
  simp [signMean, Fintype.card_fun, Fintype.card_fin, Nat.cast_pow, mul_div_cancel_left₀,
    pow_ne_zero]

lemma signMean_add {k : ℕ} (f g : (Fin k → Bool) → ℝ) :
    signMean (fun x => f x + g x) = signMean f + signMean g := by
  simp [signMean, Finset.sum_add_distrib, add_div]

lemma signMean_mul {k : ℕ} (c : ℝ) (f : (Fin k → Bool) → ℝ) :
    signMean (fun x => c * f x) = c * signMean f := by
  unfold signMean
  rw [← Finset.mul_sum, mul_div_assoc]

lemma signMean_mono {k : ℕ} {f g : (Fin k → Bool) → ℝ} (h : ∀ x, f x ≤ g x) :
    signMean f ≤ signMean g := by
  apply div_le_div_of_nonneg_right (Finset.sum_le_sum fun a _ => h a) (by positivity)

lemma signMean_cons {k : ℕ} (f : (Fin (k + 1) → Bool) → ℝ) :
    signMean f = signMean (fun x => (f (Fin.cons true x) + f (Fin.cons false x)) / 2) := by
  classical
  unfold signMean
  rw [← (Fin.consEquiv (fun _ : Fin (k + 1) => Bool)).sum_comp f, Fintype.sum_prod_type]
  rw [Fintype.sum_bool]
  change ((∑ y, f (Fin.cons true y)) + ∑ y, f (Fin.cons false y)) / (2 : ℝ) ^ (k + 1) = _
  rw [← Finset.sum_div, Finset.sum_add_distrib, pow_succ, div_div, mul_comm 2]

lemma signSum_cons {k : ℕ} (b : Fin (k + 1) → ℝ) (x : Fin k → Bool) (i : Bool) :
    signSum b (Fin.cons i x) = b 0 * signValue i + signSum (b ∘ Fin.succ) x := by
  simp [signSum, Fin.sum_univ_succ, Function.comp_def]

lemma signMean_second {k : ℕ} (b : Fin k → ℝ) :
    signMean (fun x => signSum b x ^ 2) = ∑ i, b i ^ 2 := by
  induction k with
  | zero => simp [signSum, signMean_const]
  | succ k ih =>
    rw [signMean_cons]
    simp only [signSum_cons, signValue, if_true, mul_one, Bool.false_eq_true, if_false, mul_neg]
    have h : (fun x : Fin k → Bool =>
      ((b 0 + signSum (b ∘ Fin.succ) x) ^ 2 + (-(b 0) + signSum (b ∘ Fin.succ) x) ^ 2) / 2) =
        fun x => b 0 ^ 2 + signSum (b ∘ Fin.succ) x ^ 2 := by
      ext x
      ring
    rw [h, signMean_add, signMean_const, ih, Fin.sum_univ_succ]
    rfl

lemma signMean_fourth {k : ℕ} (b : Fin k → ℝ) :
    signMean (fun x => signSum b x ^ 4) ≤ 3 * (∑ i, b i ^ 2) ^ 2 := by
  induction k with
  | zero => simp [signSum, signMean_const]
  | succ k ih =>
    rw [signMean_cons]
    simp only [signSum_cons, signValue, if_true, mul_one, Bool.false_eq_true, if_false, mul_neg]
    have h : (fun x : Fin k → Bool =>
      ((b 0 + signSum (b ∘ Fin.succ) x) ^ 4 + (-(b 0) + signSum (b ∘ Fin.succ) x) ^ 4) / 2) =
        fun x => b 0 ^ 4 + ((6 * b 0 ^ 2) * signSum (b ∘ Fin.succ) x ^ 2 +
          signSum (b ∘ Fin.succ) x ^ 4) := by
      ext x
      ring
    rw [h, signMean_add, signMean_add, signMean_const, signMean_mul, signMean_second,
      Fin.sum_univ_succ]
    have hb := ih (b ∘ Fin.succ)
    simp only [Function.comp_apply] at hb ⊢
    nlinarith [sq_nonneg (b 0 ^ 2)]

lemma signMean_abs {k : ℕ} (b : Fin k → ℝ) :
    Real.sqrt (∑ i, b i ^ 2) / 5 ≤ signMean (fun x => |signSum b x|) := by
  let v : ℝ := ∑ i, b i ^ 2
  change Real.sqrt v / 5 ≤ _
  have hv : 0 ≤ v := Finset.sum_nonneg fun _ _ => sq_nonneg _
  rcases hv.eq_or_lt with hzero | hvpos
  · rw [← hzero, Real.sqrt_zero, zero_div]
    have h := signMean_mono (k := k) (f := fun _ => 0) (fun x => abs_nonneg (signSum b x))
    simpa only [signMean_const] using h
  let K := Real.sqrt (6 * v)
  have hK : 0 < K := Real.sqrt_pos.2 (by positivity)
  have hKsq : K ^ 2 = 6 * v := Real.sq_sqrt (by positivity)
  have hpoint (t : ℝ) : t ^ 2 ≤ K * |t| + (1 / (6 * v)) * t ^ 4 := by
    rcases le_or_gt |t| K with hl | hg
    · have h1 : |t| ^ 2 ≤ K * |t| := by nlinarith [mul_nonneg (sub_nonneg.mpr hl) (abs_nonneg t)]
      rw [sq_abs] at h1
      exact h1.trans (le_add_of_nonneg_right (by positivity))
    · have h1 : 6 * v ≤ t ^ 2 := by
        rw [← hKsq, ← sq_abs t]
        gcongr
      have h2 : t ^ 2 ≤ (1 / (6 * v)) * t ^ 4 := by
        rw [one_div, inv_mul_eq_div, le_div_iff₀ (by positivity)]
        nlinarith [mul_nonneg (sub_nonneg.mpr h1) (sq_nonneg t)]
      exact h2.trans (le_add_of_nonneg_left (by positivity))
  have hav := signMean_mono (fun x => hpoint (signSum b x))
  rw [signMean_second, signMean_add, signMean_mul, signMean_mul] at hav
  have hfour := signMean_fourth b
  change v ≤ _ at hav
  change _ ≤ 3 * v ^ 2 at hfour
  have hmul := mul_le_mul_of_nonneg_left hfour (show 0 ≤ 1 / (6 * v) by positivity)
  have hsimpl : (1 / (6 * v)) * (3 * v ^ 2) = v / 2 := by field_simp; ring
  rw [hsimpl] at hmul
  have h : v / 2 ≤ K * signMean (fun x => |signSum b x|) := by linarith
  have hsqrt : K = Real.sqrt 6 * Real.sqrt v := Real.sqrt_mul (by norm_num) _
  have hsix : Real.sqrt 6 ≤ 5 / 2 := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  apply (mul_le_mul_iff_of_pos_left hK).mp
  refine le_trans ?_ h
  rw [hsqrt, mul_comm (Real.sqrt 6 * Real.sqrt v)]
  have hvsq := Real.sq_sqrt hv
  calc Real.sqrt v / 5 * (Real.sqrt 6 * Real.sqrt v)
    _ = Real.sqrt 6 * (Real.sqrt v ^ 2) / 5 := by ring
    _ ≤ v / 2 := by rw [hvsq]; nlinarith [mul_nonneg (sub_nonneg.mpr hsix) hv]

end Erdos636Proof

open Finset Filter SimpleGraph

namespace Erdos636Proof

noncomputable def adjacencyBit {V : Type*} (G : SimpleGraph V) (a b : V) : ℝ :=
  open scoped Classical in if G.Adj a b then 1 else 0

lemma adjacencyBit_symm {V : Type*} (G : SimpleGraph V) (a b : V) :
    adjacencyBit G a b = adjacencyBit G b a := by
  classical
  simp [adjacencyBit, G.adj_comm]

lemma adjacencyBit_range {V : Type*} (G : SimpleGraph V) (a b : V) :
    adjacencyBit G a b = 0 ∨ adjacencyBit G a b = 1 := by
  classical
  by_cases h : G.Adj a b <;> simp [adjacencyBit, h]

noncomputable def rectangle {V : Type*} (G : SimpleGraph V) (x : Fin 4 → V) : ℝ :=
  adjacencyBit G (x 0) (x 2) + adjacencyBit G (x 1) (x 3) -
    adjacencyBit G (x 1) (x 2) - adjacencyBit G (x 0) (x 3)

lemma rectangle_sq {V : Type*} (G : SimpleGraph V) (x : Fin 4 → V)
    (hx : rectangle G x ≠ 0) : 1 ≤ rectangle G x ^ 2 := by
  rcases adjacencyBit_range G (x 0) (x 2) with h₁ | h₁ <;>
    rcases adjacencyBit_range G (x 1) (x 3) with h₂ | h₂ <;>
    rcases adjacencyBit_range G (x 1) (x 2) with h₃ | h₃ <;>
    rcases adjacencyBit_range G (x 0) (x 3) with h₄ | h₄ <;>
    norm_num [rectangle, h₁, h₂, h₃, h₄] at hx <;>
    norm_num [rectangle, h₁, h₂, h₃, h₄]

lemma rectangle_in_eight {V : Type*} (G : SimpleGraph V) (x : Fin 8 → V)
    (he : G.Adj (x 0) (x 1) ∧ G.Adj (x 2) (x 3))
    (hn : ¬ G.Adj (x 4) (x 5) ∧ ¬ G.Adj (x 6) (x 7)) :
    ∃ i : Fin 4 ↪ Fin 8, rectangle G (x ∘ i) ≠ 0 := by
  classical
  by_contra! h
  let b (i j : Fin 8) := adjacencyBit G (x i) (x j)
  have he₁ : b 0 1 = 1 := by simp [b, adjacencyBit, he.1]
  have he₂ : b 2 3 = 1 := by simp [b, adjacencyBit, he.2]
  have hn₁ : b 4 5 = 0 := by simp [b, adjacencyBit, hn.1]
  have hn₂ : b 6 7 = 0 := by simp [b, adjacencyBit, hn.2]
  have symm (i j : Fin 8) : b i j = b j i := adjacencyBit_symm G _ _
  have ran (i j : Fin 8) : b i j = 0 ∨ b i j = 1 := adjacencyBit_range G _ _
  have E (i j k l : Fin 8) (he : Function.Injective ![i, j, k, l]) :
      b i k + b j l = b j k + b i l := by
    have hh := h ⟨![i, j, k, l], he⟩
    change b i k + b j l - b j k - b i l = 0 at hh
    linarith
  have eq₁ := E 0 2 1 3 (by intro i j; fin_cases i <;> fin_cases j <;> decide)
  have eq₂ := E 0 3 1 2 (by intro i j; fin_cases i <;> fin_cases j <;> decide)
  have eq₃ := E 4 6 5 7 (by intro i j; fin_cases i <;> fin_cases j <;> decide)
  have eq₄ := E 4 7 5 6 (by intro i j; fin_cases i <;> fin_cases j <;> decide)
  have h02 : b 0 2 = 1 := by
    rw [he₁, symm 3 2, he₂] at eq₂
    rcases ran 0 2 with hh|hh <;> rcases ran 3 1 with hh'|hh' <;> linarith
  have h12 : b 1 2 = 1 := by
    rw [he₁, he₂, symm 2 1] at eq₁
    rcases ran 1 2 with hh|hh <;> rcases ran 0 3 with hh'|hh' <;> linarith
  have h46 : b 4 6 = 0 := by
    rw [hn₁, symm 7 6, hn₂] at eq₄
    rcases ran 4 6 with hh|hh <;> rcases ran 7 5 with hh'|hh' <;> linarith
  have h56 : b 5 6 = 0 := by
    rw [hn₁, hn₂, symm 6 5] at eq₃
    rcases ran 5 6 with hh|hh <;> rcases ran 4 7 with hh'|hh' <;> linarith
  have p₁ := E 0 5 1 4 (by intro i j; fin_cases i <;> fin_cases j <;> decide)
  have p₂ := E 0 6 2 4 (by intro i j; fin_cases i <;> fin_cases j <;> decide)
  have p₃ := E 1 6 2 5 (by intro i j; fin_cases i <;> fin_cases j <;> decide)
  rw [he₁, symm 5 4, hn₁, symm 5 1] at p₁
  rw [h02, symm 6 4, h46, symm 6 2] at p₂
  rw [h12, symm 6 5, h56, symm 6 2] at p₃
  rcases ran 0 4 with hh | hh <;> linarith

end Erdos636Proof

open Finset Filter SimpleGraph

namespace Erdos636Proof

noncomputable def directedEdges {V : Type*} [Fintype V] (G : SimpleGraph V) : Finset (V × V) :=
  open scoped Classical in Finset.univ.filter (fun p => G.Adj p.1 p.2)

lemma mem_directedEdges {V : Type*} [Fintype V] (G : SimpleGraph V) (p : V × V) :
    p ∈ directedEdges G ↔ G.Adj p.1 p.2 := by
  classical
  simp [directedEdges]

lemma directedEdges_card {V : Type*} [Fintype V] (G : SimpleGraph V) :
    (directedEdges G).card = 2 * Erdos88.FiniteES.edgeCount G := by
  classical
  rw [Erdos88.FiniteES.edgeCount, ← G.sum_degrees_eq_twice_card_edges]
  rw [Finset.card_eq_sum_card_fiberwise (t := (Finset.univ : Finset V))
    (f := Prod.fst) (by simp [Set.MapsTo])]
  apply Finset.sum_congr rfl
  intro x hx
  rw [← G.card_neighborFinset_eq_degree]
  let e : V ↪ V × V := ⟨fun y => (x,y), fun _ _ h => congrArg Prod.snd h⟩
  rw [← Finset.card_map e]
  congr 1
  ext p
  rcases p with ⟨a,b⟩
  simp only [Finset.mem_filter, mem_directedEdges, Finset.mem_map, G.mem_neighborFinset]
  change G.Adj a b ∧ a = x ↔ ∃ y, G.Adj x y ∧ (x,y) = (a,b)
  grind

noncomputable def eightPlacements {V : Type*} [Fintype V] (G : SimpleGraph V) :
    Finset (Fin 8 → V) := open scoped Classical in Finset.univ.filter (fun x =>
      (x 0, x 1) ∈ directedEdges G ∧ (x 2, x 3) ∈ directedEdges G ∧
      (x 4, x 5) ∈ directedEdges Gᶜ ∧ (x 6, x 7) ∈ directedEdges Gᶜ)

lemma eightPlacements_card {V : Type*} [Fintype V] (G : SimpleGraph V) :
    (eightPlacements G).card = (directedEdges G).card ^ 2 * (directedEdges Gᶜ).card ^ 2 := by
  classical
  let E := ↥(directedEdges G : Set (V × V))
  let F := ↥(directedEdges Gᶜ : Set (V × V))
  let f : ((E × E) × (F × F)) ≃ ↥(eightPlacements G : Set (Fin 8 → V)) := {
    toFun := fun ⟨⟨a,b⟩,⟨c,d⟩⟩ => ⟨![a.val.1,a.val.2,b.val.1,b.val.2,c.val.1,c.val.2,d.val.1,d.val.2],
      by simpa [eightPlacements] using And.intro a.property (And.intro b.property (And.intro c.property d.property))⟩
    invFun := fun x => by
      have hx : (x.val 0, x.val 1) ∈ directedEdges G ∧ (x.val 2, x.val 3) ∈ directedEdges G ∧
          (x.val 4, x.val 5) ∈ directedEdges Gᶜ ∧ (x.val 6, x.val 7) ∈ directedEdges Gᶜ := by
        simpa [eightPlacements] using x.property
      exact ⟨⟨⟨_, hx.1⟩,⟨_, hx.2.1⟩⟩,⟨⟨_, hx.2.2.1⟩,⟨_, hx.2.2.2⟩⟩⟩
    left_inv := by
      rintro ⟨⟨a,b⟩,⟨c,d⟩⟩
      rfl
    right_inv := by
      intro x
      apply Subtype.ext
      funext i
      fin_cases i <;> rfl }
  simpa [E, F, pow_two] using (Fintype.card_congr f).symm

noncomputable def goodRectangles {V : Type*} [Fintype V] (G : SimpleGraph V) : Finset (Fin 4 → V) :=
  open scoped Classical in Finset.univ.filter (fun x => rectangle G x ≠ 0)

noncomputable def restrictedTuples {V : Type*} [Fintype V] (F : Finset (Fin 4 → V))
    (e : Fin 4 ↪ Fin 8) : Finset (Fin 8 → V) :=
  open scoped Classical in Finset.univ.filter (fun x => x ∘ e ∈ F)

lemma restrictedTuple_card {V : Type*} [Fintype V] (F : Finset (Fin 4 → V))
    (e : Fin 4 ↪ Fin 8) :
    (restrictedTuples F e).card ≤ F.card * Fintype.card V ^ 4 := by
  classical
  let U := Set.range e
  let K := ↥(Uᶜ : Set (Fin 8))
  have hU : Fintype.card U = 4 := by
    simpa [U] using (Fintype.card_congr (Equiv.ofInjective e e.injective)).symm
  have hK : Fintype.card K = 4 := by
    change Fintype.card (Uᶜ : Set (Fin 8)) = _
    rw [Fintype.card_compl_set, hU, Fintype.card_fin]
  let M := restrictedTuples F e
  let f : ↥(M : Set (Fin 8 → V)) → ↥(F : Set (Fin 4 → V)) × (K → V) :=
    fun x => ⟨⟨x.val ∘ e, by simpa [M, restrictedTuples] using x.property⟩, fun i => x.val i⟩
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    funext i
    by_cases hi : i ∈ U
    · obtain ⟨j,rfl⟩ := hi
      exact congrFun (congrArg (fun z => z.1.val) hxy) j
    · exact congrFun (congrArg Prod.snd hxy) (⟨i,hi⟩ : K)
  simpa [M, hK] using Fintype.card_le_of_injective f hf

lemma enough_rectangles {n : ℕ} (G : SimpleGraph (Fin n)) {a : ℝ} (ha : 0 ≤ a)
    (he : a * (n : ℝ) ^ 2 ≤ Erdos88.FiniteES.edgeCount G)
    (hn : a * (n : ℝ) ^ 2 ≤ Erdos88.FiniteES.edgeCount Gᶜ) (hnpos : 0 < n) :
    (a ^ 4 / 1680) * (n : ℝ) ^ 4 ≤ (goodRectangles G).card := by
  classical
  let A := (Finset.univ : Finset (Fin 4 ↪ Fin 8)).biUnion (restrictedTuples (goodRectangles G))
  have hsub : eightPlacements G ⊆ A := by
    intro x hx
    have heach : (x 0, x 1) ∈ directedEdges G ∧ (x 2, x 3) ∈ directedEdges G ∧
        (x 4, x 5) ∈ directedEdges Gᶜ ∧ (x 6, x 7) ∈ directedEdges Gᶜ := by
      simpa [eightPlacements] using hx
    simp only [mem_directedEdges, SimpleGraph.compl_adj] at heach
    obtain ⟨e, he⟩ := rectangle_in_eight G x ⟨heach.1, heach.2.1⟩
      ⟨heach.2.2.1.2, heach.2.2.2.2⟩
    exact Finset.mem_biUnion.2 ⟨e, Finset.mem_univ _, by simp [restrictedTuples, goodRectangles, he]⟩
  have hup : (eightPlacements G).card ≤ 1680 * ((goodRectangles G).card * n ^ 4) := by
    calc _ ≤ A.card := Finset.card_le_card hsub
      _ ≤ ∑ e : Fin 4 ↪ Fin 8, (restrictedTuples (goodRectangles G) e).card := Finset.card_biUnion_le
      _ ≤ ∑ _e : Fin 4 ↪ Fin 8, (goodRectangles G).card * n ^ 4 := by
        apply Finset.sum_le_sum
        intro e _
        simpa only [Fintype.card_fin] using restrictedTuple_card (goodRectangles G) e
      _ = _ := by
        simp [Fintype.card_embedding_eq, Nat.descFactorial]
  have hlo : (a * (n : ℝ) ^ 2) ^ 2 * (a * (n : ℝ) ^ 2) ^ 2 ≤ (eightPlacements G).card := by
    rw [eightPlacements_card, Nat.cast_mul, Nat.cast_pow, Nat.cast_pow,
      directedEdges_card, directedEdges_card, Nat.cast_mul, Nat.cast_mul]
    norm_num only [Nat.cast_ofNat]
    have he' : a * (n : ℝ) ^ 2 ≤ (2 : ℝ) * Erdos88.FiniteES.edgeCount G := by
      nlinarith [Nat.cast_nonneg (α := ℝ) (Erdos88.FiniteES.edgeCount G)]
    have hn' : a * (n : ℝ) ^ 2 ≤ (2 : ℝ) * Erdos88.FiniteES.edgeCount Gᶜ := by
      nlinarith [Nat.cast_nonneg (α := ℝ) (Erdos88.FiniteES.edgeCount Gᶜ)]
    gcongr
  have hru : (eightPlacements G).card ≤ 1680 * ((goodRectangles G).card * (n : ℝ) ^ 4) := by
    exact_mod_cast hup
  have hpow : a ^ 4 * (n : ℝ) ^ 8 ≤ 1680 * ((goodRectangles G).card * (n : ℝ) ^ 4) := by
    calc a ^ 4 * (n : ℝ) ^ 8 = _ := by ring
      _ ≤ _ := hlo.trans hru
  have hh : (a ^ 4 * (n : ℝ) ^ 4) * (n : ℝ) ^ 4 ≤
      (1680 * (goodRectangles G).card) * (n : ℝ) ^ 4 := by
    convert hpow using 1 <;> ring
  have ht := (mul_le_mul_iff_of_pos_right (show 0 < (n : ℝ) ^ 4 by positivity)).mp hh
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 1680)).2
  convert ht using 1 <;> ring

end Erdos636Proof

open Finset Filter SimpleGraph

namespace Erdos636Proof

noncomputable def pairRectangle {V : Type*} (G : SimpleGraph V) (p q : V × V) : ℝ :=
  rectangle G ![p.1,p.2,q.1,q.2]

lemma pairRectangle_ne {V : Type*} (G : SimpleGraph V) (p q : V × V)
    (h : pairRectangle G p q ≠ 0) : p.1 ≠ p.2 ∧ q.1 ≠ q.2 := by
  refine ⟨fun he => h ?_, fun he => h ?_⟩ <;>
    change adjacencyBit G p.1 q.1 + adjacencyBit G p.2 q.2 -
      adjacencyBit G p.2 q.1 - adjacencyBit G p.1 q.2 = 0 <;>
    rw [he] <;> ring

lemma pairRectangle_sq {V : Type*} (G : SimpleGraph V) (p q : V × V)
    (h : pairRectangle G p q ≠ 0) : 1 ≤ pairRectangle G p q ^ 2 := rectangle_sq G _ h

lemma sum_goodRectangles {V : Type*} [Fintype V] (G : SimpleGraph V) :
    (goodRectangles G).card = ∑ p : V × V, (Finset.univ.filter (fun q => pairRectangle G p q ≠ 0)).card := by
  classical
  let e : (V × V) × (V × V) ≃ (Fin 4 → V) := {
    toFun := fun ⟨p,q⟩ => ![p.1,p.2,q.1,q.2]
    invFun := fun x => ((x 0,x 1),(x 2,x 3))
    left_inv := by rintro ⟨⟨a,b⟩,⟨c,d⟩⟩; rfl
    right_inv := by intro f; funext i; fin_cases i <;> rfl }
  rw [Finset.card_eq_sum_ones]
  simp only [goodRectangles, Finset.sum_filter]
  rw [← e.sum_comp, Fintype.sum_prod_type]
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
  rfl

open scoped Classical in
lemma sum_filter_high {α : Type*} (S : Finset α) (f : α → ℝ) (B t : ℝ)
    (hB : ∀ x ∈ S, f x ≤ B) (ht : 0 ≤ t) :
    ∑ x ∈ S, f x ≤ B * (S.filter (fun x => t ≤ f x)).card + t * S.card := by
  classical
  let F := S.filter (fun x => t ≤ f x)
  have hF : F ⊆ S := Finset.filter_subset _ _
  have hhigh : ∑ x ∈ F, f x ≤ B * F.card := by
    calc _ ≤ ∑ _x ∈ F, B := Finset.sum_le_sum fun x hx => hB x (hF hx)
      _ = _ := by simp [mul_comm]
  have hlow : ∑ x ∈ S \ F, f x ≤ t * S.card := by
    calc
      (∑ x ∈ S \ F, f x) ≤ ∑ _x ∈ S \ F, t := by
        apply Finset.sum_le_sum
        intro x hx
        obtain ⟨hs,hf⟩ := Finset.mem_sdiff.1 hx
        exact le_of_not_ge (fun h => hf (Finset.mem_filter.2 ⟨hs,h⟩))
      _ = t * (S \ F).card := by simp [mul_comm]
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (by exact_mod_cast (Finset.card_le_card (Finset.sdiff_subset : S \ F ⊆ S))) ht
  rw [← Finset.sum_sdiff hF]
  linarith

noncomputable def ends {V : Type*} (p : V × V) : Finset V :=
  open scoped Classical in {p.1,p.2}

lemma mem_ends {V : Type*} (p : V × V) (x : V) : x ∈ ends p ↔ x = p.1 ∨ x = p.2 := by
  classical
  simp [ends]

lemma ends_card_le {V : Type*} (p : V × V) : (ends p).card ≤ 2 := by
  classical
  unfold ends
  exact Finset.card_insert_le _ _ |>.trans (by simp)

noncomputable def usedVertices {V : Type*} (P : Finset (V × V)) : Finset V :=
  open scoped Classical in P.biUnion ends

lemma mem_usedVertices {V : Type*} {P : Finset (V × V)} {v : V} :
    v ∈ usedVertices P ↔ ∃ p ∈ P, v ∈ ends p := by
  classical
  exact Finset.mem_biUnion

lemma usedVertices_card_le {V : Type*} (P : Finset (V × V)) : (usedVertices P).card ≤ 2 * P.card := by
  classical
  calc _ ≤ ∑ p ∈ P, (ends p).card := Finset.card_biUnion_le
    _ ≤ ∑ _p ∈ P, 2 := Finset.sum_le_sum fun p _ => ends_card_le p
    _ = _ := by simp [mul_comm]

open scoped Classical in
lemma incident_card_le {V : Type*} [Fintype V] (P : Finset (V × V)) (U : Finset V) :
    (P.filter fun p => p.1 ∈ U ∨ p.2 ∈ U).card ≤ 2 * U.card * Fintype.card V := by
  classical
  let A := U ×ˢ (Finset.univ : Finset V)
  let B := (Finset.univ : Finset V) ×ˢ U
  calc _ ≤ (A ∪ B).card := by
        apply Finset.card_le_card
        intro p hp
        simpa [A,B] using (Finset.mem_filter.1 hp).2
    _ ≤ A.card + B.card := Finset.card_union_le _ _
    _ = _ := by simp [A,B]; ring

lemma exists_disjoint_pairs {V : Type*} [Fintype V] [Nonempty V] (m : ℕ)
    (P : Finset (V × V)) (hP : m * (4 * Fintype.card V) ≤ P.card) :
    ∃ L ⊆ P, L.card = m ∧ (L : Set (V × V)).Pairwise (fun p q => Disjoint (ends p) (ends q)) := by
  classical
  induction m generalizing P with
  | zero => exact ⟨∅, Finset.empty_subset _, by simp, by simp⟩
  | succ m ih =>
    let n := Fintype.card V
    have hn : 0 < n := Fintype.card_pos
    obtain ⟨p,hp⟩ := Finset.card_pos.1 ((Nat.mul_pos (by omega) (by omega : 0 < 4 * n)).trans_le hP)
    let H := P.filter fun q => q.1 ∈ ends p ∨ q.2 ∈ ends p
    let T := P \ H
    have hH : H.card ≤ 4 * n := by
      refine (incident_card_le P (ends p)).trans ?_
      have hc := ends_card_le p
      gcongr <;> omega
    have hT : T.card + H.card = P.card := Finset.card_sdiff_add_card_eq_card (Finset.filter_subset _ _)
    have hsmall : m * (4 * n) ≤ T.card := by
      change (m + 1) * (4*n) ≤ P.card at hP
      rw [Nat.add_mul, one_mul] at hP
      omega
    obtain ⟨L,hL,hc,hd⟩ := ih T hsmall
    have havoid (q : V × V) (hq : q ∈ L) : Disjoint (ends p) (ends q) := by
      have hqT := Finset.mem_sdiff.1 (hL hq)
      refine Finset.disjoint_left.2 ?_
      intro v hv hv'
      rcases (mem_ends q v).1 hv' with rfl | rfl
      · exact hqT.2 (Finset.mem_filter.2 ⟨hqT.1,Or.inl hv⟩)
      · exact hqT.2 (Finset.mem_filter.2 ⟨hqT.1,Or.inr hv⟩)
    have hnot : p ∉ L := fun h => (Finset.disjoint_left.1 (havoid p h))
      ((mem_ends p p.1).2 (Or.inl rfl)) ((mem_ends p p.1).2 (Or.inl rfl))
    refine ⟨insert p L, Finset.insert_subset hp (hL.trans Finset.sdiff_subset),
      by rw [Finset.card_insert_of_notMem hnot,hc], ?_⟩
    intro u hu v hv huv
    have hu' : u ∈ insert p L := hu
    have hv' : v ∈ insert p L := hv
    rcases Finset.mem_insert.1 hu' with rfl | huL
    · exact havoid v ((Finset.mem_insert.1 hv').resolve_left (Ne.symm huv))
    rcases Finset.mem_insert.1 hv' with rfl | hvL
    · exact (havoid u huL).symm
    · exact hd huL hvL huv

open scoped Classical in
lemma exists_rectangle_pairings {n : ℕ} (hn : 0 < n) (G : SimpleGraph (Fin n))
    {δ : ℝ} (hδ : 0 < δ) (hδ₁ : δ ≤ 1) {m : ℕ} (hm : 0 < m)
    (hm₁ : (m : ℝ) ≤ δ * n / 32)
    (hrect : δ * (n : ℝ) ^ 4 ≤ (goodRectangles G).card) :
    ∃ L R : Finset (Fin n × Fin n), L.card = m ∧ R.card = m ∧
      (∀ p ∈ L, p.1 ≠ p.2) ∧ (∀ q ∈ R, q.1 ≠ q.2) ∧
      (L : Set (Fin n × Fin n)).Pairwise (fun p q => Disjoint (ends p) (ends q)) ∧
      (R : Set (Fin n × Fin n)).Pairwise (fun p q => Disjoint (ends p) (ends q)) ∧
      (∀ q ∈ R, Disjoint (usedVertices L) (ends q)) ∧
      (∀ q ∈ R, δ / 8 * m ≤ (L.filter (fun p => pairRectangle G p q ≠ 0)).card) := by
  classical
  letI : Nonempty (Fin n) := ⟨⟨0,hn⟩⟩
  let P : Finset (Fin n × Fin n) := Finset.univ
  have hP : P.card = n ^ 2 := by simp [P, pow_two]
  let d (p : Fin n × Fin n) := (P.filter fun q => pairRectangle G p q ≠ 0).card
  let D := P.filter (fun p => δ / 2 * (n : ℝ)^2 ≤ (d p : ℝ))
  have hcount : (goodRectangles G).card = ∑ p ∈ P, d p := sum_goodRectangles G
  have hd : δ / 2 * (n : ℝ)^2 ≤ D.card := by
    have htot := sum_filter_high P (fun p => (d p : ℝ)) ((n : ℝ)^2) (δ / 2 * (n : ℝ)^2)
      (fun p hp => by exact_mod_cast (show d p ≤ n^2 from (Finset.card_filter_le _ _).trans hP.le))
      (by positivity)
    have hs : (∑ p ∈ P, (d p : ℝ)) = (goodRectangles G).card := by exact_mod_cast hcount.symm
    rw [hs, hP, Nat.cast_pow] at htot
    change _ ≤ (n : ℝ)^2 * D.card + _ at htot
    apply (mul_le_mul_iff_of_pos_right (show 0 < (n : ℝ)^2 by positivity)).mp
    nlinarith
  have hmD : m * (4 * Fintype.card (Fin n)) ≤ D.card := by
    simp only [Fintype.card_fin]
    have hp : (m : ℝ) * (4 * n) ≤ D.card := by
      nlinarith [mul_le_mul_of_nonneg_right hm₁ (show 0 ≤ (n : ℝ) by positivity)]
    exact_mod_cast hp
  obtain ⟨L,hL,hLm,hLd⟩ := exists_disjoint_pairs m D hmD
  have hLne (p : Fin n × Fin n) (hp : p ∈ L) : p.1 ≠ p.2 := by
    have hp' := (Finset.mem_filter.1 (hL hp)).2
    have hpos : 0 < (d p : ℝ) := lt_of_lt_of_le (by positivity) hp'
    have hpNat : 0 < d p := by exact_mod_cast hpos
    obtain ⟨q,hq⟩ := Finset.card_pos.1 hpNat
    exact (pairRectangle_ne G p q (Finset.mem_filter.1 hq).2).1
  let U := usedVertices L
  let Q := P.filter (fun q => ¬ (q.1 ∈ U ∨ q.2 ∈ U))
  have hQ : Q ⊆ P := Finset.filter_subset _ _
  have hU : U.card ≤ 2*m := (usedVertices_card_le L).trans (by rw [hLm])
  have hbad : (P \ Q).card ≤ 4*m*n := by
    have hz : P \ Q = P.filter (fun q => q.1 ∈ U ∨ q.2 ∈ U) := by
      ext q
      simp only [Finset.mem_sdiff, Q, Finset.mem_filter]
      tauto
    rw [hz]
    have h := incident_card_le P U
    simp only [Fintype.card_fin] at h
    have h' : (P.filter fun q => q.1 ∈ U ∨ q.2 ∈ U).card ≤ 2 * U.card * n := by
      convert h using 1
      congr 1
      apply Finset.ext
      intro q
      simp only [Finset.mem_filter]
    refine h'.trans ?_
    calc 2 * U.card * n ≤ 2 * (2*m) * n := by gcongr
      _ = _ := by ring
  have hdegree (p : Fin n × Fin n) (hp : p ∈ L) :
      δ / 4 * (n : ℝ)^2 ≤ (Q.filter (fun q => pairRectangle G p q ≠ 0)).card := by
    have hp' := (Finset.mem_filter.1 (hL hp)).2
    have hdecomp : (Q.filter (fun q => pairRectangle G p q ≠ 0)).card + (P \ Q).card ≥ d p := by
      let F := P.filter (fun q => pairRectangle G p q ≠ 0)
      let FQ := Q.filter (fun q => pairRectangle G p q ≠ 0)
      have hsub : F ⊆ FQ ∪ (P \ Q) := by
        intro q hq
        by_cases h : q ∈ Q
        · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨h,(Finset.mem_filter.1 hq).2⟩)
        · exact Finset.mem_union_right _ (Finset.mem_sdiff.2 ⟨(Finset.mem_filter.1 hq).1,h⟩)
      exact (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    have hRC : (d p : ℝ) ≤ (Q.filter (fun q => pairRectangle G p q ≠ 0)).card + (P \ Q).card := by
      exact_mod_cast hdecomp
    have hBC : ((P \ Q).card : ℝ) ≤ 4 * m * n := by exact_mod_cast hbad
    nlinarith [mul_le_mul_of_nonneg_right hm₁ (show 0 ≤ (n : ℝ) by positivity)]
  let dr (q : Fin n × Fin n) := (L.filter (fun p => pairRectangle G p q ≠ 0)).card
  let T := Q.filter (fun q => δ / 8 * m ≤ (dr q : ℝ))
  have hsum : ∑ p ∈ L, ((Q.filter (fun q => pairRectangle G p q ≠ 0)).card : ℝ) =
      ∑ q ∈ Q, (dr q : ℝ) := by
    simp only [dr, Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one, Finset.sum_filter]
    rw [Finset.sum_comm]
  have hTl : δ / 8 * (n : ℝ)^2 ≤ T.card := by
    have hab := Finset.sum_le_sum (fun p hp => hdegree p hp)
    rw [hsum, Finset.sum_const, nsmul_eq_mul, hLm] at hab
    have hhi := sum_filter_high Q (fun q => (dr q : ℝ)) (m : ℝ) (δ / 8 * m)
      (fun q _ => by exact_mod_cast ((Finset.card_filter_le _ _).trans hLm.le)) (by positivity)
    change _ ≤ (m : ℝ) * T.card + (δ / 8 * m) * Q.card at hhi
    have hQc : (Q.card : ℝ) ≤ (n : ℝ)^2 := by exact_mod_cast ((Finset.card_le_card hQ).trans hP.le)
    apply (mul_le_mul_iff_of_pos_left (show 0 < (m : ℝ) by positivity)).mp
    nlinarith [mul_le_mul_of_nonneg_left hQc (show 0 ≤ (δ / 8 * m : ℝ) by positivity)]
  have hmT : m * (4 * Fintype.card (Fin n)) ≤ T.card := by
    simp only [Fintype.card_fin]
    have hp : (m : ℝ) * (4 * n) ≤ T.card := by
      nlinarith [mul_le_mul_of_nonneg_right hm₁ (show 0 ≤ (n : ℝ) by positivity)]
    exact_mod_cast hp
  obtain ⟨R,hR,hRm,hRd⟩ := exists_disjoint_pairs m T hmT
  have hRlow (q : Fin n × Fin n) (hq : q ∈ R) : δ / 8 * m ≤ (dr q : ℝ) :=
    (Finset.mem_filter.1 (hR hq)).2
  refine ⟨L,R,hLm,hRm,hLne,?_,hLd,hRd,?_,hRlow⟩
  · intro q hq
    have hpos : 0 < (dr q : ℝ) := lt_of_lt_of_le (by positivity) (hRlow q hq)
    have hpNat : 0 < dr q := by exact_mod_cast hpos
    obtain ⟨p,hp⟩ := Finset.card_pos.1 hpNat
    exact (pairRectangle_ne G p q (Finset.mem_filter.1 hp).2).2
  · intro q hq
    have hqQ := (Finset.mem_filter.1 (hR hq)).1
    have hh := (Finset.mem_filter.1 hqQ).2
    apply Finset.disjoint_left.2
    intro v hv hv'
    rcases (mem_ends q v).1 hv' with rfl | rfl
    · exact hh (Or.inl hv)
    · exact hh (Or.inr hv)

end Erdos636Proof

open Finset Filter SimpleGraph

namespace Erdos636Proof

lemma exists_sign_contrast {m : ℕ} (b : Fin m → Fin m → ℝ) {v : ℝ}
    (hv : ∀ j, v ≤ ∑ i, (b i j) ^ 2) :
    ∃ x y : Fin m → Bool, (m : ℝ) * (Real.sqrt v / 5) ≤
      ∑ j, signSum (fun i => b i j) x * signValue (y j) := by
  classical
  let f (x : Fin m → Bool) := ∑ j, |signSum (fun i => b i j) x|
  have hmean : signMean f = ∑ j, signMean (fun x => |signSum (fun i => b i j) x|) := by
    unfold f signMean
    rw [← Finset.sum_div, Finset.sum_comm]
  have hbound : (m : ℝ) * (Real.sqrt v / 5) ≤ signMean f := by
    rw [hmean]
    calc (m : ℝ) * (Real.sqrt v / 5) = ∑ _j : Fin m, Real.sqrt v / 5 := by simp
      _ ≤ _ := Finset.sum_le_sum fun j _ => (div_le_div_of_nonneg_right
        (Real.sqrt_le_sqrt (hv j)) (by norm_num)).trans (signMean_abs (fun i => b i j))
  have hsum : ∑ _x : Fin m → Bool, signMean f ≤ ∑ x : Fin m → Bool, f x := by
    simp [signMean, Nat.cast_pow]
    rw [← mul_div_assoc, mul_div_cancel_left₀ _ (by positivity)]
  obtain ⟨x,_,hx⟩ := Finset.exists_le_of_sum_le Finset.univ_nonempty hsum
  refine ⟨x, fun j => decide (0 ≤ signSum (fun i => b i j) x), hbound.trans (hx.trans_eq ?_)⟩
  unfold f
  apply Finset.sum_congr rfl
  intro j hj
  by_cases h : 0 ≤ signSum (fun i => b i j) x
  · simp [signValue, h, abs_of_nonneg h]
  · simp [signValue, h, abs_of_neg (lt_of_not_ge h)]

def pickVertex {V : Type*} (p : V × V) (s : Bool) : V := if s then p.1 else p.2

lemma pickVertex_mem {V : Type*} (p : V × V) (b : Bool) : pickVertex p b ∈ ends p := by
  cases b <;> simp [pickVertex, mem_ends]

noncomputable def picked {V : Type*} {m : ℕ} (p : Fin m → V × V) (s : Fin m → Bool) : Finset V :=
  open scoped Classical in Finset.univ.image (fun i => pickVertex (p i) (s i))

lemma pickVertex_inj {V : Type*} {m : ℕ} {p : Fin m → V × V}
    (hp : ∀ i j, i ≠ j → Disjoint (ends (p i)) (ends (p j))) (s : Fin m → Bool) :
    Function.Injective (fun i => pickVertex (p i) (s i)) := by
  intro i j h
  dsimp only at h
  by_contra hne
  apply (Finset.disjoint_left.1 (hp i j hne)) (pickVertex_mem (p i) (s i))
  rw [h]
  exact pickVertex_mem (p j) (s j)

lemma picked_card {V : Type*} {m : ℕ} {p : Fin m → V × V}
    (hp : ∀ i j, i ≠ j → Disjoint (ends (p i)) (ends (p j))) (s : Fin m → Bool) :
    (picked p s).card = m := by
  classical
  rw [picked, Finset.card_image_of_injective _ (pickVertex_inj hp s)]
  simp

lemma sum_picked {V : Type*} {m : ℕ} {p : Fin m → V × V}
    (hp : ∀ i j, i ≠ j → Disjoint (ends (p i)) (ends (p j))) (s : Fin m → Bool) (f : V → ℝ) :
    ∑ x ∈ picked p s, f x = ∑ i, f (pickVertex (p i) (s i)) := by
  classical
  unfold picked
  exact Finset.sum_image (pickVertex_inj hp s).injOn

noncomputable def cross {V : Type*} (G : SimpleGraph V) (A B : Finset V) : ℝ :=
  ∑ x ∈ A, ∑ y ∈ B, adjacencyBit G x y

lemma cross_symm {V : Type*} (G : SimpleGraph V) (A B : Finset V) :
    cross G A B = cross G B A := by
  unfold cross
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => adjacencyBit_symm _ _ _

lemma cross_union_left {V : Type*} [DecidableEq V] (G : SimpleGraph V) {A B : Finset V}
    (h : Disjoint A B) (F : Finset V) : cross G (A ∪ B) F = cross G A F + cross G B F := by
  exact Finset.sum_union h

lemma cross_union_right {V : Type*} [DecidableEq V] (G : SimpleGraph V) (F : Finset V)
    {A B : Finset V} (h : Disjoint A B) : cross G F (A ∪ B) = cross G F A + cross G F B := by
  rw [cross_symm G F (A ∪ B), cross_union_left G h, cross_symm G A F, cross_symm G B F]

noncomputable def edgeProfile {V : Type*} (G : SimpleGraph V) (A : Finset V) : ℕ :=
  (G.induce (A : Set V)).edgeSet.ncard

lemma cross_self {V : Type*} [Fintype V] (G : SimpleGraph V) (A : Finset V) :
    cross G A A = 2 * edgeProfile G A := by
  classical
  let H : SimpleGraph ↥A := G.induce (A : Set V)
  have hsum : (∑ x ∈ A, ∑ y ∈ A, adjacencyBit G x y) =
      ∑ x : ↥A, ∑ y : ↥A, adjacencyBit G x y := by
    rw [Finset.univ_eq_attach A, ← Finset.sum_attach A (fun x => ∑ y ∈ A, adjacencyBit G x y)]
    apply Finset.sum_congr rfl
    intro x _
    exact (Finset.sum_attach A (fun y => adjacencyBit G x y)).symm
  have hvertex (x : ↥A) :
      (∑ y : ↥A, adjacencyBit G x y) = H.degree x := by
    rw [← H.card_neighborFinset_eq_degree, Finset.card_eq_sum_ones, Nat.cast_sum]
    have hnb : H.neighborFinset x = Finset.univ.filter (fun y => H.Adj x y) := by
      ext y
      simp
    rw [hnb, Finset.sum_filter]
    simp [adjacencyBit, H]
  change (∑ x ∈ A, ∑ y ∈ A, adjacencyBit G x y) = _
  rw [hsum]
  simp_rw [hvertex]
  rw [← Nat.cast_sum, H.sum_degrees_eq_twice_card_edges, Nat.cast_mul, Nat.cast_ofNat]
  congr 1
  exact_mod_cast (H.edgeFinset_card.trans Nat.card_eq_fintype_card.symm :
    H.edgeFinset.card = H.edgeSet.ncard)

lemma cross_self_union {V : Type*} [DecidableEq V] (G : SimpleGraph V) {A B : Finset V}
    (h : Disjoint A B) : cross G (A ∪ B) (A ∪ B) =
      cross G A A + cross G B B + 2 * cross G A B := by
  rw [cross_union_left G h, cross_union_right G A h, cross_union_right G B h, cross_symm G B A]
  ring

lemma rectangle_choosing {V : Type*} (G : SimpleGraph V) (p q : V × V) (s t : Bool) :
    adjacencyBit G (pickVertex p s) (pickVertex q t) +
      adjacencyBit G (pickVertex p (!s)) (pickVertex q (!t)) -
      adjacencyBit G (pickVertex p (!s)) (pickVertex q t) -
      adjacencyBit G (pickVertex p s) (pickVertex q (!t)) =
    pairRectangle G p q * signValue s * signValue t := by
  cases s <;> cases t <;> simp [signValue, pickVertex, pairRectangle, rectangle] <;> ring

lemma picked_subset_used {V : Type*} {m : ℕ} {P : Finset (V × V)}
    {p : Fin m → V × V} (h : ∀ i, p i ∈ P) (s : Fin m → Bool) :
    picked p s ⊆ usedVertices P := by
  classical
  intro v hv
  obtain ⟨i,_,rfl⟩ := Finset.mem_image.1 hv
  exact mem_usedVertices.2 ⟨p i, h i, pickVertex_mem _ _⟩

lemma cross_contrast {V : Type*} {m : ℕ} (G : SimpleGraph V)
    {p q : Fin m → V × V} (hp : ∀ i j, i ≠ j → Disjoint (ends (p i)) (ends (p j)))
    (hq : ∀ i j, i ≠ j → Disjoint (ends (q i)) (ends (q j)))
    (x y : Fin m → Bool) :
    let A := picked p x
    let A' := picked p (fun i => !(x i))
    let B := picked q y
    let B' := picked q (fun i => !(y i))
    cross G A B + cross G A' B' - cross G A' B - cross G A B' =
      ∑ j, signSum (fun i => pairRectangle G (p i) (q j)) x * signValue (y j) := by
  dsimp only
  unfold cross
  simp_rw [sum_picked hp, sum_picked hq]
  rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  have h : (∑ i, ((∑ j, adjacencyBit G (pickVertex (p i) (x i)) (pickVertex (q j) (y j))) +
      (∑ j, adjacencyBit G (pickVertex (p i) (!(x i))) (pickVertex (q j) (!(y j)))) -
      (∑ j, adjacencyBit G (pickVertex (p i) (!(x i))) (pickVertex (q j) (y j))) -
      (∑ j, adjacencyBit G (pickVertex (p i) (x i)) (pickVertex (q j) (!(y j)))))) =
    ∑ i, ∑ j, (pairRectangle G (p i) (q j) * signValue (x i) * signValue (y j)) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun j _ => rectangle_choosing G (p i) (q j) (x i) (y j))
  rw [h, Finset.sum_comm]
  simp [signSum, Finset.sum_mul]

lemma profile_contrast {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    {A A' B B' F : Finset V} (ha : Disjoint A B) (ha' : Disjoint A' B')
    (hb : Disjoint A' B) (hb' : Disjoint A B')
    (hfA : Disjoint A F) (hfA' : Disjoint A' F) (hfB : Disjoint B F) (hfB' : Disjoint B' F) :
    (edgeProfile G (A ∪ B ∪ F) : ℝ) + edgeProfile G (A' ∪ B' ∪ F) -
      edgeProfile G (A' ∪ B ∪ F) - edgeProfile G (A ∪ B' ∪ F) =
      cross G A B + cross G A' B' - cross G A' B - cross G A B' := by
  have h (D E : Finset V) (hDE : Disjoint D E) (hDF : Disjoint D F) (hEF : Disjoint E F) :
      2 * (edgeProfile G (D ∪ E ∪ F) : ℝ) = (cross G D D + cross G E E + 2 * cross G D E) +
        cross G F F + 2 * (cross G D F + cross G E F) := by
    rw [← cross_self, cross_self_union G (Finset.disjoint_union_left.2 ⟨hDF,hEF⟩),
      cross_self_union G hDE, cross_union_left G hDE]
  linarith [h A B ha hfA hfB, h A' B' ha' hfA' hfB', h A' B hb hfA' hfB, h A B' hb' hfA hfB']

end Erdos636Proof

open Finset Filter SimpleGraph

namespace Erdos636Proof

open scoped Classical in
lemma discrepancy_from_pairings {n m : ℕ} (G : SimpleGraph (Fin n)) (L R : Finset (Fin n × Fin n))
    (hL : L.card = m) (hR : R.card = m)
    (hLd : (L : Set (Fin n × Fin n)).Pairwise (fun p q => Disjoint (ends p) (ends q)))
    (hRd : (R : Set (Fin n × Fin n)).Pairwise (fun p q => Disjoint (ends p) (ends q)))
    (hLR : ∀ q ∈ R, Disjoint (usedVertices L) (ends q))
    {v : ℝ} (hvar : ∀ q ∈ R, v ≤ (L.filter (fun p => pairRectangle G p q ≠ 0)).card) :
    ∀ k : ℕ, 2*m ≤ k → k + 2*m ≤ n → ∃ A B : Finset (Fin n),
      A.card = k ∧ B.card = k ∧ (m : ℝ) * (Real.sqrt v / 10) ≤
        (edgeProfile G B : ℝ) - edgeProfile G A := by
  classical
  let eL : Fin m ≃ ↥L := (Fintype.equivFinOfCardEq (by simpa using hL)).symm
  let eR : Fin m ≃ ↥R := (Fintype.equivFinOfCardEq (by simpa using hR)).symm
  let p (i : Fin m) := (eL i).val
  let q (j : Fin m) := (eR j).val
  have hpMem (i : Fin m) : p i ∈ L := (eL i).property
  have hqMem (i : Fin m) : q i ∈ R := (eR i).property
  have hp (i j : Fin m) (h : i ≠ j) : Disjoint (ends (p i)) (ends (p j)) :=
    hLd (hpMem i) (hpMem j) (fun he => h (eL.injective (Subtype.ext he)))
  have hq (i j : Fin m) (h : i ≠ j) : Disjoint (ends (q i)) (ends (q j)) :=
    hRd (hqMem i) (hqMem j) (fun he => h (eR.injective (Subtype.ext he)))
  have hUD : Disjoint (usedVertices L) (usedVertices R) := by
    apply Finset.disjoint_left.2
    intro z hLz hRz
    obtain ⟨r,hr,hrz⟩ := mem_usedVertices.1 hRz
    exact (Finset.disjoint_left.1 (hLR r hr)) hLz hrz
  have hv (j : Fin m) : v ≤ ∑ i, pairRectangle G (p i) (q j) ^ 2 := by
    have hsum : ∑ i, pairRectangle G (p i) (q j) ^ 2 =
        ∑ a ∈ L, pairRectangle G a (q j) ^ 2 := by
      calc
        _ = ∑ a : ↥L, pairRectangle G a.val (q j) ^ 2 :=
          eL.sum_comp (fun a : ↥L => pairRectangle G a.val (q j) ^ 2)
        _ = _ := by
          rw [Finset.univ_eq_attach L]
          exact Finset.sum_attach L (fun a => pairRectangle G a (q j) ^ 2)
    rw [hsum]
    refine (hvar (q j) (hqMem j)).trans ?_
    rw [Finset.card_eq_sum_ones, Nat.cast_sum]
    simp only [Nat.cast_one]
    refine (Finset.sum_le_sum fun a ha => pairRectangle_sq G a (q j) (Finset.mem_filter.1 ha).2).trans ?_
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun a _ _ => sq_nonneg _)
  obtain ⟨x,y,hxy⟩ := exists_sign_contrast (fun i j => pairRectangle G (p i) (q j)) hv
  intro k hk₁ hk₂
  let Used := usedVertices L ∪ usedVertices R
  have hUsed : Used.card ≤ 4*m := by
    have h₁ := usedVertices_card_le L
    have h₂ := usedVertices_card_le R
    rw [hL] at h₁; rw [hR] at h₂
    exact (Finset.card_union_le _ _).trans (by omega)
  have hroom : k - 2*m ≤ (Finset.univ \ Used).card := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨F, hF, hFcard⟩ := Finset.exists_subset_card_eq hroom
  have hdis (x' y' : Fin m → Bool) : Disjoint (picked p x') (picked q y') :=
    hUD.mono (picked_subset_used hpMem x') (picked_subset_used hqMem y')
  have hfL (x' : Fin m → Bool) : Disjoint (picked p x') F := by
    apply Finset.disjoint_left.2
    intro z hz hzF
    exact (Finset.mem_sdiff.1 (hF hzF)).2 (Finset.mem_union_left _ (picked_subset_used hpMem x' hz))
  have hfR (y' : Fin m → Bool) : Disjoint (picked q y') F := by
    apply Finset.disjoint_left.2
    intro z hz hzF
    exact (Finset.mem_sdiff.1 (hF hzF)).2 (Finset.mem_union_right _ (picked_subset_used hqMem y' hz))
  let X (x' y' : Fin m → Bool) := picked p x' ∪ picked q y' ∪ F
  have hcard (x' y' : Fin m → Bool) : (X x' y').card = k := by
    change (picked p x' ∪ picked q y' ∪ F).card = k
    rw [Finset.card_union_of_disjoint (Finset.disjoint_union_left.2 ⟨hfL x',hfR y'⟩),
      Finset.card_union_of_disjoint (hdis x' y'), picked_card hp, picked_card hq, hFcard]
    omega
  let x' := fun i => !(x i)
  let y' := fun i => !(y i)
  have hcontrast := profile_contrast G (hdis x y) (hdis x' y') (hdis x' y) (hdis x y')
    (hfL x) (hfL x') (hfR y) (hfR y')
  rw [cross_contrast G hp hq x y] at hcontrast
  change (edgeProfile G (X x y) : ℝ) + edgeProfile G (X x' y') - edgeProfile G (X x' y) -
      edgeProfile G (X x y') = _ at hcontrast
  by_cases h : (m : ℝ) * (Real.sqrt v / 10) ≤ (edgeProfile G (X x y) : ℝ) - edgeProfile G (X x' y)
  · exact ⟨X x' y, X x y, hcard _ _, hcard _ _, h⟩
  · exact ⟨X x y', X x' y', hcard _ _, hcard _ _, by linarith⟩

lemma edgeProfile_insert {n : ℕ} (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) {x : Fin n}
    (hx : x ∉ A) : edgeProfile G A ≤ edgeProfile G (insert x A) ∧
      edgeProfile G (insert x A) ≤ edgeProfile G A + n := by
  classical
  have hd : Disjoint A {x} := by simp [hx]
  have hsum := cross_self_union G hd
  rw [cross_self, cross_self, cross_self] at hsum
  have he : edgeProfile G {x} = 0 := by
    have hcross : cross G {x} {x} = 0 := by simp [cross, adjacencyBit]
    rw [cross_self] at hcross
    exact_mod_cast (show (edgeProfile G {x} : ℝ) = 0 by linarith)
  have hnon : 0 ≤ cross G A {x} := by
    simp only [cross, Finset.sum_singleton]
    apply Finset.sum_nonneg
    intro y hy
    rcases adjacencyBit_range G y x with h|h <;> simp [h]
  have hle : cross G A {x} ≤ n := by
    simp only [cross, Finset.sum_singleton]
    calc _ ≤ ∑ _y ∈ A, (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro y hy
          rcases adjacencyBit_range G y x with h|h <;> simp [h]
      _ = A.card := by simp
      _ ≤ n := by
        have h := Finset.card_le_univ A
        rw [Fintype.card_fin] at h
        exact_mod_cast h
  have heq : A ∪ {x} = insert x A := by ext y; simp [or_comm]
  rw [heq, he, Nat.cast_zero] at hsum
  constructor
  · exact_mod_cast (show (edgeProfile G A : ℝ) ≤ (edgeProfile G (insert x A) : ℝ) by linarith)
  · exact_mod_cast (show (edgeProfile G (insert x A) : ℝ) ≤ (edgeProfile G A : ℝ) + n by linarith)

lemma intermediate_profile {n : ℕ} (G : SimpleGraph (Fin n)) (A B : Finset (Fin n))
    (hcard : A.card = B.card) (T : ℕ) (hA : edgeProfile G A ≤ T) (hB : T ≤ edgeProfile G B) :
    ∃ S : Finset (Fin n), S.card = A.card ∧ T ≤ edgeProfile G S ∧ edgeProfile G S ≤ T+n := by
  classical
  have aux : ∀ k : ℕ, ∀ A : Finset (Fin n), (A \ B).card = k → A.card = B.card →
      edgeProfile G A ≤ T →
      ∃ S : Finset (Fin n), S.card = B.card ∧ T ≤ edgeProfile G S ∧ edgeProfile G S ≤ T+n := by
    intro k
    induction k with
    | zero =>
      intro A hk hc _
      have hab : A ⊆ B := Finset.sdiff_eq_empty_iff_subset.mp (Finset.card_eq_zero.1 hk)
      have hAB := Finset.eq_of_subset_of_card_le hab hc.ge
      subst A
      exact ⟨B, rfl, hB, by omega⟩
    | succ k ih =>
      intro A pk pc hAl
      obtain ⟨a,ha⟩ : (A \ B).Nonempty := Finset.card_pos.1 (by omega)
      have ha' := Finset.mem_sdiff.1 ha
      have hBneq : ¬ B ⊆ A := by
        intro hsub
        have hBA := Finset.eq_of_subset_of_card_le hsub pc.le
        apply ha'.2
        rw [hBA]
        exact ha'.1
      obtain ⟨b,hba⟩ : (B \ A).Nonempty := Finset.nonempty_iff_ne_empty.2
        (fun h => hBneq (Finset.sdiff_eq_empty_iff_subset.1 h))
      obtain ⟨hb,hn⟩ := Finset.mem_sdiff.1 hba
      let U := A.erase a
      let A' := insert b U
      have hnU : b ∉ U := fun h => hn (Finset.mem_of_mem_erase h)
      have haU : a ∉ U := Finset.notMem_erase _ _
      have hUad : insert a U = A := Finset.insert_erase ha'.1
      have hUc : U.card + 1 = A.card := by rw [← hUad, Finset.card_insert_of_notMem haU]
      have hA'c : A'.card = B.card := by
        change (insert b U).card = B.card
        rw [Finset.card_insert_of_notMem hnU, hUc, pc]
      have hk : (A' \ B).card = k := by
        have heq : A' \ B = (A \ B).erase a := by
          apply Finset.ext
          intro z
          change z ∈ insert b (A.erase a) \ B ↔ z ∈ (A \ B).erase a
          simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_erase]
          by_cases hz : z = b
          · subst z
            simp [hb]
          · simp only [hz, false_or]
            tauto
        rw [heq]
        have h := Finset.card_erase_add_one ha
        omega
      have hUlow := (edgeProfile_insert G U haU).1
      rw [hUad] at hUlow
      have hhigh := (edgeProfile_insert G U hnU).2
      by_cases h : T ≤ edgeProfile G A'
      · exact ⟨A', hA'c, h, by change edgeProfile G A' ≤ T+n; change edgeProfile G A' ≤ _ at hhigh; omega⟩
      · exact ih A' hk hA'c (by omega)
  obtain ⟨S,hS,hSL,hSU⟩ := aux _ A rfl hcard hA
  exact ⟨S,hS.trans hcard.symm,hSL,hSU⟩

end Erdos636Proof

open Finset Filter SimpleGraph

namespace Erdos636Proof

lemma floor_half (x : ℝ) (hx : 2 ≤ x) : x / 2 ≤ (⌊x⌋₊ : ℝ) := by
  have h := Nat.lt_floor_add_one x
  linarith

lemma distinct_profiles {n m t : ℕ} (G : SimpleGraph (Fin n)) (hn : 0 < n)
    (hm : 4*m + n/2 ≤ n)
    (hs : ∀ k, 2*m ≤ k → k + 2*m ≤ n → ∃ A B : Finset (Fin n),
      A.card = k ∧ B.card = k ∧ edgeProfile G A + 2*n*t ≤ edgeProfile G B) :
    Erdos636.HasManyDistinctInducedSubgraphs G (((n/2)*t : ℕ) : ℝ) := by
  classical
  have hk₁ (i : Fin (n/2)) : 2*m ≤ 2*m + (i : ℕ) := Nat.le_add_right _ _
  have hk₂ (i : Fin (n/2)) : 2*m + (i : ℕ) + 2*m ≤ n := by omega
  choose A B hA hB hspread using (fun i => hs (2*m + (i : Fin (n/2))) (hk₁ i) (hk₂ i))
  let target (i : Fin (n/2)) (j : Fin t) := edgeProfile G (A i) + 2*n*(j : ℕ)
  have intermediate (i : Fin (n/2)) (j : Fin t) := intermediate_profile G (A i) (B i)
    ((hA i).trans (hB i).symm) (target i j) (Nat.le_add_right _ _)
    (le_trans (Nat.add_le_add_left (Nat.mul_le_mul_left (2*n) j.isLt.le) _) (hspread i))
  choose S hS hSl hSu using intermediate
  let f (p : Fin (n/2) × Fin t) := (S p.1 p.2 : Set (Fin n))
  have hS_order (i : Fin (n/2)) (j j' : Fin t) (h : j < j') :
      edgeProfile G (S i j) < edgeProfile G (S i j') := by
    have h₁ := hSu i j
    have h₂ := hSl i j'
    have hmul := Nat.mul_le_mul_left (2*n) (show (j : ℕ)+1 ≤ (j' : ℕ) from h)
    rw [Nat.mul_add, Nat.mul_one] at hmul
    dsimp [target] at h₁ h₂
    omega
  have hPair (x y : Fin (n/2) × Fin t) (hxy : x ≠ y) :
      (f x).ncard ≠ (f y).ncard ∨
      (G.induce (f x)).edgeSet.ncard ≠ (G.induce (f y)).edgeSet.ncard := by
    rcases x with ⟨i,j⟩
    rcases y with ⟨i',j'⟩
    by_cases hi : i = i'
    · subst i'
      have hj : j ≠ j' := fun h => hxy (by rw [h])
      right
      rcases lt_or_gt_of_ne hj with h | h
      · exact (hS_order i j j' h).ne
      · exact (hS_order i j' j h).ne.symm
    · left
      dsimp [f]
      rw [Set.ncard_coe_finset, Set.ncard_coe_finset, hS, hS, hA, hA]
      exact fun h => hi (Fin.ext (by omega))
  have hinj : Function.Injective f := by
    intro a b hab
    by_contra hne
    rcases hPair a b hne with h | h
    · exact h (congrArg Set.ncard hab)
    · exact h (congrArg (fun U => (G.induce U).edgeSet.ncard) hab)
  refine ⟨Set.range f, ?_, ?_⟩
  · rintro _ ⟨x,rfl⟩ _ ⟨y,rfl⟩ h
    exact hPair x y (fun e => h (congrArg f e))
  · rw [Set.ncard_range_of_injective hinj, Nat.card_prod, Nat.card_fin, Nat.card_fin]

lemma count_monotone {V : Type*} {G : SimpleGraph V} {a b : ℝ} (h : a ≤ b) :
    Erdos636.HasManyDistinctInducedSubgraphs G b → Erdos636.HasManyDistinctInducedSubgraphs G a := by
  rintro ⟨S,hS,hcard⟩
  exact ⟨S,hS,h.trans hcard⟩

end Erdos636Proof

open Erdos636Proof

theorem OMA.solution : type_of% @Erdos636.erdos_636.variants.erdos_faudree_sos := by
  intro C hC
  obtain ⟨a,ha,N,hN⟩ := eventual_density C hC
  let δ := min (1 : ℝ) (a^4/1680)
  have hδ : 0 < δ := lt_min (by norm_num) (by positivity)
  have hδ1 : δ ≤ 1 := min_le_left _ _
  let c := (δ/64)*(Real.sqrt ((δ/8)*(δ/64))/10)
  have hc : 0 < c := by dsimp [c]; positivity
  obtain ⟨M₁,hM₁⟩ := exists_nat_ge (64/δ)
  obtain ⟨M₂,hM₂⟩ := exists_nat_ge ((4/c)^2)
  refine ⟨c/12, by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop (max N (max M₁ (max M₂ 4)))] with n hnt
  intro G hcl hi
  have hnN : N ≤ n := le_trans (le_max_left _ _) hnt
  have hn4 : 4 ≤ n := le_trans (by omega) hnt
  have hn : 0 < n := by omega
  have hnM1 : (64/δ : ℝ) ≤ n := hM₁.trans (by exact_mod_cast (show M₁ ≤ n by omega))
  have hnM2 : (4/c : ℝ)^2 ≤ n := hM₂.trans (by exact_mod_cast (show M₂ ≤ n by omega))
  have hnR : 0 < (n : ℝ) := by positivity
  have h2m : (2 : ℝ) ≤ δ * n / 32 := by
    rw [div_le_iff₀ hδ] at hnM1
    linarith
  have hsqrt : (4/c : ℝ) ≤ Real.sqrt n := (Real.le_sqrt (by positivity) (by positivity)).2 hnM2
  have h2t : (2 : ℝ) ≤ c * Real.sqrt n / 2 := by
    rw [div_le_iff₀ hc] at hsqrt
    linarith
  let m := ⌊δ*n/32⌋₊
  let t := ⌊c*Real.sqrt n/2⌋₊
  have hm_low : δ*n/64 ≤ (m : ℝ) := by
    have h := floor_half _ h2m
    change _ ≤ (m : ℝ) at h
    linarith
  have ht_low : c*Real.sqrt n/4 ≤ (t : ℝ) := by
    have h := floor_half _ h2t
    change _ ≤ (t : ℝ) at h
    linarith
  have hm_hi : (m : ℝ) ≤ δ*n/32 := Nat.floor_le (by positivity)
  have ht_hi : (t : ℝ) ≤ c*Real.sqrt n/2 := Nat.floor_le (by positivity)
  have hmp : 0 < m := by
    exact_mod_cast (show 0 < (m : ℝ) from lt_of_lt_of_le (by positivity) hm_low)
  have hm : 4*m + n/2 ≤ n := by
    have hm4 : 4*m ≤ n/2 := by
      have hmR : (8*m : ℝ) ≤ n := by nlinarith [mul_le_mul_of_nonneg_right hδ1 hnR.le]
      have hmN : 8*m ≤ n := by exact_mod_cast hmR
      omega
    omega
  obtain ⟨he,hd⟩ := hN n hnN G hcl hi
  have hgood : δ * (n : ℝ)^4 ≤ (goodRectangles G).card :=
    (mul_le_mul_of_nonneg_right (min_le_right _ _) (by positivity)).trans (enough_rectangles G ha.le he hd hn)
  obtain ⟨L,R,hL,hR,_,_,hLd,hRd,hLR,hcol⟩ := exists_rectangle_pairings hn G hδ hδ1 hmp hm_hi hgood
  have hspread := discrepancy_from_pairings G L R hL hR hLd hRd hLR hcol
  have hv : (δ/8)*(δ/64)*(n : ℝ) ≤ (δ/8)*m := by
    nlinarith [mul_le_mul_of_nonneg_left hm_low (show 0 ≤ δ/8 by positivity)]
  have hv' : Real.sqrt ((δ/8)*(δ/64)) * Real.sqrt n ≤ Real.sqrt (δ/8*m) := by
    rw [← Real.sqrt_mul (by positivity)]
    exact Real.sqrt_le_sqrt hv
  have hs : ∀ k, 2*m ≤ k → k + 2*m ≤ n → ∃ A B : Finset (Fin n),
      A.card = k ∧ B.card = k ∧ edgeProfile G A + 2*n*t ≤ edgeProfile G B := by
    intro k hk₁ hk₂
    obtain ⟨A,B,hA,hB,hdiff⟩ := hspread k hk₁ hk₂
    refine ⟨A,B,hA,hB,?_⟩
    have hc' : c * (n : ℝ) * Real.sqrt n ≤ (m : ℝ) * (Real.sqrt (δ/8*m)/10) := by
      calc c * (n : ℝ) * Real.sqrt n =
          (δ*n/64) * ((Real.sqrt ((δ/8)*(δ/64))*Real.sqrt n)/10) := by dsimp [c]; ring
        _ ≤ _ := by gcongr
    have ht : (2 : ℝ)*n*t ≤ c * n * Real.sqrt n := by
      nlinarith [mul_le_mul_of_nonneg_left ht_hi (show 0 ≤ (2 : ℝ)*n by positivity)]
    exact_mod_cast (show (edgeProfile G A : ℝ) + 2*n*t ≤ edgeProfile G B by linarith)
  apply count_monotone _ (distinct_profiles G hn hm hs)
  have hnfl : (n : ℝ)/3 ≤ ((n/2 : ℕ) : ℝ) := by
    have h : n ≤ 3*(n/2) := by omega
    have h' : (n : ℝ) ≤ 3*((n/2 : ℕ) : ℝ) := by exact_mod_cast h
    linarith
  have hmul : (n/3 : ℝ)*(c*Real.sqrt n/4) ≤ (((n/2 : ℕ) : ℝ) * (t : ℝ)) := by gcongr
  have hr : (n : ℝ) ^ (3/2 : ℝ) = (n : ℝ)*Real.sqrt n := by
    calc
      (n : ℝ) ^ (3/2 : ℝ) = (n : ℝ) ^ (1+(1/2) : ℝ) := by norm_num
      _ = (n : ℝ) ^ (1 : ℝ) * (n : ℝ) ^ (1/2 : ℝ) := Real.rpow_add hnR _ _
      _ = (n : ℝ) * Real.sqrt n := by rw [Real.rpow_one, Real.sqrt_eq_rpow]
  rw [hr, Nat.cast_mul]
  convert hmul using 1 <;> ring
