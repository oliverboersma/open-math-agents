import OMAReductions.R_Erdos757_erdos_757_variants_lowerBound_R1_H1_R1_H3_R1
import Mathlib

/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/

/-! The Tutte–Berge formula below is adapted from Juan Pablo Traverso Gianini,
 jtraverso/berge-matching, commit f01d042c071c778fb3f432312356136a92369076,
 Apache-2.0. The incidence counting and dual matching conversion are original. -/

open SimpleGraph

namespace BergeMatching

variable {V : Type*}

/-- The number of connected components of odd order of `G − U` (as in Mathlib's
`SimpleGraph.IsTutteViolator`). -/
noncomputable def oddCount (G : SimpleGraph V) (U : Set V) : ℕ :=
  ((⊤ : G.Subgraph).deleteVerts U).coe.oddComponents.ncard
private lemma ncard_oddComponents_congr {W W' : Type*} {H : SimpleGraph W} {H' : SimpleGraph W'}
    (e : H ≃g H') : H.oddComponents.ncard = H'.oddComponents.ncard := by
  rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
  refine Nat.card_congr (e.connectedComponentEquiv.subtypeEquiv fun c => ?_)
  simp only [Set.mem_ofPred_eq]
  rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq,
    Nat.card_congr (ConnectedComponent.isoEquivSupp e c)]

open Finset in
private lemma ncard_verts_eq_two_mul [Finite V] {G : SimpleGraph V} {M : G.Subgraph}
    (hM : M.IsMatching) : M.verts.ncard = 2 * M.edgeSet.ncard := by
  classical
  have := Fintype.ofFinite V
  have h := M.spanningCoe.sum_degrees_eq_twice_card_edges
  have hdeg : ∀ v, M.spanningCoe.degree v = if v ∈ M.verts then 1 else 0 := by
    intro v
    rw [Subgraph.degree_spanningCoe]
    split_ifs with hv
    · exact (Subgraph.isMatching_iff_forall_degree.1 hM) v hv
    · exact Subgraph.degree_of_notMem_verts hv
  simp only [hdeg, Finset.sum_boole, Nat.cast_id] at h
  have e1 : M.verts.ncard = #{x | x ∈ M.verts} := by
    rw [← Set.ncard_coe_finset]; congr; ext; simp
  have e2 : M.edgeSet.ncard = #M.spanningCoe.edgeFinset := by
    rw [← Set.ncard_coe_finset, coe_edgeFinset, Subgraph.edgeSet_spanningCoe]
  rw [e1, e2, h]

/-- The graph `G` with `d` extra universal vertices. -/
private def aug (G : SimpleGraph V) (d : ℕ) : SimpleGraph (V ⊕ Fin d) where
  Adj x y := x ≠ y ∧ ∀ a b, x = .inl a → y = .inl b → G.Adj a b
  symm := ⟨fun _ _ h => ⟨h.1.symm, fun a b hx hy => (h.2 b a hy hx).symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

@[simp] private lemma aug_adj_inl_inl {G : SimpleGraph V} {d : ℕ} {a b : V} :
    (aug G d).Adj (.inl a) (.inl b) ↔ G.Adj a b := by
  change _ ∧ _ ↔ _
  refine ⟨fun h => h.2 a b rfl rfl, fun h => ⟨fun h' => h.ne (Sum.inl_injective h'), ?_⟩⟩
  rintro a' b' ha hb
  cases ha; cases hb; exact h

@[simp] private lemma aug_adj_inl_inr {G : SimpleGraph V} {d : ℕ} {a : V} {i : Fin d} :
    (aug G d).Adj (.inl a) (.inr i) :=
  show _ ∧ _ from ⟨Sum.inl_ne_inr, fun _ _ _ h => by cases h⟩

@[simp] private lemma aug_adj_inr_inl {G : SimpleGraph V} {d : ℕ} {a : V} {i : Fin d} :
    (aug G d).Adj (.inr i) (.inl a) :=
  aug_adj_inl_inr.symm

/-- The set of vertices of `aug G d` corresponding to `U` together with all new vertices. -/
private def augSet (U : Set V) (d : ℕ) : Set (V ⊕ Fin d) := Sum.inl '' U ∪ Set.range Sum.inr

@[simp] private lemma inl_mem_augSet {U : Set V} {d : ℕ} {a : V} :
    (Sum.inl a : V ⊕ Fin d) ∈ augSet U d ↔ a ∈ U := by
  simp [augSet]

@[simp] private lemma inr_mem_augSet {U : Set V} {d : ℕ} {i : Fin d} :
    (Sum.inr i : V ⊕ Fin d) ∈ augSet U d := by
  simp [augSet]

private lemma ncard_augSet [Finite V] (U : Set V) (d : ℕ) : (augSet U d).ncard = U.ncard + d := by
  rw [augSet, Set.ncard_union_eq, Set.ncard_image_of_injective _ Sum.inl_injective,
    Set.ncard_range_of_injective Sum.inr_injective, Nat.card_eq_fintype_card, Fintype.card_fin]
  rw [Set.disjoint_left]
  rintro _ ⟨a, _, rfl⟩ ⟨i, hi⟩
  cases hi

private lemma oddCount_aug_augSet [Finite V] (G : SimpleGraph V) (U : Set V) (d : ℕ) :
    oddCount (aug G d) (augSet U d) = oddCount G U := by
  let f : ((⊤ : G.Subgraph).deleteVerts U).verts →
      ((⊤ : (aug G d).Subgraph).deleteVerts (augSet U d)).verts :=
    fun a => ⟨Sum.inl a.1, by
      have := a.2
      simp only [Subgraph.deleteVerts_verts, Subgraph.verts_top, Set.mem_sdiff, Set.mem_univ,
        true_and, augSet, Set.mem_union, Set.mem_image, Sum.inl.injEq, exists_eq_right,
        Set.mem_range, reduceCtorEq, exists_false, or_false] at this ⊢
      exact this⟩
  have hf : Function.Bijective f := by
    refine ⟨fun a b h => Subtype.ext (Sum.inl_injective (congrArg Subtype.val h)), ?_⟩
    rintro ⟨x, hx⟩
    simp only [Subgraph.deleteVerts_verts, Subgraph.verts_top, Set.mem_sdiff, Set.mem_univ,
      true_and, augSet, Set.mem_union, Set.mem_image, Set.mem_range, not_or] at hx
    rcases x with a | i
    · refine ⟨⟨a, ?_⟩, rfl⟩
      simp only [Subgraph.deleteVerts_verts, Subgraph.verts_top, Set.mem_sdiff, Set.mem_univ,
        true_and]
      exact fun ha => hx.1 ⟨a, ha, rfl⟩
    · exact absurd ⟨i, rfl⟩ hx.2
  let e : ((⊤ : G.Subgraph).deleteVerts U).coe ≃g
      ((⊤ : (aug G d).Subgraph).deleteVerts (augSet U d)).coe :=
    { Equiv.ofBijective f hf with
      map_rel_iff' := by
        intro a b
        simp [f, inl_mem_augSet] }
  exact (ncard_oddComponents_congr e).symm

/-- The copy of a subgraph `M` of `G` inside `aug G d`. -/
private def liftSub {G : SimpleGraph V} (M : G.Subgraph) (d : ℕ) : (aug G d).Subgraph where
  verts := Sum.inl '' M.verts
  Adj x y := ∃ a b, x = .inl a ∧ y = .inl b ∧ M.Adj a b
  adj_sub := by
    rintro _ _ ⟨a, b, rfl, rfl, h⟩
    exact aug_adj_inl_inl.2 (M.adj_sub h)
  edge_vert := by
    rintro _ _ ⟨a, b, rfl, rfl, h⟩
    exact ⟨a, M.edge_vert h, rfl⟩
  symm := ⟨by
    rintro _ _ ⟨a, b, rfl, rfl, h⟩
    exact ⟨b, a, rfl, rfl, h.symm⟩⟩

private lemma liftSub_isMatching {G : SimpleGraph V} {M : G.Subgraph} (hM : M.IsMatching) (d : ℕ) :
    (liftSub M d).IsMatching := by
  rintro _ ⟨a, ha, rfl⟩
  obtain ⟨b, hb, hu⟩ := hM ha
  refine ⟨.inl b, ⟨a, b, rfl, rfl, hb⟩, ?_⟩
  rintro _ ⟨a', b', h1, rfl, h⟩
  cases h1
  rw [hu b' h]

lemma card_deleteVerts_add [Finite V] (G : SimpleGraph V) (U : Set V) :
    Nat.card ((⊤ : G.Subgraph).deleteVerts U).verts + U.ncard = Nat.card V := by
  have : ((⊤ : G.Subgraph).deleteVerts U).verts = Uᶜ := by ext; simp
  rw [this, Nat.card_coe_set_eq, add_comm, Set.ncard_add_ncard_compl]

private lemma aug_no_tutteViolator [Finite V] (G : SimpleGraph V) (d : ℕ)
    (hd : ∀ U : Set V, oddCount G U ≤ U.ncard + d) (hpar : Even (Nat.card V + d))
    (W : Set (V ⊕ Fin d)) : ¬ (aug G d).IsTutteViolator W := by
  intro hW
  rw [IsTutteViolator] at hW
  by_cases h : ∀ i, Sum.inr i ∈ W
  · have hWeq : W = augSet (Sum.inl ⁻¹' W) d := by
      ext x
      rcases x with a | i
      · simp
      · simp [h i]
    have h1 : oddCount (aug G d) W ≤ W.ncard := by
      rw [hWeq, oddCount_aug_augSet, ncard_augSet]
      exact hd _
    exact absurd hW (not_lt.2 h1)
  · push Not at h
    obtain ⟨i, hi⟩ := h
    set H := ((⊤ : (aug G d).Subgraph).deleteVerts W).coe
    have hj : (Sum.inr i : V ⊕ Fin d) ∈ ((⊤ : (aug G d).Subgraph).deleteVerts W).verts := by
      simpa using hi
    have hconn : ∀ x : ((⊤ : (aug G d).Subgraph).deleteVerts W).verts,
        H.connectedComponentMk x = H.connectedComponentMk ⟨_, hj⟩ := by
      rintro ⟨x, hx⟩
      by_cases hxi : x = Sum.inr i
      · subst hxi; rfl
      · apply ConnectedComponent.connectedComponentMk_eq_of_adj
        have hx' : x ∉ W := by simpa using hx
        simp only [H, Subgraph.coe_adj, Subgraph.deleteVerts_adj, Subgraph.verts_top,
          Set.mem_univ, true_and, Subgraph.top_adj]
        refine ⟨hx', hi, ?_⟩
        rcases x with a | i'
        · exact aug_adj_inl_inr
        · refine ⟨hxi, fun _ _ h _ => by cases h⟩
    have hle : H.oddComponents.ncard ≤ 1 := by
      refine (Set.ncard_le_one (Set.toFinite _)).2 fun c _ c' _ => ?_
      induction c using ConnectedComponent.ind
      induction c' using ConnectedComponent.ind
      exact (hconn _).trans (hconn _).symm
    have hW0 : W.ncard = 0 := by
      change W.ncard < H.oddComponents.ncard at hW
      omega
    have hodd : Odd H.oddComponents.ncard := by
      change W.ncard < H.oddComponents.ncard at hW
      have : H.oddComponents.ncard = 1 := by omega
      rw [this]; exact odd_one
    rw [odd_ncard_oddComponents] at hodd
    have := card_deleteVerts_add (aug G d) W
    rw [hW0, Nat.card_sum, Nat.card_eq_fintype_card (α := Fin d), Fintype.card_fin] at this
    rw [Nat.add_zero] at this
    change Odd (Nat.card ((⊤ : (aug G d).Subgraph).deleteVerts W).verts) at hodd
    rw [this] at hodd
    exact (Nat.not_even_iff_odd.2 hodd) hpar
theorem two_mul_card_add_le [Finite V] {G : SimpleGraph V} {M : G.Subgraph} (hM : M.IsMatching)
    (U : Set V) : 2 * M.edgeSet.ncard + oddCount G U ≤ Nat.card V + U.ncard := by
  classical
  set d := (M.vertsᶜ).ncard with hd
  let s : Set (V ⊕ Fin d) := Sum.inl '' M.vertsᶜ
  let t : Set (V ⊕ Fin d) := Set.range Sum.inr
  have hst : Disjoint s t := by
    rw [Set.disjoint_left]
    rintro _ ⟨a, _, rfl⟩ ⟨i, hi⟩
    cases hi
  have hcard : Nat.card s = Nat.card t := by
    rw [Nat.card_coe_set_eq, Nat.card_coe_set_eq, Set.ncard_image_of_injective _ Sum.inl_injective,
      Set.ncard_range_of_injective Sum.inr_injective, Nat.card_eq_fintype_card, Fintype.card_fin]
  obtain ⟨f⟩ := Finite.card_eq.1 hcard
  have hadj : ∀ v : s, (aug G d).Adj v (f v) := by
    rintro ⟨_, a, _, rfl⟩
    generalize f _ = y
    obtain ⟨_, i, rfl⟩ := y
    exact aug_adj_inl_inr
  obtain ⟨M2, hM2v, hM2⟩ := Subgraph.IsMatching.exists_of_disjoint_sets_of_equiv hst f hadj
  have hM1 := liftSub_isMatching hM d
  have hdisj : Disjoint (liftSub M d).support M2.support := by
    rw [hM1.support_eq_verts, hM2.support_eq_verts, hM2v, Set.disjoint_union_right]
    refine ⟨?_, ?_⟩
    · rw [Set.disjoint_left]
      rintro _ ⟨a, ha, rfl⟩ ⟨b, hb, hab⟩
      cases hab
      exact hb ha
    · rw [Set.disjoint_left]
      rintro _ ⟨a, _, rfl⟩ ⟨i, hi⟩
      cases hi
  have hperf : (liftSub M d ⊔ M2).IsPerfectMatching := by
    refine ⟨hM1.sup hM2 hdisj, fun x => ?_⟩
    rw [Subgraph.verts_sup, hM2v]
    rcases x with a | i
    · by_cases ha : a ∈ M.verts
      · exact Or.inl ⟨a, ha, rfl⟩
      · exact Or.inr (Or.inl ⟨a, ha, rfl⟩)
    · exact Or.inr (Or.inr ⟨i, rfl⟩)
  have h1 := not_isTutteViolator_of_isPerfectMatching hperf (augSet U d)
  rw [IsTutteViolator, not_lt] at h1
  have h2 : oddCount (aug G d) (augSet U d) ≤ U.ncard + d := by
    rw [← ncard_augSet]; exact h1
  rw [oddCount_aug_augSet] at h2
  have h3 := Set.ncard_add_ncard_compl M.verts
  rw [ncard_verts_eq_two_mul hM] at h3
  omega

/-- **The Tutte–Berge formula.** A finite graph has a matching `M` and a vertex set `U` with
`2 |M| + odd(G − U) = |V| + |U|`. -/
theorem exists_tutte_berge [Finite V] (G : SimpleGraph V) :
    ∃ (M : G.Subgraph) (U : Set V), M.IsMatching ∧
      2 * M.edgeSet.ncard + oddCount G U = Nat.card V + U.ncard := by
  classical
  obtain ⟨U0, hU0⟩ := Finite.exists_max (fun U : Set V => (oddCount G U : ℤ) - U.ncard)
  have hge : U0.ncard ≤ oddCount G U0 := by
    have := hU0 ∅
    simp only [Set.ncard_empty, Nat.cast_zero, sub_zero] at this
    omega
  set d := oddCount G U0 - U0.ncard with hd
  have hdU : ∀ U : Set V, oddCount G U ≤ U.ncard + d := by
    intro U
    have := hU0 U
    omega
  have hpar : Even (Nat.card V + d) := by
    have h1 := (odd_ncard_oddComponents (G := ((⊤ : G.Subgraph).deleteVerts U0).coe))
    have h2 := card_deleteVerts_add G U0
    change Odd (oddCount G U0) ↔ _ at h1
    rw [← h2]
    rcases Nat.even_or_odd (oddCount G U0) with he | ho
    · have : Even (Nat.card ((⊤ : G.Subgraph).deleteVerts U0).verts) := by
        rw [← Nat.not_odd_iff_even, ← h1, Nat.not_odd_iff_even]; exact he
      have : Nat.card ((⊤ : G.Subgraph).deleteVerts U0).verts + U0.ncard + d =
          Nat.card ((⊤ : G.Subgraph).deleteVerts U0).verts + oddCount G U0 := by omega
      rw [this]; exact Even.add (by assumption) he
    · have h3 := h1.1 ho
      have : Nat.card ((⊤ : G.Subgraph).deleteVerts U0).verts + U0.ncard + d =
          Nat.card ((⊤ : G.Subgraph).deleteVerts U0).verts + oddCount G U0 := by omega
      rw [this]; exact Odd.add_odd h3 ho
  obtain ⟨M', hM'⟩ := tutte.2 (aug_no_tutteViolator G d hdU hpar)
  let M : G.Subgraph :=
    { verts := {a | ∃ b, M'.Adj (.inl a) (.inl b)}
      Adj a b := M'.Adj (.inl a) (.inl b)
      adj_sub := fun h => aug_adj_inl_inl.1 (M'.adj_sub h)
      edge_vert := fun h => ⟨_, h⟩
      symm := ⟨fun _ _ h => h.symm⟩ }
  have hM : M.IsMatching := by
    rintro a ⟨b, hb⟩
    exact ⟨b, hb, fun c hc => Sum.inl_injective (hM'.1.eq_of_adj_left hc hb)⟩
  have hp : ∀ a : V, ∃ y, M'.Adj (.inl a) y := fun a => (hM'.1 (hM'.2 (.inl a))).exists
  choose p hp using hp
  have hcompl : (M.vertsᶜ).ncard ≤ d := by
    have := Set.ncard_le_ncard_of_injOn (s := M.vertsᶜ)
      (t := Set.range (Sum.inr : Fin d → V ⊕ Fin d)) p ?_ ?_
    · rwa [Set.ncard_range_of_injective Sum.inr_injective, Nat.card_eq_fintype_card,
        Fintype.card_fin] at this
    · intro a ha
      rcases hpa : p a with b | i
      · exact absurd ⟨b, hpa ▸ hp a⟩ ha
      · exact ⟨i, rfl⟩
    · intro a _ a' _ h
      have := hM'.1.eq_of_adj_right (hp a) (h ▸ hp a')
      exact Sum.inl_injective this
  have hweak := two_mul_card_add_le hM U0
  have h3 := Set.ncard_add_ncard_compl M.verts
  rw [ncard_verts_eq_two_mul hM] at h3
  exact ⟨M, U0, hM, by omega⟩

end BergeMatching

namespace OMA757Dual
open Finset SimpleGraph
open scoped Classical

private lemma incidence_count {A : Finset ℝ} {E V : Finset (Finset ℝ)}
    (uniform : ∀ e ∈ E, e ⊆ A ∧ e.card = 3)
    (deg : ∀ v ∈ A, (E.filter fun e => v ∈ e).card ≤ 2) (sub : V ⊆ E) :
    let X := V.biUnion id
    11*V.card + (if Odd V.card then 17 else 0) ≤ 10*X.card := by
  classical
  intro X
  have each {e} (he : e ∈ V) : e ⊆ X := fun v hv => mem_biUnion.mpr ⟨e,he,hv⟩
  have toA : X ⊆ A := by
    intro v hv
    obtain ⟨e,he,hve⟩ := mem_biUnion.mp hv
    exact (uniform e (sub he)).1 hve
  have lo (e) (he : e ∈ V) : 3 ≤ (X.bipartiteAbove (fun e v => v ∈ e) e).card := by
    rw [show X.bipartiteAbove (fun e v => v ∈ e) e = e by
      ext v
      exact ⟨fun h => (mem_filter.mp h).2,fun h => mem_filter.mpr ⟨each he h,h⟩⟩,
      (uniform e (sub he)).2]
  have hi (v) (hv : v ∈ X) : (V.bipartiteBelow (fun e v => v ∈ e) v).card ≤ 2 :=
    (card_le_card (filter_subset_filter _ sub)).trans (deg v (toA hv))
  have count := card_nsmul_le_card_nsmul (R := ℕ) (fun (e : Finset ℝ) (v : ℝ) => v ∈ e) lo hi
  change V.card * 3 ≤ X.card * 2 at count
  split_ifs with odd
  · obtain ⟨k,hk⟩ := odd
    obtain ⟨e,he⟩ := card_pos.mp (show 0<V.card by omega)
    have large := card_le_card (each he)
    rw [(uniform e (sub he)).2] at large
    omega
  · omega

private lemma barrier_bound {A : Finset ℝ} {E : Finset (Finset ℝ)}
    (uniform : ∀ e ∈ E, e ⊆ A ∧ e.card = 3)
    (deg : ∀ v ∈ A, (E.filter fun e => v ∈ e).card ≤ 2)
    (G : SimpleGraph E) (graph : ∀ i j : E, G.Adj i j ↔ i ≠ j ∧ (i.val ∩ j.val).Nonempty)
    (S : Set E) : 11*E.card + 17*BergeMatching.oddCount G S ≤ 10*A.card + 17*S.ncard := by
  classical
  let R := (⊤ : G.Subgraph).deleteVerts S
  let C := R.coe.ConnectedComponent
  let : Fintype R.verts := Fintype.ofFinite _
  let : Fintype C := Fintype.ofFinite _
  let edge (i : R.verts) : Finset ℝ := i.val.val
  have ei : Function.Injective edge := fun _ _ h => Subtype.ext (Subtype.ext h)
  let V (c : C) := c.supp.toFinset.image edge
  let X (c : C) := (V c).biUnion id
  have vsub (c : C) : V c ⊆ E := by
    rintro e he
    obtain ⟨i,_,rfl⟩ := mem_image.mp he
    exact i.val.property
  have xsub (c : C) : X c ⊆ A := by
    rintro x hx
    obtain ⟨e,he,hxe⟩ := mem_biUnion.mp hx
    exact (uniform e (vsub c he)).1 hxe
  have vc (c : C) : (V c).card = c.supp.ncard := by
    rw [show (V c).card = c.supp.toFinset.card from card_image_of_injective _ ei,Set.ncard_eq_toFinset_card']
  have fiber (c : C) : c.supp.toFinset = univ.filter (fun i : R.verts => R.coe.connectedComponentMk i = c) := by
    ext i
    simp [ConnectedComponent.mem_supp_iff]
  have total : (∑ c : C, (V c).card) = Nat.card R.verts := by
    simp_rw [vc,Set.ncard_eq_toFinset_card',fiber]
    simpa using (card_eq_sum_card_fiberwise (s:=univ) (t:=(univ : Finset C))
      (f:=R.coe.connectedComponentMk) (fun _ _ => mem_univ _)).symm
  have odd : (∑ c : C, if Odd (V c).card then 17 else 0) = 17*BergeMatching.oddCount G S := by
    simp_rw [vc]
    rw [← sum_filter]
    simp only [sum_const,nsmul_eq_mul]
    rw [Nat.mul_comm]
    congr 1
    change (univ.filter fun c : C => Odd c.supp.ncard).card = R.coe.oddComponents.ncard
    rw [Set.ncard_eq_toFinset_card']
    congr 1
    ext c
    simp [SimpleGraph.oddComponents]
  have disj : ((univ : Finset C) : Set C).PairwiseDisjoint X := by
    intro c _ d _ ne
    apply Finset.disjoint_left.mpr
    intro x hc hd
    obtain ⟨e,he,hxe⟩ := mem_biUnion.mp hc
    obtain ⟨f,hf,hxf⟩ := mem_biUnion.mp hd
    obtain ⟨i,hi,rfl⟩ := mem_image.mp he
    obtain ⟨j,hj,rfl⟩ := mem_image.mp hf
    have hci := (ConnectedComponent.mem_supp_iff c i).mp (Set.mem_toFinset.mp hi)
    have hdj := (ConnectedComponent.mem_supp_iff d j).mp (Set.mem_toFinset.mp hj)
    apply ne
    rw [← hci,← hdj]
    by_cases eq : i = j
    · rw [eq]
    · apply ConnectedComponent.connectedComponentMk_eq_of_adj
      exact ⟨i.property,j.property,(graph _ _).mpr ⟨fun h => eq (Subtype.ext h),x,mem_inter.mpr ⟨hxe,hxf⟩⟩⟩
  have parts : (∑ c : C,(X c).card) ≤ A.card := by
    rw [← card_biUnion disj]
    exact card_le_card (fun x hx => by
      obtain ⟨c,_,h⟩ := mem_biUnion.mp hx
      exact xsub c h)
  have sum := sum_le_sum (s:=(univ : Finset C)) (fun c _ => incidence_count uniform deg (vsub c))
  change (∑ c : C, (11*(V c).card + (if Odd (V c).card then 17 else 0))) ≤ ∑ c : C,10*(X c).card at sum
  rw [sum_add_distrib,← mul_sum,← mul_sum,total,odd] at sum
  have card := BergeMatching.card_deleteVerts_add G S
  change Nat.card R.verts + S.ncard = Nat.card E at card
  rw [show Nat.card E = E.card by simp] at card
  omega


private lemma extract {A : Finset ℝ} {E : Finset (Finset ℝ)}
    (uniform : ∀ e ∈ E, e ⊆ A ∧ e.card = 3)
    (deg : ∀ v ∈ A, (E.filter fun e => v ∈ e).card ≤ 2)
    (G : SimpleGraph E) (graph : ∀ i j : E, G.Adj i j ↔ i ≠ j ∧ (i.val ∩ j.val).Nonempty)
    (M : G.Subgraph) (hm : M.IsMatching) :
    let L := fun v : ℝ => E.filter fun e => v ∈ e
    ∃ T ⊆ A, T.card = M.edgeSet.ncard ∧ (∀ v ∈ T, (L v).card = 2) ∧
      (T : Set ℝ).PairwiseDisjoint L := by
  classical
  intro L
  let : Fintype M.edgeSet := Fintype.ofFinite _
  have ends (z : M.edgeSet) : ∃ i j : E, z.val = s(i,j) ∧ M.Adj i j := by
    obtain ⟨z,hz⟩ := z
    induction z using Sym2.ind with
    | _ i j => exact ⟨i,j,rfl,hz⟩
  choose i j form adj using ends
  have cross (z : M.edgeSet) := (graph _ _).mp (M.adj_sub (adj z))
  choose w hw using fun z => (cross z).2
  have inside (z) : w z ∈ A := (uniform _ (i z).property).1 (mem_inter.mp (hw z)).1
  have ne (z) : (i z).val ≠ (j z).val := fun h => (cross z).1 (Subtype.ext h)
  have both (z) : L (w z) = {(i z).val,(j z).val} := by
    symm
    apply eq_of_subset_of_card_le
    · apply insert_subset (mem_filter.mpr ⟨(i z).property,(mem_inter.mp (hw z)).1⟩)
      exact singleton_subset_iff.mpr (mem_filter.mpr ⟨(j z).property,(mem_inter.mp (hw z)).2⟩)
    · simpa [ne z] using deg (w z) (inside z)
  have recover (z) (e) (he : e ∈ L (w z)) :
      ∃ t : M.verts, t.val.val = e ∧ hm.toEdge t = z := by
    rw [both] at he
    simp only [mem_insert,mem_singleton] at he
    rcases he with rfl | rfl
    · refine ⟨⟨_,(adj z).fst_mem⟩,rfl,?_⟩
      rw [hm.toEdge_eq_of_adj (adj z)]
      exact Subtype.ext (form z).symm
    · refine ⟨⟨_,(adj z).snd_mem⟩,rfl,?_⟩
      rw [hm.toEdge_eq_of_adj (adj z).symm]
      exact Subtype.ext ((Sym2.eq_swap ..).trans (form z).symm)
  have same (z z') (e) (he : e ∈ L (w z)) (he' : e ∈ L (w z')) : z=z' := by
    obtain ⟨t,ht,eq⟩ := recover z e he
    obtain ⟨t',ht',eq'⟩ := recover z' e he'
    have h : t = t' := Subtype.ext (Subtype.ext (ht.trans ht'.symm))
    subst t'
    exact eq.symm.trans eq'
  have inj : Function.Injective w := by
    intro z z' h
    have he : (i z).val ∈ L (w z) := by rw [both]; simp
    exact same z z' _ he (h ▸ he)
  refine ⟨univ.image w,?_,?_,?_,?_⟩
  · intro v hv
    obtain ⟨z,_,rfl⟩ := mem_image.mp hv
    exact inside z
  · rw [card_image_of_injective _ inj,card_univ,← Nat.card_eq_fintype_card,Nat.card_coe_set_eq]
  · intro v hv
    obtain ⟨z,_,rfl⟩ := mem_image.mp hv
    simp [both z,ne z]
  · intro v hv u hu ne
    obtain ⟨z,_,rfl⟩ := mem_image.mp hv
    obtain ⟨z',_,rfl⟩ := mem_image.mp hu
    exact disjoint_left.mpr (fun {e} h₁ h₂ => ne (congrArg w (same z z' e h₁ h₂)))

end OMA757Dual

open Finset SimpleGraph

theorem OMA.solution : OMA.R_Erdos757_erdos_757_variants_lowerBound_R1_H1_R1_H3_R1.H1 := by
  classical
  intro A E uniform _ L deg
  let G : SimpleGraph E := {
    Adj := fun i j => i ≠ j ∧ (i.val ∩ j.val).Nonempty
    symm := ⟨fun _ _ h => ⟨h.1.symm,by rw [inter_comm]; exact h.2⟩⟩
    loopless := ⟨fun _ h => h.1 rfl⟩ }
  obtain ⟨M,S,hm,hsize⟩ := BergeMatching.exists_tutte_berge G
  have bound := OMA757Dual.barrier_bound uniform deg G (fun _ _ => Iff.rfl) S
  obtain ⟨T,sub,size,two,disj⟩ := OMA757Dual.extract uniform deg G (fun _ _ => Iff.rfl) M hm
  refine ⟨T,sub,two,disj,?_⟩
  simp only [Nat.card_eq_fintype_card,Fintype.card_coe] at hsize
  omega
