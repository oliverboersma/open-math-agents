import FormalConjectures.ErdosProblems.«151»
import Mathlib

-- Credit: @FelixDou

/-! A vertex can be put back in an edge colouring if every component of its
neighbourhood becomes bipartite on removal of at most one edge. This is the
sufficient direction of the adaptable two-colouring criterion of Hell and Zhu.
Independently, a block B can be deleted if some A inside it is protected
by B minus A and pays for the exact increase in the Ramsey threshold.
The edge-colouring-to-transversal argument is from dk8827's first reduction.
The block argument extends abduljaleel's independent-neighbourhood proposal. -/

open Finset SimpleGraph
open scoped Classical

namespace OMA.R_Erdos151_erdos_151_variants_cliqueFree_four_R3

/-- Local extension for components with at most one exceptional edge each.
The two endpoints may coincide in a bipartite component. -/
def H1 : Prop :=
  ∀ (V : Type) (L : SimpleGraph V),
    (∀ C : L.ConnectedComponent, ∃ (side : V → Bool) (a b : V),
      ∀ x y, L.Adj x y → L.connectedComponentMk x = C → side x = side y →
        (x = a ∧ y = b) ∨ (x = b ∧ y = a)) →
    ∀ c : V → V → Bool, (∀ x y, c x y = c y x) →
      ∃ d : V → Bool, ∀ x y, L.Adj x y → ¬ (d x = c x y ∧ d y = c x y)

/-- The residual graphs resist all deletions of nonempty blocks of at most half the vertices and have a nonempty
induced subgraph in which each vertex has a neighbourhood component that
cannot be made bipartite by deleting one edge. -/
def H2 : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)), G.CliqueFree 4 →
    (∀ v, (univ.filter (G.Adj v)).card < Erdos151.H n) →
    (∀ A B : Finset (Fin n), B.Nonempty → 2 * B.card ≤ n → A ⊆ B →
      (∀ t, G.IsBigMaximalClique t → (∃ x ∈ t, x ∈ A) → ∃ y ∈ t, y ∈ B \ A) →
      A.card + Erdos151.H (n - B.card) < Erdos151.H n) →
    (∃ S : Finset (Fin n), S.Nonempty ∧ ∀ v ∈ S,
      let L := G.induce (↑(S.filter (G.Adj v)) : Set (Fin n))
      ∃ C : L.ConnectedComponent, ¬ ∃ (side : ↥(S.filter (G.Adj v)) → Bool)
        (a b : ↥(S.filter (G.Adj v))), ∀ x y, L.Adj x y →
          L.connectedComponentMk x = C → side x = side y →
            (x = a ∧ y = b) ∨ (x = b ∧ y = a)) →
    G.cliqueTransversalNumber ≤ n - Erdos151.H n


section Proof

/-- Orient each component so its exceptional edge disagrees with the colour
of its endpoints. The argument works for infinite components as well. -/
theorem component_coloring : H1 := by
  intro V L hp c hc
  classical
  choose side a b hs using hp
  let adapt (C : L.ConnectedComponent) (x : V) :=
    if side C x = side C (a C) then !(c (a C) (b C)) else c (a C) (b C)
  refine ⟨fun x => adapt (L.connectedComponentMk x) x, ?_⟩
  intro x y hxy
  let C := L.connectedComponentMk x
  have he : L.connectedComponentMk y = C :=
    (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hxy).symm
  change ¬ (adapt C x = c x y ∧ adapt (L.connectedComponentMk y) y = c x y)
  rw [he]
  rintro ⟨hx, hy⟩
  have inj (i j r k : Bool) :
      (if i = r then !k else k) = (if j = r then !k else k) → i = j := by
    cases i <;> cases j <;> cases r <;> cases k <;> decide
  have hside := inj (side C x) (side C y) (side C (a C)) (c (a C) (b C)) (hx.trans hy.symm)
  have flip (k : Bool) : (!k) ≠ k := by cases k <;> decide
  rcases hs C x y hxy rfl hside with ⟨hxa, hyb⟩ | ⟨hxb, hya⟩
  · have hx' := hx
    rw [show adapt C x = !(c (a C) (b C)) by simp [adapt, hxa]] at hx'
    rw [hxa, hyb] at hx'
    exact flip _ hx'
  · have hy' := hy
    rw [show adapt C y = !(c (a C) (b C)) by simp [adapt, hya]] at hy'
    rw [hxb, hya, hc (b C) (a C)] at hy'
    exact flip _ hy'


private theorem H_attained {n : ℕ} (F : SimpleGraph (Fin n)) (hF : F.CliqueFree 3) :
    ∃ s, F.IsNIndepSet (Erdos151.H n) s := by
  let sizes : Set ℕ :=
    {k | ∀ G : SimpleGraph (Fin n), G.CliqueFree 3 → ∃ s, G.IsNIndepSet k s}
  have hnonempty : sizes.Nonempty := by
    refine ⟨0, ?_⟩
    intro G _
    exact ⟨∅,by simp [SimpleGraph.isNIndepSet_iff]⟩
  have hfinite : sizes.Finite := by
    refine (Set.finite_Iic n).subset ?_
    intro k hk
    obtain ⟨s,hs⟩ := hk F hF
    simpa [hs.card_eq] using Finset.card_le_univ s
  have hmem : Erdos151.H n ∈ sizes := hnonempty.csSup_mem hfinite
  exact hmem F hF


private theorem neighborhood_bound {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n)
    (hv : Erdos151.H n ≤ (univ.filter (G.Adj v)).card) :
    cliqueTransversalNumber G ≤ n - Erdos151.H n := by
  let N := univ.filter (G.Adj v)
  have hhit : G.IsCliqueTransversal Nᶜ := by
    intro t ht
    by_contra! h
    have hAdj (w : Fin n) (hw : w ∈ t) : G.Adj v w :=
      (mem_filter.mp (not_not.mp (by simpa only [mem_compl] using h w hw))).2
    have hc : G.IsClique (↑(insert v t) : Set (Fin n)) := by
      rw [coe_insert]
      exact ht.1.1.insert (fun w hw _ => hAdj w hw)
    have hv' : v ∈ t := ht.1.2 hc (subset_insert _ _) (mem_insert_self _ _)
    exact G.irrefl (hAdj v hv')
  refine (csInf_le' (show Nᶜ.card ∈ {k | ∃ T, G.IsCliqueTransversal T ∧ T.card=k}
    from ⟨Nᶜ,hhit,rfl⟩)).trans ?_
  rw [card_compl,Fintype.card_fin]
  exact Nat.sub_le_sub_left hv n

lemma pullback_big_clique {m n : ℕ} (G : SimpleGraph (Fin n)) (e : Fin m ↪ Fin n)
    (t : Finset (Fin n)) (ht : G.IsBigMaximalClique t)
    (hr : ∀ x ∈ t, ∃ i, e i = x) :
    (G.comap e).IsBigMaximalClique (t.preimage e e.injective.injOn) := by
  classical
  let u := t.preimage e e.injective.injOn
  have heq : u.map e = t := by
    ext x
    constructor
    · intro hx
      obtain ⟨i, hi, rfl⟩ := mem_map.mp hx
      exact mem_preimage.mp hi
    · intro hx
      obtain ⟨i, rfl⟩ := hr x hx
      exact mem_map.mpr ⟨i, mem_preimage.mpr hx, rfl⟩
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro i hi j hj hij
    exact ht.1.1 (mem_preimage.mp hi) (mem_preimage.mp hj) (e.injective.ne hij)
  · intro w hw huw j hj
    have hc : G.IsClique (↑(w.map e) : Set (Fin n)) := by
      intro x hx y hy hxy
      obtain ⟨i, hi, rfl⟩ := mem_map.mp hx
      obtain ⟨k, hk, rfl⟩ := mem_map.mp hy
      exact hw hi hk (fun h => hxy (congrArg e h))
    have hsub : t ⊆ w.map e := by
      rw [← heq]
      exact map_subset_map.mpr huw
    exact mem_preimage.mpr (ht.1.2 hc hsub (mem_map.mpr ⟨j, hj, rfl⟩))
  · have h := ht.2
    rwa [← heq, card_map] at h

/-- Combining a transversal in the complement of a block with its guards
costs at most one vertex for each guard. -/
lemma delete_block {n : ℕ} (G : SimpleGraph (Fin n))
    (A B : Finset (Fin n)) (hAB : A ⊆ B)
    (guarded : ∀ t, G.IsBigMaximalClique t → (∃ x ∈ t, x ∈ A) → ∃ y ∈ t, y ∈ B \ A)
    (e : Fin (n - B.card) ↪ Fin n)
    (cover : ∀ x, x ∉ B → ∃ i, e i = x) :
    G.cliqueTransversalNumber ≤ (G.comap e).cliqueTransversalNumber + (B.card - A.card) := by
  classical
  let F := G.comap e
  have hn : {k | ∃ T : Finset (Fin (n - B.card)), F.IsCliqueTransversal T ∧ T.card = k}.Nonempty := by
    refine ⟨univ.card, univ, ?_, rfl⟩
    intro t ht
    obtain ⟨x, _, hx, _, _⟩ := one_lt_card_iff.mp ht.2
    exact ⟨x, hx, mem_univ _⟩
  obtain ⟨T, hT, hsize⟩ := Nat.sInf_mem hn
  change T.card = F.cliqueTransversalNumber at hsize
  let U := T.map e ∪ (B \ A)
  have hU : G.IsCliqueTransversal U := by
    intro t ht
    by_cases hhit : ∃ y ∈ t, y ∈ B \ A
    · obtain ⟨y, hy, hmem⟩ := hhit
      exact ⟨y, hy, mem_union_right _ hmem⟩
    have hout (x) (hx : x ∈ t) : x ∉ B := by
      intro hb
      by_cases ha : x ∈ A
      · exact hhit (guarded t ht ⟨x, hx, ha⟩)
      · exact hhit ⟨x, hx, mem_sdiff.mpr ⟨hb, ha⟩⟩
    have hbig := pullback_big_clique G e t ht (fun x hx => cover x (hout x hx))
    obtain ⟨i, hi, hiT⟩ := hT _ hbig
    exact ⟨e i, mem_preimage.mp hi, mem_union_left _ (mem_map.mpr ⟨i, hiT, rfl⟩)⟩
  calc
    G.cliqueTransversalNumber ≤ U.card := csInf_le' ⟨U, hU, rfl⟩
    _ ≤ (T.map e).card + (B \ A).card := card_union_le _ _
    _ = _ := by rw [card_map, card_sdiff_of_subset hAB, hsize]


lemma edge_coloring_of_links {n : ℕ} (G : SimpleGraph (Fin n)) (h1 : H1)
    (peel : ∀ S : Finset (Fin n), S.Nonempty → ∃ v ∈ S,
      let L := G.induce (↑(S.filter (G.Adj v)) : Set (Fin n))
      ∀ C : L.ConnectedComponent, ∃ (side : ↥(S.filter (G.Adj v)) → Bool)
        (a b : ↥(S.filter (G.Adj v))), ∀ x y, L.Adj x y →
          L.connectedComponentMk x = C → side x = side y →
            (x = a ∧ y = b) ∨ (x = b ∧ y = a)) :
    ∃ c : Fin n → Fin n → Bool, (∀ x y, c x y = c y x) ∧
      ∀ x y z, G.Adj x y → G.Adj x z → G.Adj y z →
        ∀ b, ¬ (c x y = b ∧ c x z = b ∧ c y z = b) := by
  classical
  have aux : ∀ S : Finset (Fin n),
      ∃ c : Fin n → Fin n → Bool, (∀ x y, c x y = c y x) ∧
        ∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S, G.Adj x y → G.Adj x z → G.Adj y z →
          ∀ b, ¬ (c x y = b ∧ c x z = b ∧ c y z = b) := by
    intro S
    induction S using Finset.strongInductionOn with
    | _ S ih =>
      by_cases hS : S.Nonempty
      swap
      · exact ⟨fun _ _ => false, fun _ _ => rfl, fun x hx => (hS ⟨x, hx⟩).elim⟩
      obtain ⟨v, hv, hp⟩ := peel S hS
      obtain ⟨c, hcs, hc⟩ := ih (S.erase v) (erase_ssubset hv)
      let N := S.filter (G.Adj v)
      let L := G.induce (↑N : Set (Fin n))
      obtain ⟨d, hd⟩ := h1 (↥N) L hp (fun x y => c x.val y.val) (fun x y => hcs _ _)
      let p (x : Fin n) := if hx : x ∈ N then d ⟨x,hx⟩ else false
      let c' (x y : Fin n) := if x = v then p y else if y = v then p x else c x y
      have hcs' (x y : Fin n) : c' x y = c' y x := by
        by_cases hx : x = v <;> by_cases hy : y = v <;> simp [c', hx, hy, hcs]
      have hAt {y z : Fin n} (hy : y ∈ S) (hz : z ∈ S)
          (hvy : G.Adj v y) (hvz : G.Adj v z) (hyz : G.Adj y z) (b : Bool) :
          ¬ (c' v y = b ∧ c' v z = b ∧ c' y z = b) := by
        have hyv := hvy.ne.symm
        have hzv := hvz.ne.symm
        have hyN : y ∈ N := mem_filter.mpr ⟨hy, hvy⟩
        have hzN : z ∈ N := mem_filter.mpr ⟨hz, hvz⟩
        have hD := hd ⟨y,hyN⟩ ⟨z,hzN⟩ hyz
        rintro ⟨h₁,h₂,h₃⟩
        simp only [c',if_pos rfl,p,dif_pos hyN,dif_pos hzN,if_neg hyv,if_neg hzv] at h₁ h₂ h₃
        exact hD ⟨h₁.trans h₃.symm,h₂.trans h₃.symm⟩


      refine ⟨c',hcs',?_⟩
      intro x hx y hy z hz hxy hxz hyz b h
      by_cases hxv : x = v
      · subst x
        exact hAt hy hz hxy hxz hyz b h
      by_cases hyv : y = v
      · subst y
        exact hAt hx hz hxy.symm hyz hxz b
          ⟨(hcs' _ _).trans h.1,h.2.2,h.2.1⟩
      by_cases hzv : z = v
      · subst z
        exact hAt hx hy hxz.symm hyz.symm hxy b
          ⟨(hcs' _ _).trans h.2.1,(hcs' _ _).trans h.2.2,h.1⟩
      simp only [c',if_neg hxv,if_neg hyv,if_neg hzv] at h
      exact hc x (mem_erase.mpr ⟨hxv,hx⟩) y (mem_erase.mpr ⟨hyv,hy⟩)
        z (mem_erase.mpr ⟨hzv,hz⟩) hxy hxz hyz b h
  obtain ⟨c,hs,hc⟩ := aux univ
  exact ⟨c,hs,fun x y z => hc x (mem_univ _) y (mem_univ _) z (mem_univ _)⟩

private theorem transversal_of_edge_coloring {n : ℕ} (G : SimpleGraph (Fin n))
    (c : Fin n → Fin n → Bool) (hs : ∀ x y, c x y = c y x)
    (hc : ∀ x y z, G.Adj x y → G.Adj x z → G.Adj y z →
      ∀ b, ¬ (c x y = b ∧ c x z = b ∧ c y z = b)) :
    cliqueTransversalNumber G ≤ n - Erdos151.H n := by
  let F : SimpleGraph (Fin n) := {
    Adj := fun x y => G.Adj x y ∧ (c x y = true ∨ ¬ ∃ w, G.Adj x w ∧ G.Adj y w)
    symm := ⟨fun _ _ h => ⟨h.1.symm,h.2.elim (fun h => Or.inl ((hs _ _).trans h))
      (fun h => Or.inr (fun ⟨w,hw,hw'⟩ => h ⟨w,hw',hw⟩))⟩⟩
    loopless := ⟨fun _ h => G.irrefl h.1⟩ }
  have hF : F.CliqueFree 3 := by
    intro t h
    obtain ⟨x,y,z,hxy,hxz,hyz,-⟩ := is3Clique_iff.mp h
    exact hc x y z hxy.1 hxz.1 hyz.1 true
      ⟨hxy.2.resolve_right (fun h => h ⟨z,hxz.1,hyz.1⟩),
        hxz.2.resolve_right (fun h => h ⟨y,hxy.1,hyz.1.symm⟩),
        hyz.2.resolve_right (fun h => h ⟨x,hxy.1.symm,hxz.1.symm⟩)⟩
  obtain ⟨I,hI⟩ := H_attained F hF
  have hhit : G.IsCliqueTransversal Iᶜ := by
    intro t ht
    by_contra! h
    have hIn {x : Fin n} (hx : x ∈ t) : x ∈ I := by simpa using h x hx
    have hNo {x y : Fin n} (hx : x ∈ t) (hy : y ∈ t) (hxy : G.Adj x y) :
        c x y = false := by
      cases hb : c x y
      · rfl
      · exact (hI.isIndepSet (hIn hx) (hIn hy) hxy.ne ⟨hxy,Or.inl hb⟩).elim
    have hNotThree : t.card < 3 := by
      by_contra! hLarge
      obtain ⟨u,hu,huC⟩ := exists_subset_card_eq hLarge
      have hClique : G.IsNClique 3 u :=
        ⟨fun _ hx _ hy hxy => ht.1.1 (hu hx) (hu hy) hxy,huC⟩
      obtain ⟨x,y,z,hxy,hxz,hyz,rfl⟩ := is3Clique_iff.mp hClique
      have hx : x ∈ t := hu (by simp)
      have hy : y ∈ t := hu (by simp)
      have hz : z ∈ t := hu (by simp)
      exact hc x y z hxy hxz hyz false ⟨hNo hx hy hxy,hNo hx hz hxz,hNo hy hz hyz⟩
    have hTwo : t.card = 2 := by have := ht.2; omega
    obtain ⟨x,y,hxy,htxy⟩ := card_eq_two.mp hTwo
    have hx : x ∈ t := by simp [htxy]
    have hy : y ∈ t := by simp [htxy]
    have hAdj := ht.1.1 hx hy hxy
    have hN : ¬ ∃ w, G.Adj x w ∧ G.Adj y w := by
      rintro ⟨w,hwx,hwy⟩
      have hSub : G.IsClique (↑(insert w t) : Set (Fin n)) := by
        rw [coe_insert]
        apply ht.1.1.insert
        intro u hu _
        have : u = x ∨ u = y := by simpa [htxy] using hu
        exact this.elim (fun h => h ▸ hwx.symm) (fun h => h ▸ hwy.symm)
      have hwMem : w ∈ t := ht.1.2 hSub (subset_insert _ _) (mem_insert_self _ _)
      have : w = x ∨ w = y := by simpa [htxy] using hwMem
      exact this.elim hwx.ne.symm hwy.ne.symm
    exact hI.isIndepSet (hIn hx) (hIn hy) hxy ⟨hAdj,Or.inr hN⟩
  apply csInf_le'
  exact ⟨Iᶜ,hhit,by rw [card_compl,Fintype.card_fin,hI.card_eq]⟩


theorem main : H1 → H2 → type_of% @Erdos151.erdos_151.variants.cliqueFree_four := by
  classical
  intro h1 h2 n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro G hG
    by_cases hblock : ∃ A B : Finset (Fin n), B.Nonempty ∧ 2 * B.card ≤ n ∧ A ⊆ B ∧
        (∀ t, G.IsBigMaximalClique t → (∃ x ∈ t, x ∈ A) → ∃ y ∈ t, y ∈ B \ A) ∧
        Erdos151.H n ≤ A.card + Erdos151.H (n - B.card)
    · obtain ⟨A, B, hB, _, hAB, hg, hgain⟩ := hblock
      have hb : B.card ≤ n := by simpa using card_le_univ B
      have ha := card_le_card hAB
      have hbpos := card_pos.mpr hB
      let W := Bᶜ
      have hW : Fintype.card (↥W) = n - B.card := by simp [W]
      let f := Fintype.equivFinOfCardEq hW
      let e := f.symm.toEmbedding.trans (Function.Embedding.subtype (· ∈ W))
      have hcover (x : Fin n) (hx : x ∉ B) : ∃ i, e i = x := by
        let z : ↥W := ⟨x, mem_compl.mpr hx⟩
        exact ⟨f z, by simp [e, z]⟩
      have hsmall := ih (n - B.card) (by omega) (G.comap e)
        (CliqueFree.comap (SimpleGraph.Embedding.comap e G).isContained hG)
      have hdelete := delete_block G A B hAB hg e hcover
      obtain ⟨s, hs⟩ := H_attained (⊥ : SimpleGraph (Fin (n - B.card)))
        (cliqueFree_bot (by decide))
      have hH : Erdos151.H (n - B.card) ≤ n - B.card := by
        simpa [hs.card_eq] using card_le_univ s
      omega
    have strict : ∀ A B : Finset (Fin n), B.Nonempty → 2 * B.card ≤ n → A ⊆ B →
        (∀ t, G.IsBigMaximalClique t → (∃ x ∈ t, x ∈ A) → ∃ y ∈ t, y ∈ B \ A) →
        A.card + Erdos151.H (n - B.card) < Erdos151.H n := by
      intro A B hb hproper hab hg
      exact lt_of_not_ge (fun h => hblock ⟨A, B, hb, hproper, hab, hg, h⟩)
    by_cases hlarge : ∃ v, Erdos151.H n ≤ (univ.filter (G.Adj v)).card
    · obtain ⟨v, hv⟩ := hlarge
      exact neighborhood_bound G v hv
    have hdegree (v) : (univ.filter (G.Adj v)).card < Erdos151.H n :=
      lt_of_not_ge (fun h => hlarge ⟨v, h⟩)
    by_contra hbad
    obtain ⟨c, hs, hc⟩ := edge_coloring_of_links G h1 (by
      intro S hS
      by_contra hn
      apply hbad
      apply h2 n G hG hdegree strict
      refine ⟨S, hS, ?_⟩
      intro v hv
      apply not_forall.mp
      exact fun hall => hn ⟨v, hv, hall⟩)
    exact hbad (transversal_of_edge_coloring G c hs hc)

/-- Only the residual extremal case remains after the component argument. -/
theorem bound_of_residual : H2 → type_of% @Erdos151.erdos_151.variants.cliqueFree_four :=
  main component_coloring

end Proof

end OMA.R_Erdos151_erdos_151_variants_cliqueFree_four_R3
