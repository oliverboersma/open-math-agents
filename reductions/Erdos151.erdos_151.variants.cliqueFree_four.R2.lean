import FormalConjectures.ErdosProblems.«151»
import Mathlib

/-!
The edge count is local to each edge. A hypergraph whose edges are the
triangles of G admits a red-blue coloring when every graph edge belongs
to at most two triangles. This reduces the clique transversal bound
to an independence bound in a triangle-free graph.
-/

open Finset SimpleGraph
open scoped Classical

namespace OMA.R_Erdos151_erdos_151_variants_cliqueFree_four_R2

/-- Isolate the range where every triangle-free graph has guaranteed
independence number at most nine. -/
def H1 : Prop :=
  ∀ n, Erdos151.H n ≤ 9 → ∀ G : SimpleGraph (Fin n), G.CliqueFree 4 →
    cliqueTransversalNumber G ≤ n - Erdos151.H n

/-- The remaining graphs have no sufficiently large neighborhood and have
an edge in at least three triangles. -/
def H2 : Prop :=
  ∀ n, 10 ≤ Erdos151.H n → ∀ G : SimpleGraph (Fin n), G.CliqueFree 4 →
    (∀ v, (univ.filter (G.Adj v)).card < Erdos151.H n) →
    (∃ x y, G.Adj x y ∧ 3 ≤ (univ.filter fun z => G.Adj x z ∧ G.Adj y z).card) →
    cliqueTransversalNumber G ≤ n - Erdos151.H n

section Proof

variable {ι α : Type*} [DecidableEq ι] [DecidableEq α]

private theorem no_third (T : Finset ι) (E : ι → Finset α)
    (hDegree : ∀ x, (T.filter (fun t => x ∈ E t)).card ≤ 2)
    {t u v : ι} (ht : t ∈ T) (hu : u ∈ T) (hv : v ∈ T)
    (htu : t ≠ u) (htv : t ≠ v) (huv : u ≠ v)
    {x : α} (hxt : x ∈ E t) (hxu : x ∈ E u) (hxv : x ∈ E v) : False := by
  have hSub : ({t,u,v} : Finset ι) ⊆ T.filter (fun t => x ∈ E t) := by
    intro y hy
    simp only [mem_insert,mem_singleton] at hy
    rcases hy with rfl|rfl|rfl
    · exact mem_filter.mpr ⟨ht,hxt⟩
    · exact mem_filter.mpr ⟨hu,hxu⟩
    · exact mem_filter.mpr ⟨hv,hxv⟩
  have hh := (card_le_card hSub).trans (hDegree x)
  simp [htu,htv,huv] at hh

theorem red_blue (T : Finset ι) (E : ι → Finset α)
    (hSize : ∀ t ∈ T, (E t).card = 3)
    (hDegree : ∀ x, (T.filter (fun t => x ∈ E t)).card ≤ 2) :
    ∃ R : Finset α, ∀ t ∈ T, (∃ x ∈ E t, x ∈ R) ∧ (∃ y ∈ E t, y ∉ R) := by
  classical
  by_cases hT : T.Nonempty
  · obtain ⟨t0,ht0⟩ := hT
    let V := T.biUnion E
    let Good := V.powerset.filter (fun R => ∀ t ∈ T, (E t ∩ R).card ≤ 1)
    have hEmpty : ∅ ∈ Good := by simp [Good]
    obtain ⟨R,hR,hMax⟩ := exists_max_image Good card ⟨∅,hEmpty⟩
    have hRSub : R ⊆ V := mem_powerset.mp (mem_filter.mp hR).1
    have hRGood : ∀ t ∈ T, (E t ∩ R).card ≤ 1 := (mem_filter.mp hR).2
    let U := T.filter (fun t => E t ∩ R = ∅)
    have hUT : U ⊆ T := filter_subset _ _
    have hU0 (t : ι) (ht : t ∈ U) : E t ∩ R = ∅ := (mem_filter.mp ht).2
    have hVx {x : α} {t : ι} (ht : t ∈ T) (hx : x ∈ E t) : x ∈ V :=
      mem_biUnion.mpr ⟨t,ht,hx⟩
    have hNonRed {x : α} {t : ι} (ht : t ∈ U) (hx : x ∈ E t) : x ∉ R := by
      intro hr
      have hmem := mem_inter.mpr ⟨hx,hr⟩
      rw [hU0 t ht] at hmem
      exact notMem_empty _ hmem
    have hNeedsRed {x : α} (hx : x ∈ V) (hxR : x ∉ R) :
        ∃ t ∈ T, t ∉ U ∧ x ∈ E t := by
      by_contra! hf
      have hNew : insert x R ∈ Good := by
        refine mem_filter.mpr ⟨mem_powerset.mpr (insert_subset hx hRSub),?_⟩
        intro t ht
        by_cases he : x ∈ E t
        · have heq : E t ∩ insert x R = {x} := by
            ext y
            simp only [mem_inter,mem_insert,mem_singleton]
            constructor
            · rintro ⟨hy,rfl|hyR⟩
              · rfl
              · have hh : y ∈ E t ∩ R := mem_inter.mpr ⟨hy,hyR⟩
                rw [hU0 t (by by_contra hn; exact hf t ht hn he)] at hh
                exact (notMem_empty _ hh).elim
            · rintro rfl
              exact ⟨he,Or.inl rfl⟩
          rw [heq,card_singleton]
        · have heq : E t ∩ insert x R = E t ∩ R := by
            ext y
            simp only [mem_inter,mem_insert]
            grind
          rw [heq]
          exact hRGood t ht
      have hh := hMax _ hNew
      rw [card_insert_of_notMem hxR] at hh
      omega
    have hUDisjoint : (U : Set ι).PairwiseDisjoint E := by
      intro t ht u hu htu
      apply Finset.disjoint_left.mpr
      intro x hxt hxu
      obtain ⟨v,hv,hvU,hxv⟩ := hNeedsRed (hVx (hUT ht) hxt) (hNonRed ht hxt)
      exact no_third T E hDegree (hUT ht) (hUT hu) hv htu
        (fun he => hvU (he ▸ ht)) (fun he => hvU (he ▸ hu)) hxt hxu hxv
    let key (x : α) : ι :=
      if h : ∃ t ∈ T, t ∉ U ∧ x ∈ E t then h.choose else t0
    have hKey {t : ι} (ht : t ∈ U) {x : α} (hx : x ∈ E t) :
        key x ∈ T ∧ key x ∉ U ∧ x ∈ E (key x) := by
      have h := hNeedsRed (hVx (hUT ht) hx) (hNonRed ht hx)
      exact by simpa only [key,dif_pos h] using h.choose_spec
    have hKeyEq {t u : ι} (ht : t ∈ U) (hu : u ∈ T) (huU : u ∉ U)
        {x : α} (hx : x ∈ E t) (hxu : x ∈ E u) : key x = u := by
      obtain ⟨hk,hkU,hxk⟩ := hKey ht hx
      by_contra hne
      exact no_third T E hDegree (hUT ht) hk hu (fun he => hkU (he ▸ ht))
        (fun he => huU (he ▸ ht)) hne hx hxk hxu
    have hOtherCard {u : ι} (hu : u ∈ T) (huU : u ∉ U) : (E u \ R).card = 2 := by
      have hh := card_sdiff_add_card_inter (E u) R
      have hp : 0 < (E u ∩ R).card := card_pos.mpr (by
        apply nonempty_iff_ne_empty.mpr
        exact fun h => huU (mem_filter.mpr ⟨hu,h⟩))
      have hh' := hRGood u hu
      rw [hSize u hu] at hh
      omega
    let options (t : U) : Finset ι := (E t.val).image key
    have hHall : ∀ S : Finset U, S.card ≤ (S.biUnion options).card := by
      intro S
      let W := S.biUnion (fun t => E t.val)
      have hWsize : W.card = 3*S.card := by
        rw [card_biUnion (show (S : Set U).PairwiseDisjoint (fun t => E t.val) from by
          intro t ht u hu hn
          exact hUDisjoint t.property u.property (fun he => hn (Subtype.ext he)))]
        simp [fun t : U => hSize t.val (hUT t.property),mul_comm]
      have hOpts : S.biUnion options = W.image key := by
        ext u
        constructor
        · intro hu
          obtain ⟨t,ht,htu⟩ := mem_biUnion.mp hu
          obtain ⟨x,hx,rfl⟩ := mem_image.mp htu
          exact mem_image.mpr ⟨x,mem_biUnion.mpr ⟨t,ht,hx⟩,rfl⟩
        · intro hu
          obtain ⟨x,hx,rfl⟩ := mem_image.mp hu
          obtain ⟨t,ht,hxt⟩ := mem_biUnion.mp hx
          exact mem_biUnion.mpr ⟨t,ht,mem_image_of_mem key hxt⟩
      have hFiber (u : ι) (hu : u ∈ W.image key) :
          (W.filter (fun x => key x = u)).card ≤ 2 := by
        obtain ⟨x,hx,rfl⟩ := mem_image.mp hu
        obtain ⟨t,ht,hxt⟩ := mem_biUnion.mp hx
        have hk := hKey t.property hxt
        rw [← hOtherCard hk.1 hk.2.1]
        apply card_le_card
        intro y hy
        obtain ⟨hy,hey⟩ := mem_filter.mp hy
        obtain ⟨u,hu,hyu⟩ := mem_biUnion.mp hy
        exact mem_sdiff.mpr ⟨hey ▸ (hKey u.property hyu).2.2,hNonRed u.property hyu⟩
      have hcount : W.card ≤ 2*(W.image key).card := by
        rw [card_eq_sum_card_fiberwise (fun x hx => mem_image_of_mem key hx)]
        calc
          _ ≤ ∑ _u ∈ W.image key, 2 := sum_le_sum hFiber
          _ = _ := by simp [mul_comm]
      rw [hOpts]
      omega
    obtain ⟨f,hInj,hf⟩ := (all_card_le_biUnion_card_iff_exists_injective options).mp hHall
    let chosen (t : U) := (mem_image.mp (hf t)).choose
    have hChosen (t : U) : chosen t ∈ E t.val ∧ key (chosen t) = f t :=
      (mem_image.mp (hf t)).choose_spec
    let Add := univ.image chosen
    refine ⟨R ∪ Add,?_⟩
    intro t ht
    have hAtMost : (E t ∩ Add).card ≤ 1 := by
      apply card_le_one.mpr
      intro x hx y hy
      obtain ⟨hxT,hxA⟩ := mem_inter.mp hx
      obtain ⟨hyT,hyA⟩ := mem_inter.mp hy
      obtain ⟨u,_,rfl⟩ := mem_image.mp hxA
      obtain ⟨v,_,rfl⟩ := mem_image.mp hyA
      congr 1
      by_cases htU : t ∈ U
      · have hu : u = ⟨t,htU⟩ := by
          by_contra hn
          exact (Finset.disjoint_left.mp (hUDisjoint u.property htU
            (fun he => hn (Subtype.ext he)))) (hChosen u).1 hxT
        have hv : v = ⟨t,htU⟩ := by
          by_contra hn
          exact (Finset.disjoint_left.mp (hUDisjoint v.property htU
            (fun he => hn (Subtype.ext he)))) (hChosen v).1 hyT
        exact hu.trans hv.symm
      · apply hInj
        exact (hChosen u).2.symm.trans ((hKeyEq u.property ht htU (hChosen u).1 hxT).trans
          ((hKeyEq v.property ht htU (hChosen v).1 hyT).symm.trans (hChosen v).2))
    have hRed : (E t ∩ (R ∪ Add)).card ≤ 2 := by
      rw [inter_union_distrib_left]
      exact (card_union_le _ _).trans (by have := hRGood t ht; omega)
    constructor
    · by_cases htU : t ∈ U
      · let u : U := ⟨t,htU⟩
        exact ⟨chosen u,(hChosen u).1,mem_union_right _ (mem_image_of_mem _ (mem_univ u))⟩
      · have hMem : (E t ∩ R).Nonempty := nonempty_iff_ne_empty.mpr
          (fun h => htU (mem_filter.mpr ⟨ht,h⟩))
        obtain ⟨x,hx⟩ := hMem
        exact ⟨x,(mem_inter.mp hx).1,mem_union_left _ (mem_inter.mp hx).2⟩
    · by_contra! hn
      have he : E t ∩ (R ∪ Add) = E t := inter_eq_left.mpr hn
      rw [he,hSize t ht] at hRed
      omega
  · exact ⟨∅,by simp [not_nonempty_iff_eq_empty.mp hT]⟩


section Triangles

open SimpleGraph

variable {n : ℕ} (G : SimpleGraph (Fin n))

private theorem three_edge_set [DecidableRel G.Adj] {a b c : Fin n}
    (hab : G.Adj a b) (hac : G.Adj a c) (hbc : G.Adj b c) :
    ({a,b,c} : Finset (Fin n)).sym2 ∩ G.edgeFinset =
      ({s(a,b),s(a,c),s(b,c)} : Finset (Sym2 (Fin n))) := by
  apply Subset.antisymm
  · simp only [subset_iff,Sym2.forall,mem_inter,mk_mem_sym2_iff,mem_insert,
      mem_edgeFinset,mem_singleton,mem_edgeSet,and_imp]
    rintro d e (rfl|rfl|rfl) (rfl|rfl|rfl) h <;> simp [*] at *
  · simp [insert_subset,mem_inter,mem_edgeFinset,hab,hac,hbc]

private theorem triangle_edge_coloring [DecidableRel G.Adj]
    (hCount : ∀ x y, G.Adj x y → (G.neighborFinset x ∩ G.neighborFinset y).card ≤ 2) :
    ∃ c : Fin n → Fin n → Bool, (∀ x y, c x y = c y x) ∧
      ∀ x y z, G.Adj x y → G.Adj x z → G.Adj y z →
        ∀ b, ¬ (c x y = b ∧ c x z = b ∧ c y z = b) := by
  classical
  let T := G.cliqueFinset 3
  let E (t : Finset (Fin n)) := t.sym2 ∩ G.edgeFinset
  have hSize (t : Finset (Fin n)) (ht : t ∈ T) : (E t).card = 3 := by
    obtain ⟨a,b,c,hab,hac,hbc,rfl⟩ := is3Clique_iff.mp (mem_cliqueFinset_iff.mp ht)
    rw [show E {a,b,c} = {s(a,b),s(a,c),s(b,c)} from three_edge_set G hab hac hbc]
    refine card_eq_three.mpr ⟨_,_,_,?_,?_,?_,rfl⟩ <;> simp [hab.ne,hac.ne,hbc.ne]
  have hDegree (e : Sym2 (Fin n)) : (T.filter fun t => e ∈ E t).card ≤ 2 := by
    rcases Sym2.mk_surjective e with ⟨⟨x,y⟩,rfl⟩
    by_cases hxy : G.Adj x y
    · let N := G.neighborFinset x ∩ G.neighborFinset y
      have hSub : (T.filter fun t => s(x,y) ∈ E t) ⊆ N.image (fun z => {x,y,z}) := by
        intro t ht
        obtain ⟨ht,hEdge⟩ := mem_filter.mp ht
        have htG := mem_cliqueFinset_iff.mp ht
        have ⟨hx,hy⟩ := mk_mem_sym2_iff.mp (mem_inter.mp hEdge).1
        have hsmall : ({x,y} : Finset (Fin n)).card < t.card := by
          rw [htG.card_eq,card_pair hxy.ne]
          decide
        obtain ⟨z,hz,hzp⟩ := exists_mem_notMem_of_card_lt_card hsmall
        have hzx : z ≠ x := fun h => hzp (by simp [h])
        have hzy : z ≠ y := fun h => hzp (by simp [h])
        have hSet : ({x,y,z} : Finset (Fin n)) = t := by
          apply eq_of_subset_of_card_le (by simp [insert_subset,hx,hy,hz])
          rw [htG.card_eq,card_insert_of_notMem (by simp [hxy.ne,hzx.symm]),card_pair hzy.symm]
        exact mem_image.mpr ⟨z,mem_inter.mpr ⟨(G.mem_neighborFinset x z).mpr
          (htG.isClique hx hz hzx.symm),(G.mem_neighborFinset y z).mpr
          (htG.isClique hy hz hzy.symm)⟩,hSet⟩
      exact ((card_le_card hSub).trans card_image_le).trans (hCount x y hxy)
    · have he : s(x,y) ∉ G.edgeFinset := by simpa using hxy
      have hNone : (T.filter fun t => s(x,y) ∈ E t) = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro t ht
        exact he (mem_inter.mp (mem_filter.mp ht).2).2
      change (T.filter fun t => s(x,y) ∈ E t).card ≤ 2
      rw [hNone,card_empty]
      norm_num
  obtain ⟨R,hR⟩ := red_blue T E hSize hDegree
  let c (x y : Fin n) : Bool := decide (s(x,y) ∈ R)
  refine ⟨c,?_ ,?_⟩
  · intro x y
    unfold c
    rw [Sym2.eq_swap]
  · intro x y z hxy hxz hyz b hMono
    let t : Finset (Fin n) := {x,y,z}
    have ht : t ∈ T := mem_cliqueFinset_iff.mpr (is3Clique_triple_iff.mpr ⟨hxy,hxz,hyz⟩)
    have hE : E t = {s(x,y),s(x,z),s(y,z)} := three_edge_set G hxy hxz hyz
    obtain ⟨⟨r,hr,hrR⟩,⟨q,hq,hqR⟩⟩ := hR t ht
    cases b with
    | false =>
      have hnot (u v : Fin n) (hb : c u v = false) : s(u,v) ∉ R := by
        simpa [c] using hb
      simp only [hE,mem_insert,mem_singleton] at hr
      rcases hr with rfl|rfl|rfl
      · exact (hnot x y hMono.1) hrR
      · exact (hnot x z hMono.2.1) hrR
      · exact (hnot y z hMono.2.2) hrR
    | true =>
      have hmem (u v : Fin n) (hb : c u v = true) : s(u,v) ∈ R := by
        simpa [c] using hb
      simp only [hE,mem_insert,mem_singleton] at hq
      rcases hq with rfl|rfl|rfl
      · exact hqR (hmem x y hMono.1)
      · exact hqR (hmem x z hMono.2.1)
      · exact hqR (hmem y z hMono.2.2)

end Triangles

open SimpleGraph

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


theorem transversal_of_two_triangles {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hCount : ∀ x y, G.Adj x y → (G.neighborFinset x ∩ G.neighborFinset y).card ≤ 2) :
    cliqueTransversalNumber G ≤ n - Erdos151.H n := by
  obtain ⟨c,hs,hc⟩ := triangle_edge_coloring G hCount
  exact transversal_of_edge_coloring G c hs hc

private theorem neighborhood_bound {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (v : Fin n) (hv : Erdos151.H n ≤ G.degree v) :
    cliqueTransversalNumber G ≤ n - Erdos151.H n := by
  let N := G.neighborFinset v
  have hhit : G.IsCliqueTransversal Nᶜ := by
    intro t ht
    by_contra! h
    have hAdj (w : Fin n) (hw : w ∈ t) : G.Adj v w :=
      (G.mem_neighborFinset v w).mp (not_not.mp (by simpa only [mem_compl] using h w hw))
    have hc : G.IsClique (↑(insert v t) : Set (Fin n)) := by
      rw [coe_insert]
      exact ht.1.1.insert (fun w hw _ => hAdj w hw)
    have hv' : v ∈ t := ht.1.2 hc (subset_insert _ _) (mem_insert_self _ _)
    exact G.irrefl (hAdj v hv')
  refine (csInf_le' (show Nᶜ.card ∈ {k | ∃ T, G.IsCliqueTransversal T ∧ T.card=k}
    from ⟨Nᶜ,hhit,rfl⟩)).trans ?_
  rw [card_compl,Fintype.card_fin]
  exact Nat.sub_le_sub_left hv n

theorem main : H1 → H2 → type_of% @Erdos151.erdos_151.variants.cliqueFree_four := by
  intro hSmall hLarge n G hG
  by_cases hH : Erdos151.H n ≤ 9
  · exact hSmall n hH G hG
  by_cases hDeg : ∃ v : Fin n, Erdos151.H n ≤ G.degree v
  · obtain ⟨v,hv⟩ := hDeg
    exact neighborhood_bound G v hv
  by_cases hTri :
      ∀ x y, G.Adj x y → (G.neighborFinset x ∩ G.neighborFinset y).card ≤ 2
  · exact transversal_of_two_triangles G hTri
  push Not at hTri
  obtain ⟨x,y,hxy,hCount⟩ := hTri
  apply hLarge n (by omega) G hG
  · intro v
    have hv := Nat.lt_of_not_ge (fun h => hDeg ⟨v,h⟩)
    rw [← SimpleGraph.neighborFinset_eq_filter, G.card_neighborFinset_eq_degree]
    exact hv
  · refine ⟨x,y,hxy,?_⟩
    have hSet : (univ.filter fun z => G.Adj x z ∧ G.Adj y z) =
        G.neighborFinset x ∩ G.neighborFinset y := by
      ext z
      simp
    rw [hSet]
    omega

end Proof

end OMA.R_Erdos151_erdos_151_variants_cliqueFree_four_R2
