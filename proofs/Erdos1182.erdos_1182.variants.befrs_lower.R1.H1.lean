import OMAReductions.R_Erdos1182_erdos_1182_variants_befrs_lower_R1
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Logic.Equiv.Fintype

/-!
# Sparse core reduction for Erdős Problem 1182 (BEFRS lower bound, R1.H1)

Assembled from `R1.H1.R1` and its leaf proofs `R1.H1.R1.H1` and `R1.H1.R1.H2`.
Credit: @dk8827.

Separates the two local graph operations (leaf deletion and suspended-path
contraction) used to compress a connected graph to a sparse core without
degree-1 vertices or adjacent degree-2 vertices.
-/

namespace OMA.Erdos1182BefrsLowerR1H1

namespace R1H1R1

open SimpleGraph
open scoped BigOperators

/-- Deleting a leaf from a connected graph preserves the obstruction if
the host is large enough for the leaf extension argument. -/
def H1 : Prop :=
  ∀ {l m : ℕ} (G : SimpleGraph (Fin l)) (C : SimpleGraph (Fin m)),
    4 ≤ l → 2 * l - 1 ≤ m → G.Connected → C.CliqueFree 3 →
    (∃ x, (G.neighborSet x).ncard = 1) →
    ∃ H : SimpleGraph (Fin (l - 1)), H.Connected ∧
      H.edgeSet.ncard + 1 ≤ G.edgeSet.ncard ∧ (H.IsContained Cᶜ → G.IsContained Cᶜ)

/-- Shortening a suspended path with adjacent degree-two vertices preserves the
obstruction. If the two other endpoints coincide, replace the triangle by a leaf. -/
def H2 : Prop :=
  ∀ {l m : ℕ} (G : SimpleGraph (Fin l)) (C : SimpleGraph (Fin m)),
    4 ≤ l → 2 * l - 1 ≤ m → G.Connected → C.CliqueFree 3 →
    (∃ x y, G.Adj x y ∧ (G.neighborSet x).ncard = 2 ∧ (G.neighborSet y).ncard = 2) →
    ∃ H : SimpleGraph (Fin (l - 1)), H.Connected ∧
      H.edgeSet.ncard + 1 ≤ G.edgeSet.ncard ∧ (H.IsContained Cᶜ → G.IsContained Cᶜ)

theorem blueTriangle {m : ℕ} (C : SimpleGraph (Fin m)) (hm : 6 ≤ m)
    (hC : C.CliqueFree 3) : (⊤ : SimpleGraph (Fin 3)).IsContained Cᶜ := by
  classical
  apply (not_cliqueFree_iff_top_isContained 3).mp
  intro hblue
  let v : Fin m := ⟨0, by omega⟩
  by_cases hred : 3 ≤ (C.neighborFinset v).card
  · obtain ⟨S, hS, hscard⟩ := Finset.exists_subset_card_eq hred
    let p := S.orderEmbOfFin hscard
    have hadj (i : Fin 3) : C.Adj v (p i) :=
      (mem_neighborFinset C v _).mp (hS (S.orderEmbOfFin_mem hscard i))
    have hpair (i j : Fin 3) (hij : i ≠ j) : Cᶜ.Adj (p i) (p j) := by
      rw [compl_adj]
      exact ⟨p.injective.ne hij, fun h => hC _ (is3Clique_triple_iff.mpr ⟨hadj i, hadj j, h⟩)⟩
    exact hblue _ (is3Clique_triple_iff.mpr
      ⟨hpair 0 1 (by decide), hpair 0 2 (by decide), hpair 1 2 (by decide)⟩)
  · have hdeg := C.degree_compl (v := v)
    have hdeg' : (Cᶜ.neighborFinset v).card = m - 1 - (C.neighborFinset v).card := by
      simpa only [Fintype.card_fin, card_neighborFinset_eq_degree] using hdeg
    have hlarge : 3 ≤ (Cᶜ.neighborFinset v).card := by omega
    obtain ⟨S, hS, hscard⟩ := Finset.exists_subset_card_eq hlarge
    let p := S.orderEmbOfFin hscard
    have hadj (i : Fin 3) : Cᶜ.Adj v (p i) :=
      (mem_neighborFinset Cᶜ v _).mp (hS (S.orderEmbOfFin_mem hscard i))
    have hpair (i j : Fin 3) (hij : i ≠ j) : C.Adj (p i) (p j) := by
      by_contra h
      have hh := (compl_adj C _ _).mpr ⟨p.injective.ne hij, h⟩
      exact hblue _ (is3Clique_triple_iff.mpr ⟨hadj i, hadj j, hh⟩)
    exact hC _ (is3Clique_triple_iff.mpr
      ⟨hpair 0 1 (by decide), hpair 0 2 (by decide), hpair 1 2 (by decide)⟩)

theorem smallGraphsEmbed {l m : ℕ} (H : SimpleGraph (Fin l)) (C : SimpleGraph (Fin m))
    (hl : l ≤ 3) (hm : 6 ≤ m) (hC : C.CliqueFree 3) : H.IsContained Cᶜ := by
  apply IsContained.trans ?_ (blueTriangle C hm hC)
  refine isContained_iff_exists_le_comap.mpr ⟨Fin.castLEEmb hl, ?_⟩
  intro x y hxy
  simpa only [comap_adj, top_adj] using (Fin.castLEEmb hl).injective.ne (H.ne_of_adj hxy)

theorem positiveDegree {l : ℕ} (H : SimpleGraph (Fin l)) (hl : 1 < l) (hH : H.Connected)
    (v : Fin l) : 0 < (H.neighborSet v).ncard := by
  classical
  have : Nontrivial (Fin l) := Fintype.one_lt_card_iff_nontrivial.mp (by simpa using hl)
  obtain ⟨w, hw⟩ := exists_ne v
  have hp := (hH.preconnected v w).degree_pos_left hw.symm
  rw [← card_neighborFinset_eq_degree, ← Set.ncard_coe_finset, coe_neighborFinset] at hp
  exact hp

theorem coreCounts {l k : ℕ} (H : SimpleGraph (Fin l))
    (hl : 0 < l) (hedge : H.edgeSet.ncard ≤ l + k)
    (hdeg : ∀ v, 2 ≤ (H.neighborSet v).ncard)
    (hind : ∀ x y, (H.neighborSet x).ncard = 2 → (H.neighborSet y).ncard = 2 → ¬ H.Adj x y) :
    ∃ D : Finset (Fin l), l ≤ 5 * k ∧ l - D.card < 4 * k ∧
      (H.induce (↑Dᶜ : Set (Fin l))).edgeSet.ncard ≤ l - D.card + k ∧
      ∀ x ∈ D, (H.neighborSet x).ncard ≤ 2 := by
  classical
  let D := Finset.univ.filter (fun v => (H.neighborSet v).ncard = 2)
  let U := Dᶜ
  have hD (x : Fin l) : x ∈ D ↔ (H.neighborSet x).ncard = 2 := by simp [D]
  have degree_ncard (x : Fin l) : H.degree x = (H.neighborSet x).ncard := by
    rw [← card_neighborFinset_eq_degree, ← Set.ncard_coe_finset, coe_neighborFinset]
  have hDsum : ∑ x ∈ D, H.degree x = 2 * D.card := by
    calc
      _ = ∑ _ ∈ D, 2 := Finset.sum_congr rfl (fun x hx => (degree_ncard x).trans ((hD x).mp hx))
      _ = _ := by simp [Nat.mul_comm]
  have hUsum : 3 * U.card ≤ ∑ x ∈ U, H.degree x := by
    calc
      _ = ∑ _ ∈ U, 3 := by simp [Nat.mul_comm]
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro x hx
        have hne : (H.neighborSet x).ncard ≠ 2 :=
          fun hh => Finset.mem_compl.mp hx ((hD x).mpr hh)
        rw [degree_ncard]
        exact lt_of_le_of_ne (hdeg x) hne.symm
  have hUV : U.card = l - D.card := by rw [Finset.card_compl, Fintype.card_fin]
  have hDU : D.card + U.card = l := by
    rw [Finset.card_add_card_compl, Fintype.card_fin]
  have hcount : H.edgeFinset.card = H.edgeSet.ncard := by
    rw [← coe_edgeFinset, Set.ncard_coe_finset]
  have hSum : 2 * D.card + 3 * U.card ≤ 2 * H.edgeFinset.card := by
    calc
      _ ≤ (∑ x ∈ D, H.degree x) + ∑ x ∈ U, H.degree x := by omega
      _ = _ := by rw [Finset.sum_add_sum_compl, H.sum_degrees_eq_twice_card_edges]
  let removed := D.biUnion (fun x => H.incidenceFinset x)
  have hremoved : removed.card = 2 * D.card := by
    calc
      _ = ∑ x ∈ D, (H.incidenceFinset x).card := by
        apply Finset.card_biUnion
        intro x hx y hy hxy
        apply Finset.disjoint_left.mpr
        intro e he hf
        change e ∈ H.incidenceFinset x at he
        change e ∈ H.incidenceFinset y at hf
        rw [incidenceFinset_eq_filter, Finset.mem_filter] at he hf
        exact hind x y ((hD x).mp hx) ((hD y).mp hy)
          ((H.adj_iff_exists_edge).mpr ⟨hxy, e, mem_edgeFinset.mp he.1, he.2, hf.2⟩)
      _ = _ := by simpa only [card_incidenceFinset_eq_degree] using hDsum
  let kept := H.edgeFinset.filter (fun e => e.toFinset ⊆ U)
  have hkept : kept.card = (H.induce (↑U : Set (Fin l))).edgeSet.ncard := by
    rw [← coe_edgeFinset, Set.ncard_coe_finset]
    exact card_filter_edgeFinset_toFinset_subset U
  have hsplit : removed.card + kept.card ≤ H.edgeFinset.card := by
    have hdis : Disjoint removed kept := by
      apply Finset.disjoint_left.mpr
      intro e he hf
      obtain ⟨x, hx, hxe⟩ := Finset.mem_biUnion.mp he
      rw [incidenceFinset_eq_filter, Finset.mem_filter] at hxe
      have hxu : x ∈ U := (Finset.mem_filter.mp hf).2 (Sym2.mem_toFinset.mpr hxe.2)
      exact Finset.mem_compl.mp hxu hx
    rw [← Finset.card_union_of_disjoint hdis]
    apply Finset.card_le_card
    intro e he
    rcases Finset.mem_union.mp he with he | he
    · obtain ⟨x, hx, hxe⟩ := Finset.mem_biUnion.mp he
      exact H.incidenceFinset_subset x hxe
    · exact (Finset.mem_filter.mp he).1
  have hV : 2 * U.card ≤ 4 * k := by omega
  have hDt : D.card ≤ U.card + k := by omega
  have hk : 0 < k := by omega
  refine ⟨D, ?_, ?_, ?_, fun x hx => ((hD x).mp hx).le⟩
  · omega
  · omega
  · change (H.induce (↑U : Set (Fin l))).edgeSet.ncard ≤ l - D.card + k
    omega

theorem main : H1 → H2 → OMA.R_Erdos1182_erdos_1182_variants_befrs_lower_R1.H1 := by
  intro hleaf hpath n hn G hG hsize C hC havoid
  let k := (2 * n + 1) / 15
  have compress : ∀ l ≤ n, ∀ (H : SimpleGraph (Fin l)), H.Connected →
      H.edgeSet.ncard ≤ l + k → ¬ H.IsContained Cᶜ →
      ∃ (r : ℕ) (J : SimpleGraph (Fin r)) (D : Finset (Fin r)),
        r ≤ 5 * k ∧ r - D.card < 4 * k ∧
        (J.induce (↑Dᶜ : Set (Fin r))).edgeSet.ncard ≤ r - D.card + k ∧
        (∀ x ∈ D, (J.neighborSet x).ncard ≤ 2) ∧ ¬ J.IsContained Cᶜ := by
    intro l
    induction l using Nat.strong_induction_on with
    | _ l ih =>
      intro hln H hconn he hbad
      have hl : 4 ≤ l := by
        by_contra! h
        exact hbad (smallGraphsEmbed H C (by omega) (by omega) hC)
      by_cases hasLeaf : ∃ x, (H.neighborSet x).ncard = 1
      · obtain ⟨J, hJ, hJedge, htransfer⟩ := hleaf H C hl (by omega) hconn hC hasLeaf
        exact ih (l - 1) (by omega) (by omega) J hJ (by omega) (fun h => hbad (htransfer h))
      by_cases hasPath : ∃ x y, H.Adj x y ∧
          (H.neighborSet x).ncard = 2 ∧ (H.neighborSet y).ncard = 2
      · obtain ⟨J, hJ, hJedge, htransfer⟩ := hpath H C hl (by omega) hconn hC hasPath
        exact ih (l - 1) (by omega) (by omega) J hJ (by omega) (fun h => hbad (htransfer h))
      have hdeg (v : Fin l) : 2 ≤ (H.neighborSet v).ncard := by
        have hp := positiveDegree H (by omega) hconn v
        have hne : (H.neighborSet v).ncard ≠ 1 := fun h => hasLeaf ⟨v, h⟩
        omega
      have hind x y (hx : (H.neighborSet x).ncard = 2) (hy : (H.neighborSet y).ncard = 2)
          (hxy : H.Adj x y) : False := hasPath ⟨x, y, hxy, hx, hy⟩
      obtain ⟨D, hlk, hdc, hde, hdd⟩ := coreCounts H (by omega) he hdeg hind
      exact ⟨l, H, D, hlk, hdc, hde, hdd, hbad⟩
  obtain ⟨l, H, D, hl, hD, hE, hdeg, hbad⟩ := compress n le_rfl G hG hsize havoid
  refine ⟨l, k, H, D, ?_, hl, hD, hE, hdeg, hbad⟩
  dsimp [k]
  omega

end R1H1R1

section LeafDeletion

open SimpleGraph

private lemma path_avoids_leaf {V : Type} {G : SimpleGraph V} {x a : V}
    (unique : ∀ u, G.Adj x u → u = a) {u v : V}
    (p : G.Walk u v) (hp : p.IsPath) (hu : u ≠ x) (hv : v ≠ x) :
    x ∉ p.support := by
  induction p with
  | nil => simpa using Ne.symm hu
  | @cons u w v huw p ih =>
    have hn := List.nodup_cons.mp (show (u :: p.support).Nodup from hp.support_nodup)
    have hw : w ≠ x := by
      intro he
      subst w
      cases p with
      | nil => exact hv rfl
      | @cons _ z _ hxz p =>
        have huz : u = z := (unique u huw.symm).trans (unique z hxz).symm
        have hz : z ∈ (Walk.cons hxz p).support := by simp
        exact hn.1 (by rw [huz]; exact hz)
    intro hx
    change x ∈ u :: p.support at hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hu rfl
    · exact ih (Walk.IsPath.mk' hn.2) hw hv hx

private lemma leaf_embedding {l m : ℕ} (G : SimpleGraph (Fin l)) (C : SimpleGraph (Fin m))
    (hlm : 2 * l - 1 ≤ m) (hC : C.CliqueFree 3)
    (x a : Fin l) (hxa : G.Adj x a) (unique : ∀ u, G.Adj x u → u = a)
    (U : Finset (Fin l)) (hU : U = Finset.univ.erase x)
    (hcopy : (G.induce (↑U : Set (Fin l))).IsContained Cᶜ) : G.IsContained Cᶜ := by
  classical
  by_cases hlarge : ∃ v : Fin m, l ≤ (C.neighborFinset v).card
  · obtain ⟨v, hv⟩ := hlarge
    obtain ⟨S, hS, hc⟩ := Finset.exists_subset_card_eq hv
    refine isContained_iff_exists_le_comap.mpr ⟨(S.orderEmbOfFin hc).toEmbedding, ?_⟩
    intro u w huw
    change Cᶜ.Adj (S.orderEmbOfFin hc u) (S.orderEmbOfFin hc w)
    rw [compl_adj]
    refine ⟨(S.orderEmbOfFin hc).injective.ne (G.ne_of_adj huw), ?_⟩
    intro hh
    have hu := (mem_neighborFinset C v _).mp (hS (S.orderEmbOfFin_mem hc u))
    have hw := (mem_neighborFinset C v _).mp (hS (S.orderEmbOfFin_mem hc w))
    exact hC _ (is3Clique_triple_iff.mpr ⟨hu, hw, hh⟩)
  have hu (u : Fin l) (hne : u ≠ x) : u ∈ U := by
    rw [hU]
    exact Finset.mem_erase.mpr ⟨hne, Finset.mem_univ u⟩
  obtain ⟨f, hf⟩ := isContained_iff_exists_le_comap.mp hcopy
  let A : ↥U := ⟨a, hu a (G.ne_of_adj hxa.symm)⟩
  let used : Finset (Fin m) := Finset.univ.map f
  let red := C.neighborFinset (f A)
  have hused : used.card = l - 1 := by
    simp only [used, Finset.card_map, Finset.card_univ]
    change Fintype.card ↥U = _
    rw [Fintype.card_coe, hU, Finset.card_erase_of_mem (Finset.mem_univ x), Finset.card_univ, Fintype.card_fin]
  have hred : red.card < l := Nat.lt_of_not_ge (fun h => hlarge ⟨f A, h⟩)
  have hl : 0 < l := (Nat.zero_le x.val).trans_lt x.isLt
  have hc : (used ∪ red).card < (Finset.univ : Finset (Fin m)).card := by
    have hh := Finset.card_union_le used red
    rw [Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨y, _, hy⟩ := Finset.exists_mem_notMem_of_card_lt_card hc
  have hyne (u : ↥U) : y ≠ f u := fun eq => hy
    (Finset.mem_union_left _ (eq ▸ Finset.mem_map_of_mem f (Finset.mem_univ u)))
  have hya : Cᶜ.Adj y (f A) := (compl_adj C _ _).mpr ⟨hyne A, fun h => hy
    (Finset.mem_union_right _ ((mem_neighborFinset C (f A) y).mpr h.symm))⟩
  let g (u : Fin l) : Fin m := if h : u ≠ x then f ⟨u, hu u h⟩ else y
  have hgx : g x = y := dif_neg (not_not.mpr rfl)
  have hg (u : Fin l) (h : u ≠ x) : g u = f ⟨u, hu u h⟩ := dif_pos h
  refine isContained_iff_exists_le_comap.mpr ⟨⟨g, ?_⟩, ?_⟩
  · intro u w huw
    by_cases hux : u = x
    · subst u
      by_contra hw
      have hwx : w ≠ x := fun e => hw e.symm
      exact hyne ⟨w, hu w hwx⟩ (hgx.symm.trans (huw.trans (hg w hwx)))
    · by_cases hwx : w = x
      · subst w
        exact (hyne ⟨u, hu u hux⟩ (hgx.symm.trans (huw.symm.trans (hg u hux)))).elim
      · rw [hg u hux, hg w hwx] at huw
        exact congrArg Subtype.val (f.injective huw)
  · have preserve_from_x (u : Fin l) (h : G.Adj x u) : Cᶜ.Adj (g x) (g u) := by
      have hua := unique u h
      subst u
      rw [hgx, hg a (G.ne_of_adj hxa.symm)]
      exact hya
    intro u w huw
    change Cᶜ.Adj (g u) (g w)
    by_cases hux : u = x
    · subst u
      exact preserve_from_x w huw
    · by_cases hwx : w = x
      · subst w
        exact (preserve_from_x u huw.symm).symm
      · rw [hg u hux, hg w hwx]
        exact hf (show (G.induce (↑U : Set (Fin l))).Adj ⟨u, hu u hux⟩ ⟨w, hu w hwx⟩ from huw)

theorem h1_proof : R1H1R1.H1 := by
  intro l m G C hl hm hG hC hex
  classical
  obtain ⟨x, hx⟩ := hex
  have hxdeg : G.degree x = 1 := by
    rw [← card_neighborFinset_eq_degree, ← Set.ncard_coe_finset, coe_neighborFinset, hx]
  obtain ⟨a, hxa, uniq⟩ := degree_eq_one_iff_existsUnique_adj.mp hxdeg
  let U := (Finset.univ : Finset (Fin l)).erase x
  have hcard : Fintype.card ↥U = l - 1 := by
    rw [Fintype.card_coe, Finset.card_erase_of_mem (Finset.mem_univ x), Finset.card_univ,
      Fintype.card_fin]
  let G' := G.induce (↑U : Set (Fin l))
  let A : ↥U := ⟨a, Finset.mem_erase.mpr ⟨G.ne_of_adj hxa.symm, Finset.mem_univ _⟩⟩
  have hconn : G'.Connected := by
    refine (connected_iff _).mpr ⟨?_, ⟨A⟩⟩
    intro u v
    obtain ⟨p, hp⟩ := (hG.preconnected u v).exists_isPath
    have ha (w : Fin l) (hw : w ∈ p.support) : w ∈ U :=
      Finset.mem_erase.mpr ⟨fun e => path_avoids_leaf uniq p hp
        (Finset.mem_erase.mp u.property).1 (Finset.mem_erase.mp v.property).1 (e ▸ hw),
        Finset.mem_univ _⟩
    exact ⟨p.induce (↑U : Set (Fin l)) ha⟩
  have hedge : G'.edgeSet.ncard + 1 ≤ G.edgeSet.ncard := by
    rw [← coe_edgeFinset, ← coe_edgeFinset (G := G), Set.ncard_coe_finset, Set.ncard_coe_finset]
    change (G.induce (↑U : Set (Fin l))).edgeFinset.card + 1 ≤ G.edgeFinset.card
    rw [← card_filter_edgeFinset_toFinset_subset]
    let E := G.edgeFinset.filter (fun e => e.toFinset ⊆ U)
    have hdis : Disjoint E (G.incidenceFinset x) := by
      apply Finset.disjoint_left.mpr
      intro e he hinc
      rw [incidenceFinset_eq_filter, Finset.mem_filter] at hinc
      have hxU := (Finset.mem_filter.mp he).2 (Sym2.mem_toFinset.mpr hinc.2)
      exact (Finset.mem_erase.mp hxU).1 rfl
    have hle : (E ∪ G.incidenceFinset x).card ≤ G.edgeFinset.card :=
      Finset.card_le_card (Finset.union_subset (Finset.filter_subset _ _) (G.incidenceFinset_subset x))
    rw [Finset.card_union_of_disjoint hdis, card_incidenceFinset_eq_degree, hxdeg] at hle
    exact hle
  let e := (Fintype.equivFinOfCardEq hcard).symm
  let H := G'.comap e
  let i : H ≃g G' := { toEquiv := e, map_rel_iff' := Iff.rfl }
  refine ⟨H, i.connected_iff.mpr hconn, ?_, ?_⟩
  · have he : H.edgeSet.ncard = G'.edgeSet.ncard := by
      rw [← coe_edgeFinset, ← coe_edgeFinset (G := G'), Set.ncard_coe_finset, Set.ncard_coe_finset]
      exact i.card_edgeFinset_eq
    omega
  · intro hcopy
    exact leaf_embedding G C hm hC x a hxa uniq U rfl
      (IsContained.trans ⟨i.symm.toCopy⟩ hcopy)

end LeafDeletion

section PathContraction

open SimpleGraph

private lemma embed_anchored {V W : Type} [Fintype V] [Fintype W]
    (hcard : Fintype.card V ≤ Fintype.card W)
    {a b : V} {c d : W} (hab : a ≠ b) (hcd : c ≠ d) :
    ∃ f : V ↪ W, f a = c ∧ f b = d := by
  classical
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hcard
  let before (k : Bool) := if k then e a else e b
  let after (k : Bool) := if k then c else d
  have hbefore : Function.Injective before := by
    intro i j h
    cases i <;> cases j <;> simp_all [before, e.injective.ne hab]
  have hafter : Function.Injective after := by
    intro i j h
    cases i <;> cases j <;> simp_all [after]
  obtain ⟨p, hp⟩ := Equiv.Perm.exists_extending_pair before after hbefore hafter
  exact ⟨e.trans p.toEmbedding, hp true, hp false⟩

private lemma embed_in_blue_clique {l m : ℕ} (G : SimpleGraph (Fin l)) (C : SimpleGraph (Fin m))
    (X : Finset (Fin m)) (hcard : l ≤ X.card)
    (hblue : ∀ a ∈ X, ∀ b ∈ X, ¬ C.Adj a b) : G.IsContained Cᶜ := by
  classical
  obtain ⟨S, hS, hScard⟩ := Finset.exists_subset_card_eq hcard
  refine isContained_iff_exists_le_comap.mpr ⟨(S.orderEmbOfFin hScard).toEmbedding, ?_⟩
  intro u w huw
  change Cᶜ.Adj (S.orderEmbOfFin hScard u) (S.orderEmbOfFin hScard w)
  rw [compl_adj]
  refine ⟨(S.orderEmbOfFin hScard).injective.ne (G.ne_of_adj huw), ?_⟩
  exact hblue _ (hS (S.orderEmbOfFin_mem hScard u)) _ (hS (S.orderEmbOfFin_mem hScard w))

private lemma embed_in_near_blue_clique {l m : ℕ} (G : SimpleGraph (Fin l)) (C : SimpleGraph (Fin m))
    (X : Finset (Fin m)) (hcard : l ≤ X.card)
    {x y : Fin l} (hxy : x ≠ y) (hnxy : ¬ G.Adj x y)
    {r s : Fin m} (hr : r ∈ X) (hs : s ∈ X) (hrs : r ≠ s)
    (hred : ∀ a ∈ X, ∀ b ∈ X, C.Adj a b → (a = r ∧ b = s) ∨ (a = s ∧ b = r)) :
    G.IsContained Cᶜ := by
  classical
  have hsz : Fintype.card (Fin l) ≤ Fintype.card ↥X := by
    simpa only [Fintype.card_fin, Fintype.card_coe] using hcard
  have hh : (⟨r, hr⟩ : ↥X) ≠ ⟨s, hs⟩ := fun he => hrs (congrArg Subtype.val he)
  obtain ⟨f, hfx, hfy⟩ := embed_anchored hsz hxy hh
  let e : Fin l ↪ Fin m := f.trans ⟨Subtype.val, Subtype.val_injective⟩
  have hex : e x = r := congrArg Subtype.val hfx
  have hey : e y = s := congrArg Subtype.val hfy
  refine isContained_iff_exists_le_comap.mpr ⟨e, ?_⟩
  intro a b hab
  change Cᶜ.Adj (e a) (e b)
  rw [compl_adj]
  refine ⟨e.injective.ne (G.ne_of_adj hab), ?_⟩
  intro h
  rcases hred (e a) (f a).property (e b) (f b).property h with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · have ha' := e.injective (ha.trans hex.symm)
    have hb' := e.injective (hb.trans hey.symm)
    exact hnxy (ha' ▸ hb' ▸ hab)
  · have ha' := e.injective (ha.trans hey.symm)
    have hb' := e.injective (hb.trans hex.symm)
    exact hnxy (hb' ▸ ha' ▸ hab.symm)

private lemma embed_blue_clique_with_apex {l m : ℕ} (G : SimpleGraph (Fin l)) (C : SimpleGraph (Fin m))
    (X : Finset (Fin m)) (hcard : l - 1 ≤ X.card)
    {x y z : Fin l} (hy : y ≠ x) (hz : z ≠ x) (hyz : y ≠ z)
    (hN : ∀ a, G.Adj x a → a = y ∨ a = z)
    {v r s : Fin m} (hv : v ∉ X) (hr : r ∈ X) (hs : s ∈ X) (hrs : r ≠ s)
    (hvr : Cᶜ.Adj v r) (hvs : Cᶜ.Adj v s)
    (hblue : ∀ a ∈ X, ∀ b ∈ X, ¬ C.Adj a b) : G.IsContained Cᶜ := by
  classical
  let U := (Finset.univ : Finset (Fin l)).erase x
  have hu (a : Fin l) (ha : a ≠ x) : a ∈ U := Finset.mem_erase.mpr ⟨ha, Finset.mem_univ a⟩
  have hsz : Fintype.card ↥U ≤ Fintype.card ↥X := by
    rw [Fintype.card_coe, Fintype.card_coe, Finset.card_erase_of_mem (Finset.mem_univ x),
      Finset.card_univ, Fintype.card_fin]
    exact hcard
  have hh : (⟨y, hu y hy⟩ : ↥U) ≠ ⟨z, hu z hz⟩ := fun he => hyz (congrArg Subtype.val he)
  have hh' : (⟨r, hr⟩ : ↥X) ≠ ⟨s, hs⟩ := fun he => hrs (congrArg Subtype.val he)
  obtain ⟨f, hfY, hfZ⟩ := embed_anchored hsz hh hh'
  let g (a : Fin l) : Fin m := if ha : a ≠ x then (f ⟨a, hu a ha⟩).val else v
  have gx : g x = v := dif_neg (not_not.mpr rfl)
  have gg (a : Fin l) (ha : a ≠ x) : g a = (f ⟨a, hu a ha⟩).val := dif_pos ha
  have gin (a : Fin l) (ha : a ≠ x) : g a ∈ X := by rw [gg a ha]; exact (f _).property
  have gi : Function.Injective g := by
    intro a b hab
    by_contra hn
    by_cases ha : a = x
    · subst a
      exact hv (gx ▸ hab ▸ gin b (Ne.symm hn))
    · by_cases hb : b = x
      · subst b
        exact hv (gx ▸ hab.symm ▸ gin a hn)
      · rw [gg a ha, gg b hb] at hab
        exact hn (congrArg Subtype.val (f.injective (Subtype.ext hab)))
  have ghx (a : Fin l) (ha : G.Adj x a) : Cᶜ.Adj (g x) (g a) := by
    rw [gx]
    rcases hN a ha with h | h
    · subst a
      rw [gg y hy, hfY]
      exact hvr
    · subst a
      rw [gg z hz, hfZ]
      exact hvs
  refine isContained_iff_exists_le_comap.mpr ⟨⟨g, gi⟩, ?_⟩
  intro a b hab
  change Cᶜ.Adj (g a) (g b)
  by_cases ha : a = x
  · subst a
    exact ghx b hab
  · by_cases hb : b = x
    · subst b
      exact (ghx a hab.symm).symm
    · exact (compl_adj C _ _).mpr
        ⟨gi.ne (G.ne_of_adj hab), hblue _ (gin a ha) _ (gin b hb)⟩

private lemma place_two_vertices {l m : ℕ} (G : SimpleGraph (Fin l)) (C : SimpleGraph (Fin m))
    {x y : Fin l} (hxy : x ≠ y)
    (R : Set (Fin l)) (hR : ∀ z, z ∈ R ↔ z ≠ x ∧ z ≠ y)
    (f : R ↪ Fin m)
    (hf : ∀ a b : R, G.Adj a b → Cᶜ.Adj (f a) (f b))
    {p q : Fin m} (hpq : Cᶜ.Adj p q)
    (hp : ∀ a : R, p ≠ f a) (hq : ∀ a : R, q ≠ f a)
    (hx : ∀ a : R, G.Adj x a → Cᶜ.Adj p (f a))
    (hy : ∀ a : R, G.Adj y a → Cᶜ.Adj q (f a)) :
    G.IsContained Cᶜ := by
  classical
  let g (z : Fin l) : Fin m := if hz : z ∈ R then f ⟨z, hz⟩ else if z = x then p else q
  have gX : g x = p := by
    have h : x ∉ R := fun h => ((hR x).mp h).1 rfl
    simp [g, h]
  have gY : g y = q := by
    have h : y ∉ R := fun h => ((hR y).mp h).2 rfl
    simp [g, h, hxy.symm]
  have gR (a : R) : g a = f a := dif_pos a.property
  have casesR (a : Fin l) : a = x ∨ a = y ∨ a ∈ R := by
    by_cases ha : a = x
    · exact Or.inl ha
    by_cases hb : a = y
    · exact Or.inr (Or.inl hb)
    exact Or.inr (Or.inr ((hR a).mpr ⟨ha, hb⟩))
  have hginj : Function.Injective g := by
    intro a b hab
    rcases casesR a with ha | ha | ha
    · subst a
      rcases casesR b with hb | hb | hb
      · exact hb.symm
      · subst b
        exact ((compl_adj C _ _).mp hpq).1 (gX.symm.trans (hab.trans gY)) |>.elim
      · exact (hp ⟨b, hb⟩ (gX.symm.trans (hab.trans (gR ⟨b, hb⟩)))).elim
    · subst a
      rcases casesR b with hb | hb | hb
      · subst b
        exact ((compl_adj C _ _).mp hpq).1 (gX.symm.trans (hab.symm.trans gY)) |>.elim
      · exact hb.symm
      · exact (hq ⟨b, hb⟩ (gY.symm.trans (hab.trans (gR ⟨b, hb⟩)))).elim
    · rcases casesR b with hb | hb | hb
      · subst b
        exact (hp ⟨a, ha⟩ (gX.symm.trans (hab.symm.trans (gR ⟨a, ha⟩)))).elim
      · subst b
        exact (hq ⟨a, ha⟩ (gY.symm.trans (hab.symm.trans (gR ⟨a, ha⟩)))).elim
      · exact congrArg Subtype.val (f.injective
          ((gR ⟨a, ha⟩).symm.trans (hab.trans (gR ⟨b, hb⟩))))
  have gxAdj (z : Fin l) (h : G.Adj x z) : Cᶜ.Adj (g x) (g z) := by
    rw [gX]
    rcases casesR z with hz | hz | hz
    · exact (G.ne_of_adj h hz.symm).elim
    · subst z
      rw [gY]
      exact hpq
    · exact (gR ⟨z, hz⟩).symm ▸ hx ⟨z, hz⟩ h
  have gyAdj (z : Fin l) (h : G.Adj y z) : Cᶜ.Adj (g y) (g z) := by
    rw [gY]
    rcases casesR z with hz | hz | hz
    · subst z
      rw [gX]
      exact hpq.symm
    · exact (G.ne_of_adj h hz.symm).elim
    · exact (gR ⟨z, hz⟩).symm ▸ hy ⟨z, hz⟩ h
  refine isContained_iff_exists_le_comap.mpr ⟨⟨g, hginj⟩, ?_⟩
  intro a b hab
  change Cᶜ.Adj (g a) (g b)
  rcases casesR a with ha | ha | ha
  · subst a
    exact gxAdj b hab
  · subst a
    exact gyAdj b hab
  · rcases casesR b with hb | hb | hb
    · subst b
      exact (gxAdj a hab.symm).symm
    · subst b
      exact (gyAdj a hab.symm).symm
    · exact (gR ⟨a, ha⟩).symm ▸ (gR ⟨b, hb⟩).symm ▸ hf ⟨a, ha⟩ ⟨b, hb⟩ hab

private theorem pathContractionGraph {l : ℕ} (G : SimpleGraph (Fin l)) (x y u : Fin l)
    (hconn : G.Connected) (hxy : G.Adj x y) (hxu : G.Adj x u) (hyu : y ≠ u)
    (hN : ∀ a, G.Adj x a → a = y ∨ a = u)
    (W : Finset (Fin l)) (hW : W = Finset.univ.erase x)
    (Y U : ↥W) (hY : (Y : Fin l) = y) (hU : (U : Fin l) = u)
    (H : SimpleGraph ↥W)
    (hH : H = G.induce (↑W : Set (Fin l)) ⊔ fromEdgeSet {s(Y, U)}) :
    H.Connected ∧ H.edgeSet.ncard + 1 ≤ G.edgeSet.ncard := by
  classical
  have hyu' : Y ≠ U := fun h => hyu (hY.symm.trans ((congrArg Subtype.val h).trans hU))
  have hju : H.Adj Y U := by
    rw [hH]
    exact Or.inr ((fromEdgeSet_adj _).mpr ⟨by simp, hyu'⟩)
  have he (a : Fin l) (ha : a ≠ x) : a ∈ W := by
    rw [hW]
    exact Finset.mem_erase.mpr ⟨ha, Finset.mem_univ _⟩
  have hmem (a : Fin l) (ha : a ∈ W) : a ≠ x := by
    rw [hW, Finset.mem_erase] at ha
    exact ha.1
  have hne (A : ↥W) : (A : Fin l) ≠ x := hmem A.val A.property
  let f (a : Fin l) : ↥W := if ha : a = x then Y else ⟨a, he a ha⟩
  have hfx : f x = Y := dif_pos rfl
  have hf (a : Fin l) (ha : a ≠ x) : f a = ⟨a, he a ha⟩ := dif_neg ha
  have hfy : f y = Y := by
    rw [hf y (G.ne_of_adj hxy.symm)]
    exact Subtype.ext hY.symm
  have hfu : f u = U := by
    rw [hf u (G.ne_of_adj hxu.symm)]
    exact Subtype.ext hU.symm
  have fromX (v : Fin l) (hxv : G.Adj x v) : H.Reachable (f x) (f v) := by
    rcases hN v hxv with hv | hv
    · rw [hv, hfx, hfy]
    · rw [hv, hfx, hfu]
      exact hju.reachable
  have hadj {a b : Fin l} (hab : G.Adj a b) : H.Reachable (f a) (f b) := by
    by_cases ha : a = x
    · subst a
      exact fromX b hab
    · by_cases hb : b = x
      · subst b
        exact (fromX a hab.symm).symm
      · rw [hf a ha, hf b hb]
        exact (show H.Adj ⟨a, he a ha⟩ ⟨b, he b hb⟩ by
          rw [hH]
          exact Or.inl hab).reachable
  have reach {a b : Fin l} (p : G.Walk a b) : H.Reachable (f a) (f b) := by
    induction p with
    | nil => exact Reachable.rfl
    | cons h _ ih => exact (hadj h).trans ih
  constructor
  · refine (connected_iff _).mpr ⟨?_, ⟨Y⟩⟩
    intro A B
    have hfa : f A = A := by
      rw [hf _ (hne A)]
    have hfb : f B = B := by
      rw [hf _ (hne B)]
    obtain ⟨p⟩ := hconn.preconnected A B
    simpa only [hfa, hfb] using reach p
  · let J := G.induce (↑W : Set (Fin l))
    let K : SimpleGraph ↥W := fromEdgeSet {s(Y, U)}
    have hpair : G.degree x = 2 := by
      classical
      rw [← card_neighborFinset_eq_degree]
      have hn : G.neighborFinset x = {y, u} := by
        ext v
        rw [mem_neighborFinset, Finset.mem_insert, Finset.mem_singleton]
        exact ⟨hN v, fun h => h.elim (fun hv => hv.symm ▸ hxy) (fun hv => hv.symm ▸ hxu)⟩
      rw [hn, Finset.card_pair hyu]
    have hdecrease : J.edgeFinset.card + 2 ≤ G.edgeFinset.card := by
      change (G.induce (↑W : Set (Fin l))).edgeFinset.card + 2 ≤ G.edgeFinset.card
      rw [← card_filter_edgeFinset_toFinset_subset]
      let E := G.edgeFinset.filter (fun e => e.toFinset ⊆ W)
      have hdis : Disjoint E (G.incidenceFinset x) := by
        apply Finset.disjoint_left.mpr
        intro e hE hinc
        rw [incidenceFinset_eq_filter, Finset.mem_filter] at hinc
        have hxW := (Finset.mem_filter.mp hE).2 (Sym2.mem_toFinset.mpr hinc.2)
        rw [hW, Finset.mem_erase] at hxW
        exact hxW.1 rfl
      have hle : (E ∪ G.incidenceFinset x).card ≤ G.edgeFinset.card :=
        Finset.card_le_card (Finset.union_subset (Finset.filter_subset _ _) (G.incidenceFinset_subset x))
      rw [Finset.card_union_of_disjoint hdis, card_incidenceFinset_eq_degree, hpair] at hle
      exact hle
    have hk : K.edgeSet.ncard ≤ 1 := by
      change (fromEdgeSet ({s(Y, U)} : Set (Sym2 ↥W))).edgeSet.ncard ≤ 1
      rw [edgeSet_fromEdgeSet]
      simpa using Set.ncard_le_ncard (Set.sdiff_subset :
        ({s(Y, U)} : Set (Sym2 ↥W)) \ Sym2.diagSet ⊆ {s(Y, U)})
    have hbound : H.edgeSet.ncard ≤ J.edgeSet.ncard + K.edgeSet.ncard := by
      have hh : H = J ⊔ K := hH
      rw [hh, edgeSet_sup]
      exact Set.ncard_union_le _ _
    have hj : J.edgeSet.ncard + 2 ≤ G.edgeSet.ncard := by
      rw [← coe_edgeFinset, ← coe_edgeFinset (G := G), Set.ncard_coe_finset,
        Set.ncard_coe_finset]
      exact hdecrease
    omega

private lemma adjacent_degree_two_other {l : ℕ} (G : SimpleGraph (Fin l)) {x y : Fin l}
    (hxy : G.Adj x y) (hx : (G.neighborSet x).ncard = 2) :
    ∃ u, u ≠ y ∧ G.Adj x u ∧ ∀ t, G.Adj x t → t = y ∨ t = u := by
  obtain ⟨a, b, hab, h⟩ := Set.ncard_eq_two.mp hx
  have hm (t : Fin l) : G.Adj x t ↔ t = a ∨ t = b := by
    change t ∈ G.neighborSet x ↔ _
    rw [h, Set.mem_insert_iff, Set.mem_singleton_iff]
  rcases (hm y).mp hxy with rfl | rfl
  · exact ⟨b, hab.symm, (hm b).mpr (Or.inr rfl), fun t ht => (hm t).mp ht⟩
  · exact ⟨a, hab, (hm a).mpr (Or.inl rfl), fun t ht => ((hm t).mp ht).symm⟩

private lemma shorten_keeps_blue_copy {l m : ℕ} (G : SimpleGraph (Fin l)) (C : SimpleGraph (Fin m))
    (hl : 4 ≤ l) (hm : 2 * l - 1 ≤ m) (hC : C.CliqueFree 3)
    {x y u v : Fin l} (hxy : G.Adj x y) (hxu : G.Adj x u) (hyv : G.Adj y v)
    (huy : u ≠ y) (hvx : v ≠ x)
    (hx : ∀ t, G.Adj x t → t = y ∨ t = u)
    (hy : ∀ t, G.Adj y t → t = x ∨ t = v)
    (W : Finset (Fin l)) (hW : W = Finset.univ.erase x)
    (Y U V : ↥W) (hY : Y.val = y) (hU : U.val = u) (hV : V.val = v)
    (H : SimpleGraph ↥W) (hH : H = G.induce (↑W : Set (Fin l)) ⊔ fromEdgeSet {s(Y, U)})
    (hcopy : H.IsContained Cᶜ) : G.IsContained Cᶜ := by
  classical
  obtain ⟨f, hf⟩ := isContained_iff_exists_le_comap.mp hcopy
  let used := (Finset.univ : Finset ↥W).map f
  let X := usedᶜ
  have hUsed : used.card = l - 1 := by
    rw [Finset.card_map, Finset.card_univ, Fintype.card_coe, hW,
      Finset.card_erase_of_mem (Finset.mem_univ x), Finset.card_univ, Fintype.card_fin]
  have hX : l ≤ X.card := by
    change l ≤ usedᶜ.card
    rw [Finset.card_compl, Fintype.card_fin, hUsed]
    omega
  have outside (a : Fin m) (ha : a ∈ X) (b : ↥W) : a ≠ f b := by
    intro e
    exact Finset.mem_compl.mp ha (e ▸ Finset.mem_map_of_mem f (Finset.mem_univ b))
  have blueOutside (a : Fin m) (ha : a ∈ X) (b : ↥W) (hn : ¬ C.Adj a (f b)) :
      Cᶜ.Adj a (f b) := (compl_adj C _ _).mpr ⟨outside a ha b, hn⟩
  have hYU : Cᶜ.Adj (f Y) (f U) := hf (show H.Adj Y U by
    rw [hH]
    apply Or.inr
    apply (fromEdgeSet_adj _).mpr
    exact ⟨by simp, fun e => huy (hU.symm.trans ((congrArg Subtype.val e).symm.trans hY))⟩)
  have hYV : Cᶜ.Adj (f Y) (f V) := hf (show H.Adj Y V by
    rw [hH]
    apply Or.inl
    change G.Adj Y.val V.val
    simpa only [hY, hV] using hyv)
  let R : Set (Fin l) := {t | t ≠ x ∧ t ≠ y}
  let incl : R ↪ ↥W := ⟨fun a => ⟨a.val, by
    rw [hW]
    exact Finset.mem_erase.mpr ⟨a.property.1, Finset.mem_univ _⟩⟩,
    fun a b e => Subtype.ext (congrArg (fun w : ↥W => w.val) e)⟩
  let e := incl.trans f
  have eAdj (a b : R) (h : G.Adj a b) : Cᶜ.Adj (e a) (e b) := hf (show H.Adj (incl a) (incl b) by
    rw [hH]
    exact Or.inl h)
  have eX (a : Fin m) (ha : a ∈ X) (b : R) : a ≠ e b := outside a ha (incl b)
  have eY (a : R) : f Y ≠ e a := by
    intro he
    have e' := congrArg Subtype.val (f.injective he)
    exact a.property.2 (e'.symm.trans hY)
  have place {p q : Fin m} (hpq : Cᶜ.Adj p q)
      (hp : ∀ a : R, p ≠ e a) (hq : ∀ a : R, q ≠ e a)
      (hpu : Cᶜ.Adj p (f U)) (hqv : Cᶜ.Adj q (f V)) : G.IsContained Cᶜ := by
    refine place_two_vertices G C (G.ne_of_adj hxy) R (fun _ => Iff.rfl) e eAdj hpq hp hq ?_ ?_
    · intro a ha
      have hau := (hx a ha).resolve_left a.property.2
      have he' : e a = f U := congrArg f (Subtype.ext (hau.trans hU.symm))
      simpa only [he'] using hpu
    · intro a ha
      have hav := (hy a ha).resolve_left a.property.1
      have he' : e a = f V := congrArg f (Subtype.ext (hav.trans hV.symm))
      simpa only [he'] using hqv
  by_contra hbad
  let A := X.filter (fun t => C.Adj (f Y) t)
  let B := X.filter (fun t => Cᶜ.Adj (f Y) t)
  have Ared (a : Fin m) (ha : a ∈ A) : C.Adj (f Y) a := (Finset.mem_filter.mp ha).2
  have Bblue (b : Fin m) (hb : b ∈ B) : Cᶜ.Adj (f Y) b := (Finset.mem_filter.mp hb).2
  have AX (a : Fin m) (ha : a ∈ A) : a ∈ X := (Finset.mem_filter.mp ha).1
  have BX (b : Fin m) (hb : b ∈ B) : b ∈ X := (Finset.mem_filter.mp hb).1
  have partition (t : Fin m) (ht : t ∈ X) : t ∈ A ∨ t ∈ B := by
    by_cases h : C.Adj (f Y) t
    · exact Or.inl (Finset.mem_filter.mpr ⟨ht, h⟩)
    · exact Or.inr (Finset.mem_filter.mpr ⟨ht, (compl_adj C _ _).mpr ⟨(outside t ht Y).symm, h⟩⟩)
  have BredU (b : Fin m) (hb : b ∈ B) : C.Adj b (f U) := by
    by_contra h
    exact hbad (place (Bblue b hb).symm (eX b (BX b hb)) eY
      (blueOutside b (BX b hb) U h) hYV)
  have BredV (b : Fin m) (hb : b ∈ B) : C.Adj b (f V) := by
    by_contra h
    exact hbad (place (Bblue b hb) eY (eX b (BX b hb)) hYU
      (blueOutside b (BX b hb) V h))
  have Aind (a : Fin m) (ha : a ∈ A) (b : Fin m) (hb : b ∈ A) : ¬ C.Adj a b :=
    fun h => hC _ (is3Clique_triple_iff.mpr ⟨Ared a ha, Ared b hb, h⟩)
  have Bind (a : Fin m) (ha : a ∈ B) (b : Fin m) (hb : b ∈ B) : ¬ C.Adj a b :=
    fun h => hC _ (is3Clique_triple_iff.mpr ⟨(BredU a ha).symm, (BredU b hb).symm, h⟩)
  let P := A.filter (fun a => ∃ b ∈ B, C.Adj a b)
  have PA (a : Fin m) (ha : a ∈ P) : a ∈ A := (Finset.mem_filter.mp ha).1
  have Pblue (a : Fin m) (ha : a ∈ P) : Cᶜ.Adj a (f U) ∧ Cᶜ.Adj a (f V) := by
    obtain ⟨b, hb, hab⟩ := (Finset.mem_filter.mp ha).2
    refine ⟨blueOutside a (AX a (PA a ha)) U ?_, blueOutside a (AX a (PA a ha)) V ?_⟩
    · exact fun h => hC _ (is3Clique_triple_iff.mpr ⟨hab, h, BredU b hb⟩)
    · exact fun h => hC _ (is3Clique_triple_iff.mpr ⟨hab, h, BredV b hb⟩)
  have uniqueP (a : Fin m) (ha : a ∈ P) (b : Fin m) (hb : b ∈ P) : a = b := by
    by_contra hn
    have hpq : Cᶜ.Adj a b := (compl_adj C _ _).mpr ⟨hn, Aind a (PA a ha) b (PA b hb)⟩
    exact hbad (place hpq (eX a (AX a (PA a ha))) (eX b (AX b (PA b hb)))
      (Pblue a ha).1 (Pblue b hb).2)
  have redEdge (a : Fin m) (ha : a ∈ X) (b : Fin m) (hb : b ∈ X) (hab : C.Adj a b) :
      (a ∈ P ∧ b ∈ B) ∨ (b ∈ P ∧ a ∈ B) := by
    rcases partition a ha with ha' | ha'
    · rcases partition b hb with hb' | hb'
      · exact (Aind a ha' b hb' hab).elim
      · exact Or.inl ⟨Finset.mem_filter.mpr ⟨ha', b, hb', hab⟩, hb'⟩
    · rcases partition b hb with hb' | hb'
      · exact Or.inr ⟨Finset.mem_filter.mpr ⟨hb', a, ha', hab.symm⟩, ha'⟩
      · exact (Bind a ha' b hb' hab).elim
  by_cases hex : P.Nonempty
  swap
  · exact hbad (embed_in_blue_clique G C X hX (fun a ha b hb h =>
      (redEdge a ha b hb h).elim (fun hh => hex ⟨a, hh.1⟩) (fun hh => hex ⟨b, hh.1⟩)))
  obtain ⟨a, ha⟩ := hex
  have haX := AX a (PA a ha)
  by_cases hb : 1 < B.card
  · obtain ⟨b, hbB, c, hcB, hbc⟩ := Finset.one_lt_card.mp hb
    have inErase (t : Fin m) (ht : t ∈ B) : t ∈ X.erase a :=
      Finset.mem_erase.mpr ⟨fun eq => ((compl_adj C _ _).mp (Bblue t ht)).2
        (eq ▸ Ared a (PA a ha)), BX t ht⟩
    have hsz : l - 1 ≤ (X.erase a).card := by
      rw [Finset.card_erase_of_mem haX]
      omega
    refine hbad (embed_blue_clique_with_apex G C (X.erase a) hsz
      (G.ne_of_adj hxy.symm) (G.ne_of_adj hxu.symm) huy.symm hx ?_
      (inErase b hbB) (inErase c hcB) hbc (Bblue b hbB) (Bblue c hcB) ?_)
    · exact fun ht => outside (f Y) (Finset.mem_of_mem_erase ht) Y rfl
    · intro p hp q hq hpq
      rcases redEdge p (Finset.mem_of_mem_erase hp) q (Finset.mem_of_mem_erase hq) hpq with h | h
      · exact (Finset.mem_erase.mp hp).1 (uniqueP p h.1 a ha)
      · exact (Finset.mem_erase.mp hq).1 (uniqueP q h.1 a ha)
  obtain ⟨b, hbB, hab⟩ := (Finset.mem_filter.mp ha).2
  have uniqueB (t : Fin m) (ht : t ∈ B) : t = b :=
    Finset.card_le_one.mp (Nat.le_of_not_gt hb) t ht b hbB
  have hxdeg : (G.neighborSet x).ncard = 2 := by
    have he : G.neighborSet x = {y, u} := by
      ext t
      change G.Adj x t ↔ t ∈ ({y, u} : Set (Fin l))
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      exact ⟨hx t, fun h => h.elim (fun e => e.symm ▸ hxy) (fun e => e.symm ▸ hxu)⟩
    exact Set.ncard_eq_two.mpr ⟨y, u, huy.symm, he⟩
  let S := insert x (G.neighborFinset x)
  have hS : S.card < (Finset.univ : Finset (Fin l)).card := by
    have hd : (G.neighborFinset x).card = 2 := by
      rw [← Set.ncard_coe_finset, coe_neighborFinset, hxdeg]
    have hh : S.card ≤ (G.neighborFinset x).card + 1 := Finset.card_insert_le _ _
    rw [Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨t, _, ht⟩ := Finset.exists_mem_notMem_of_card_lt_card hS
  have htx : x ≠ t := fun e => ht (e ▸ Finset.mem_insert_self _ _)
  have htn : ¬ G.Adj x t := fun h => ht (Finset.mem_insert_of_mem ((mem_neighborFinset G x t).mpr h))
  refine hbad (embed_in_near_blue_clique G C X hX htx htn haX (BX b hbB)
    (C.ne_of_adj hab) ?_)
  intro p hp q hq hpq
  rcases redEdge p hp q hq hpq with h | h
  · exact Or.inl ⟨uniqueP p h.1 a ha, uniqueB q h.2⟩
  · exact Or.inr ⟨uniqueB p h.2, uniqueP q h.1 a ha⟩

theorem h2_proof : R1H1R1.H2 := by
  intro l m G C hl hm hconn hC hex
  classical
  obtain ⟨x, y, hxy, hx, hy⟩ := hex
  obtain ⟨u, huy, hxu, hxN⟩ := adjacent_degree_two_other G hxy hx
  obtain ⟨v, hvx, hyv, hyN⟩ := adjacent_degree_two_other G hxy.symm hy
  let W := (Finset.univ : Finset (Fin l)).erase x
  have hmem (a : Fin l) (ha : a ≠ x) : a ∈ W := Finset.mem_erase.mpr ⟨ha, Finset.mem_univ _⟩
  let Y : ↥W := ⟨y, hmem y (G.ne_of_adj hxy.symm)⟩
  let U : ↥W := ⟨u, hmem u (G.ne_of_adj hxu.symm)⟩
  let V : ↥W := ⟨v, hmem v hvx⟩
  let J := G.induce (↑W : Set (Fin l)) ⊔ fromEdgeSet {s(Y, U)}
  obtain ⟨hJ, hJedge⟩ := pathContractionGraph G x y u hconn hxy hxu huy.symm hxN
    W rfl Y U rfl rfl J rfl
  have hcard : Fintype.card ↥W = l - 1 := by
    rw [Fintype.card_coe, Finset.card_erase_of_mem (Finset.mem_univ x), Finset.card_univ,
      Fintype.card_fin]
  let e := (Fintype.equivFinOfCardEq hcard).symm
  let H := J.comap e
  let i : H ≃g J := { toEquiv := e, map_rel_iff' := Iff.rfl }
  refine ⟨H, i.connected_iff.mpr hJ, ?_, ?_⟩
  · have he : H.edgeSet.ncard = J.edgeSet.ncard := by
      rw [← coe_edgeFinset, ← coe_edgeFinset (G := J), Set.ncard_coe_finset, Set.ncard_coe_finset]
      exact i.card_edgeFinset_eq
    omega
  · intro hcopy
    exact shorten_keeps_blue_copy G C hl hm hC hxy hxu hyv huy hvx hxN hyN
      W rfl Y U V rfl rfl rfl J rfl (IsContained.trans ⟨i.symm.toCopy⟩ hcopy)

end PathContraction

end OMA.Erdos1182BefrsLowerR1H1

theorem OMA.solution : OMA.R_Erdos1182_erdos_1182_variants_befrs_lower_R1.H1 :=
  OMA.Erdos1182BefrsLowerR1H1.R1H1R1.main
    OMA.Erdos1182BefrsLowerR1H1.h1_proof
    OMA.Erdos1182BefrsLowerR1H1.h2_proof
