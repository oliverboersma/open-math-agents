import OMAReductions.R_ReconstructionConjecture_reconstruction_conjecture_variants_tree_R1_H4_R1
import Mathlib.Tactic

/-!
Proof of `ReconstructionConjecture.reconstruction_conjecture.variants.tree.R1.H4.R1.H4`
(Kelly's path-limb reconstruction case for bicentral non-path trees of odd diameter `2 * r + 1`).

Given hypomorphic finite trees `G, H` of odd diameter `2 * r + 1` (`r ≥ 1`) that are not paths,
with bicenter decompositions `(G₁, G₂)` and `(H₁, H₂)` where at least one limb has size `≤ r + 1`:
1. Any limb has size `≥ r + 1`; a limb of size `r + 1` is a path of length `r` from its center
   vertex, with a unique depth-`r` leaf `u_r` and no vertices of degree `≥ 3`.
2. Deleting any leaf `v` yields a tree with unchanged distances. Its diameter is `2 * r` (central)
   if and only if `v` is the unique depth-`r` vertex of its limb, and `2 * r + 1` (bicentral, same
   bicenter) otherwise.
3. If both `G` and `H` have a path-limb (`|G₁| = |H₁| = r + 1`), then either `G - u_r ≅ H - v_r`
   (in which case swapping the two length-`r` path-branches at the unique center extends to
   `G ≃g H`), or the two diameter-`2r` cards swap sides, forcing `m_G = m_H + 1` and `m_G + 1 = m_H`
   for the minimum distance `m` from the center to a vertex of degree `≥ 3`.
4. If `|G₁| = r + 1` while `|H₁|, |H₂| ≥ r + 2`, bicentral cards force `|H₁| = |H₂| = r + 2` and
   `|G₂| = r + 3`, so `H` has exactly two degree-`3` vertices `a_i ∈ H₁, b_j ∈ H₂` (`0 ≤ i, j < r`)
   each adjacent to a leaf. Comparing `G - u_r ≅ H - b_r` with the bicentral cards forces
   `i = j ≤ r - 2` and `{d_p, d_q} = {i, i + 1}` in `G₂`, yielding a bicentral card of `G` whose
   unique degree-`3` vertex either lies at distance `i + 1 ≠ i` or has no leaf neighbor.
-/

namespace TreeH4Proof

open SimpleGraph Classical

/- ### Part 1: Basic graph isomorphism and tree-distance utilities -/

private lemma iso_edist_le {A B : Type} {R₁ : SimpleGraph A} {R₂ : SimpleGraph B}
    (φ : R₁ ≃g R₂) (x y : A) : R₂.edist (φ x) (φ y) ≤ R₁.edist x y := by
  rw [SimpleGraph.edist_eq_sInf]
  apply le_sInf
  rintro d ⟨p, rfl⟩
  exact (SimpleGraph.edist_le (p.map φ.toHom)).trans (by simp)

private lemma iso_edist_eq {A B : Type} {R₁ : SimpleGraph A} {R₂ : SimpleGraph B}
    (φ : R₁ ≃g R₂) (x y : A) : R₂.edist (φ x) (φ y) = R₁.edist x y := by
  apply le_antisymm (iso_edist_le φ x y)
  have h := iso_edist_le φ.symm (φ x) (φ y)
  simpa using h

private lemma iso_dist_eq {A B : Type} {R₁ : SimpleGraph A} {R₂ : SimpleGraph B}
    (φ : R₁ ≃g R₂) (x y : A) : R₂.dist (φ x) (φ y) = R₁.dist x y := by
  unfold SimpleGraph.dist
  rw [iso_edist_eq φ x y]

private lemma iso_neighborSet_ncard {A B : Type} [Fintype A] [Fintype B]
    {R₁ : SimpleGraph A} {R₂ : SimpleGraph B} (φ : R₁ ≃g R₂) (x : A) :
    (R₂.neighborSet (φ x)).ncard = (R₁.neighborSet x).ncard := by
  have himg : R₂.neighborSet (φ x) = φ '' R₁.neighborSet x := by
    ext y
    constructor
    · intro hy
      refine ⟨φ.symm y, ?_, φ.apply_symm_apply y⟩
      change R₁.Adj x (φ.symm y)
      rw [← φ.map_rel_iff, φ.apply_symm_apply]
      exact hy
    · rintro ⟨z, hz, rfl⟩
      exact φ.map_rel_iff.mpr hz
  rw [himg, Set.ncard_image_of_injective _ φ.injective]

private lemma iso_isTree {A B : Type} {R₁ : SimpleGraph A} {R₂ : SimpleGraph B}
    (φ : R₁ ≃g R₂) (h : R₁.IsTree) : R₂.IsTree := by
  haveI : Nonempty B := h.connected.nonempty.map φ
  refine ⟨⟨fun x y => ?_⟩, ?_⟩
  · obtain ⟨w⟩ := h.connected (φ.symm x) (φ.symm y)
    exact ⟨(w.map φ.toHom).copy (φ.apply_symm_apply x) (φ.apply_symm_apply y)⟩
  · intro x c hc
    have hc' : (c.map φ.symm.toHom).IsCycle := hc.map φ.symm.injective
    exact h.isAcyclic (c.map φ.symm.toHom) hc'

private lemma iso_diam_eq {A B : Type} {R₁ : SimpleGraph A} {R₂ : SimpleGraph B}
    (φ : R₁ ≃g R₂) : R₂.diam = R₁.diam := by
  unfold SimpleGraph.diam SimpleGraph.ediam SimpleGraph.eccent
  have h : (⨆ u : B, ⨆ v : B, R₂.edist u v) = ⨆ u : A, ⨆ v : A, R₁.edist u v := by
    rw [← Equiv.iSup_comp φ.toEquiv]
    apply iSup_congr; intro u
    rw [← Equiv.iSup_comp φ.toEquiv]
    apply iSup_congr; intro v
    exact iso_edist_eq φ u v
  rw [h]

private def iso_induce_congr {V : Type} {G : SimpleGraph V} {S₁ S₂ : Set V} (h : S₁ = S₂) :
    G.induce S₁ ≃g G.induce S₂ where
  toEquiv := Equiv.setCongr h
  map_rel_iff' := Iff.rfl

private lemma connected_ediam_ne_top {V : Type} [Fintype V] {T : SimpleGraph V}
    (hT : T.Connected) : T.ediam ≠ ⊤ := by
  apply ne_of_lt
  have hle : T.ediam ≤ (Fintype.card V : ℕ∞) := by
    unfold SimpleGraph.ediam
    apply iSup_le; intro u; apply iSup_le; intro v
    obtain ⟨p, hp_path, -⟩ := hT.exists_path_of_dist u v
    have hlen : p.length ≤ Fintype.card V := by
      have h1 := hp_path.support_nodup.length_le_card
      have h2 := p.length_support
      omega
    exact (SimpleGraph.edist_le p).trans (Nat.cast_le.mpr hlen)
  exact lt_of_le_of_lt hle (ENat.natCast_lt_top _)

private lemma connected_dist_le_diam {V : Type} [Fintype V] {T : SimpleGraph V}
    (hT : T.Connected) (x y : V) : T.dist x y ≤ T.diam :=
  T.dist_le_diam (connected_ediam_ne_top hT)

private lemma connected_exists_adj {V : Type} {T : SimpleGraph V} (hT : T.Connected)
    {a b : V} (hab : a ≠ b) : ∃ y : V, T.Adj a y := by
  obtain ⟨p⟩ := hT a b
  cases p with
  | nil => exact absurd rfl hab
  | cons h _ => exact ⟨_, h⟩

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

private lemma walk_getVert_dist_le {V : Type} {T : SimpleGraph V} (hT : T.Connected) :
    ∀ {a b : V} (p : T.Walk a b) (i : ℕ), T.dist a (p.getVert i) ≤ i
  | _, _, .nil, _ => by simp
  | _, _, .cons _ _, 0 => by simp
  | a, _, @Walk.cons _ _ _ v _ hadj p', i + 1 => by
    have h1 := walk_getVert_dist_le hT p' i
    have h2 := hT.dist_triangle (u := a) (v := v) (w := p'.getVert i)
    rw [dist_eq_one_iff_adj.mpr hadj] at h2
    simp only [Walk.getVert_cons_succ]
    omega

private lemma walk_getVert_dist_end_le {V : Type} {T : SimpleGraph V} :
    ∀ {a b : V} (p : T.Walk a b) (i : ℕ), T.dist (p.getVert i) b ≤ p.length - i
  | _, _, .nil, _ => by simp
  | _, _, .cons h p', 0 => by
    simp only [Walk.getVert_zero, Nat.sub_zero]
    exact SimpleGraph.dist_le (.cons h p')
  | _, _, .cons _ p', i + 1 => by
    simp only [Walk.getVert_cons_succ, Walk.length_cons, Nat.add_sub_add_right]
    exact walk_getVert_dist_end_le p' i

private lemma path_getVert_dist {V : Type} {T : SimpleGraph V} (hT : T.IsTree)
    {a b : V} (p : T.Walk a b) (hp : p.IsPath) (i : ℕ) (hi : i ≤ p.length) :
    T.dist a (p.getVert i) = i := by
  obtain ⟨w, hw_path, hw_len⟩ := hT.connected.exists_path_of_dist a b
  have huniq := (hT.existsUnique_path a b).unique hp hw_path
  have hplen : T.dist a b = p.length := by rw [← hw_len, ← congrArg Walk.length huniq]
  have h1 := walk_getVert_dist_le hT.connected p i
  have h2 := walk_getVert_dist_end_le p i
  have h3 := hT.connected.dist_triangle (u := a) (v := p.getVert i) (w := b)
  omega

private lemma getVert_concat_length {V : Type} {T : SimpleGraph V} :
    ∀ {a b c : V} (q : T.Walk a b) (h : T.Adj b c), (q.concat h).getVert q.length = b
  | _, _, _, .nil, _ => rfl
  | _, _, _, .cons _ q', h => getVert_concat_length q' h

private lemma tree_unique_parent {V : Type} {T : SimpleGraph V} (hT : T.IsTree)
    {r x : V} (hx : x ≠ r) :
    ∃! y : V, T.Adj x y ∧ T.dist y r + 1 = T.dist x r := by
  obtain ⟨p, hp_path, hp_len⟩ := hT.connected.exists_path_of_dist r x
  have hpos : 0 < p.length := by
    rw [hp_len]
    exact Nat.pos_of_ne_zero fun h0 => hx ((hT.connected.dist_eq_zero_iff.mp h0).symm)
  let y := p.getVert (p.length - 1)
  have hy_adj : T.Adj y x := by
    have h1 := p.adj_getVert_succ (by omega : p.length - 1 < p.length)
    have h2 : p.length - 1 + 1 = p.length := by omega
    rwa [h2, Walk.getVert_length] at h1
  have hy_dist : T.dist y r + 1 = T.dist x r := by
    rw [SimpleGraph.dist_comm (u := y) (v := r), SimpleGraph.dist_comm (u := x) (v := r)]
    have hd := path_getVert_dist hT p hp_path (p.length - 1) (by omega)
    rw [hd, ← hp_len]
    omega
  refine ⟨y, ⟨hy_adj.symm, hy_dist⟩, ?_⟩
  rintro z ⟨hz_adj, hz_dist⟩
  obtain ⟨qz, hqz_path, hqz_len⟩ := hT.connected.exists_path_of_dist r z
  have hx_not_mem : x ∉ qz.support := by
    intro hmem
    obtain ⟨k, hk, hkz⟩ := List.mem_iff_getElem.mp hmem
    have hkle : k ≤ qz.length := by have := qz.length_support; omega
    have hget : qz.getVert k = x := by rw [Walk.getVert_eq_support_getElem qz hkle]; exact hkz
    have hdx : T.dist r x = k := by rw [← hget]; exact path_getVert_dist hT qz hqz_path k hkle
    rw [SimpleGraph.dist_comm (u := r) (v := x)] at hdx
    rw [SimpleGraph.dist_comm (u := z) (v := r)] at hz_dist
    omega
  have hqz'_path : (qz.concat hz_adj.symm).IsPath := hqz_path.concat hx_not_mem hz_adj.symm
  have huniq := (hT.existsUnique_path r x).unique hqz'_path hp_path
  have hget : (qz.concat hz_adj.symm).getVert (p.length - 1) = y := by rw [huniq]
  have hlen_eq : qz.length = p.length - 1 := by
    have := congrArg Walk.length huniq
    rw [Walk.length_concat] at this
    omega
  rw [← hlen_eq, getVert_concat_length] at hget
  exact hget

private lemma tree_adj_dist_diff {V : Type} {T : SimpleGraph V} (hT : T.IsTree)
    {r x y : V} (hadj : T.Adj x y) :
    T.dist y r + 1 = T.dist x r ∨ T.dist x r + 1 = T.dist y r := by
  have h1 : T.dist x r ≤ T.dist y r + 1 := by
    have := hT.connected.dist_triangle (u := x) (v := y) (w := r)
    rw [dist_eq_one_iff_adj.mpr hadj] at this
    omega
  have h2 : T.dist y r ≤ T.dist x r + 1 := by
    have := hT.connected.dist_triangle (u := y) (v := x) (w := r)
    rw [dist_eq_one_iff_adj.mpr hadj.symm] at this
    omega
  by_contra hne
  have heq : T.dist x r = T.dist y r := by omega
  obtain ⟨px, hpx_path, hpx_len⟩ := hT.connected.exists_path_of_dist r x
  obtain ⟨py, hpy_path, hpy_len⟩ := hT.connected.exists_path_of_dist r y
  have hnot_y : y ∉ px.support := by
    intro hmem
    obtain ⟨k, hk, hkv⟩ := List.mem_iff_getElem.mp hmem
    have hkle : k ≤ px.length := by have := px.length_support; omega
    have hget : px.getVert k = y := by rw [Walk.getVert_eq_support_getElem px hkle]; exact hkv
    have hdy := path_getVert_dist hT px hpx_path k hkle
    rw [hget] at hdy
    have hkl : k = px.length := by
      rw [SimpleGraph.dist_comm (u := r) (v := y)] at hdy
      rw [SimpleGraph.dist_comm (u := x) (v := r)] at heq
      omega
    subst hkl
    rw [Walk.getVert_length] at hget
    exact hadj.ne hget
  have hconcat_path : (px.concat hadj).IsPath := hpx_path.concat hnot_y hadj
  have huniq := (hT.existsUnique_path r y).unique hconcat_path hpy_path
  have hlen := congrArg Walk.length huniq
  rw [Walk.length_concat, hpx_len, hpy_len, SimpleGraph.dist_comm (u := r) (v := x),
    SimpleGraph.dist_comm (u := r) (v := y)] at hlen
  omega

private lemma leaf_adj_unique {V : Type} [Fintype V] {T : SimpleGraph V} {v a b : V}
    (hleaf : (T.neighborSet v).ncard = 1) (ha : T.Adj v a) (hb : T.Adj v b) : a = b := by
  have hsub : ({a, b} : Set V) ⊆ T.neighborSet v := by
    rintro x (rfl | rfl) <;> assumption
  by_contra hne
  have h2 : ({a, b} : Set V).ncard = 2 := Set.ncard_pair hne
  have hle : ({a, b} : Set V).ncard ≤ (T.neighborSet v).ncard :=
    Set.ncard_le_ncard hsub (Set.toFinite _)
  omega

private lemma delete_leaf_isTree {V : Type} [Fintype V] {T : SimpleGraph V}
    (hT : T.IsTree) (hV : 2 ≤ Fintype.card V) {v : V} (hleaf : (T.neighborSet v).ncard = 1) :
    (T.induce ({v}ᶜ : Set V)).IsTree := by
  haveI : Nonempty ({v}ᶜ : Set V) := by
    by_contra hemp
    rw [not_nonempty_iff] at hemp
    have hcard : Fintype.card V ≤ 1 := by
      have : ∀ x : V, x = v := fun x => by
        by_contra hx
        exact IsEmpty.false (⟨x, hx⟩ : ({v}ᶜ : Set V))
      have : Subsingleton V := ⟨fun a b => (this a).trans (this b).symm⟩
      exact Fintype.card_le_one_iff_subsingleton.mpr this
    omega
  refine ⟨⟨fun x y => ?_⟩, ?_⟩
  · obtain ⟨p, hp_path, -⟩ := hT.connected.exists_path_of_dist x.1 y.1
    have hv_not : v ∉ p.support := by
      intro hmem
      obtain ⟨k, hk, hkv⟩ := List.mem_iff_getElem.mp hmem
      have hkle : k ≤ p.length := by have := p.length_support; omega
      have hget : p.getVert k = v := by rw [Walk.getVert_eq_support_getElem p hkle]; exact hkv
      have hk0 : 0 < k := by
        by_contra h0
        have hk0' : k = 0 := by omega
        subst hk0'
        rw [Walk.getVert_zero] at hget
        exact x.2 hget
      have hkl : k < p.length := by
        by_contra hge
        have hkeq : k = p.length := by omega
        subst hkeq
        rw [Walk.getVert_length] at hget
        exact y.2 hget
      have hadj1 : T.Adj (p.getVert (k - 1)) v := by
        have h1 := p.adj_getVert_succ (by omega : k - 1 < p.length)
        rwa [show k - 1 + 1 = k by omega, hget] at h1
      have hadj2 : T.Adj v (p.getVert (k + 1)) := by
        have h1 := p.adj_getVert_succ hkl
        rwa [hget] at h1
      have heq := leaf_adj_unique hleaf hadj1.symm hadj2
      have hnodup := hp_path.support_nodup
      have h1_eq : p.support[k - 1]'(by have := p.length_support; omega) = p.getVert (k - 1) :=
        (Walk.getVert_eq_support_getElem p (by omega)).symm
      have h2_eq : p.support[k + 1]'(by have := p.length_support; omega) = p.getVert (k + 1) :=
        (Walk.getVert_eq_support_getElem p (by omega)).symm
      have hidx := (List.Nodup.getElem_inj_iff hnodup).mp (h1_eq.trans (heq.trans h2_eq.symm))
      omega
    exact ⟨p.induce ({v}ᶜ : Set V) fun u hu => fun huv => hv_not (huv ▸ hu)⟩
  · intro x c hc
    let f : T.induce ({v}ᶜ : Set V) →g T := (SimpleGraph.Embedding.induce _).toHom
    exact hT.isAcyclic (c.map f) (hc.map Subtype.val_injective)

private lemma delete_nonleaf_not_isTree {V : Type} [Fintype V] {T : SimpleGraph V}
    (hT : T.IsTree) {v : V} (hdeg : 2 ≤ (T.neighborSet v).ncard) :
    ¬ (T.induce ({v}ᶜ : Set V)).IsTree := by
  intro hsub
  obtain ⟨a, ha, b, hb, hab⟩ := (Set.one_lt_ncard (Set.toFinite _)).mp (by omega : 1 < (T.neighborSet v).ncard)
  have hav : a ≠ v := (ha.ne).symm
  have hbv : b ≠ v := (hb.ne).symm
  obtain ⟨p, hp_path, -⟩ := hsub.connected.exists_path_of_dist ⟨a, hav⟩ ⟨b, hbv⟩
  let f : T.induce ({v}ᶜ : Set V) →g T := (SimpleGraph.Embedding.induce _).toHom
  have hp'_path : (p.map f).IsPath :=
    (Walk.isPath_def _).mpr (by rw [Walk.support_map]; exact hp_path.support_nodup.map Subtype.val_injective)
  have hv_not : v ∉ (p.map f).support := by
    rw [Walk.support_map, List.mem_map]
    rintro ⟨u, -, hu⟩
    exact u.2 hu
  let q : T.Walk a b := Walk.cons ha.symm (Walk.cons hb Walk.nil)
  have hq_path : q.IsPath := by
    rw [Walk.isPath_def]
    show ([a, v, b] : List V).Nodup
    simp [hav, hab, hbv.symm]
  have huniq := (hT.existsUnique_path a b).unique hp'_path hq_path
  have hv_in : v ∈ q.support := by simp [q]
  rw [← huniq] at hv_in
  exact hv_not hv_in

private lemma delete_leaf_dist {V : Type} [Fintype V] {T : SimpleGraph V}
    (hT : T.IsTree) (hV : 2 ≤ Fintype.card V) {v : V} (hleaf : (T.neighborSet v).ncard = 1)
    (x y : ({v}ᶜ : Set V)) : (T.induce ({v}ᶜ : Set V)).dist x y = T.dist x.1 y.1 :=
  induce_dist_eq hT (delete_leaf_isTree hT hV hleaf) x y

private lemma neighborSet_induce_compl_ncard_of_not_adj {V : Type} [Fintype V]
    {T : SimpleGraph V} {v : V} {x : ({v}ᶜ : Set V)} (hnadj : ¬ T.Adj x.1 v) :
    ((T.induce ({v}ᶜ : Set V)).neighborSet x).ncard = (T.neighborSet x.1).ncard := by
  have himg : T.neighborSet x.1 = Subtype.val '' (T.induce ({v}ᶜ : Set V)).neighborSet x := by
    ext y
    constructor
    · intro hy
      have hyv : y ≠ v := fun h => hnadj (h ▸ hy)
      exact ⟨⟨y, hyv⟩, hy, rfl⟩
    · rintro ⟨⟨z, _⟩, hz, rfl⟩
      exact hz
  rw [himg, Set.ncard_image_of_injective _ Subtype.val_injective]

private lemma neighborSet_induce_compl_ncard_of_adj {V : Type} [Fintype V]
    {T : SimpleGraph V} {v : V} {x : ({v}ᶜ : Set V)} (hadj : T.Adj x.1 v) :
    ((T.induce ({v}ᶜ : Set V)).neighborSet x).ncard + 1 = (T.neighborSet x.1).ncard := by
  have himg : T.neighborSet x.1 = insert v (Subtype.val '' (T.induce ({v}ᶜ : Set V)).neighborSet x) := by
    ext y
    constructor
    · intro hy
      by_cases hyv : y = v
      · exact Or.inl hyv
      · exact Or.inr ⟨⟨y, hyv⟩, hy, rfl⟩
    · rintro (rfl | ⟨⟨z, _⟩, hz, rfl⟩)
      · exact hadj
      · exact hz
  have hnot : v ∉ Subtype.val '' (T.induce ({v}ᶜ : Set V)).neighborSet x := by
    rintro ⟨⟨z, hzv⟩, _, hz⟩
    exact hzv hz
  rw [himg, Set.ncard_insert_of_notMem hnot (Set.toFinite _),
    Set.ncard_image_of_injective _ Subtype.val_injective]

/- ### Part 2: Bicenter structure, unique center, and limb analysis -/

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

private abbrev BicenterData.swap {V : Type} [Fintype V] {T : SimpleGraph V} {r : ℕ}
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

private abbrev BicenterData.side₁ {V : Type} [Fintype V] {T : SimpleGraph V} {r : ℕ}
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
  have h : D.side₁ = (D.A₁ : Set V) := by ext x; exact (mem_A₁_iff D).symm
  rw [h, Set.ncard_coe_finset]

private lemma mem_side₁_self {V : Type} [Fintype V] {T : SimpleGraph V} {r : ℕ}
    (D : BicenterData T r) : D.c₁ ∈ D.side₁ := by
  simp only [BicenterData.side₁, Set.mem_ofPred_eq, SimpleGraph.dist_self, dist_eq_one_iff_adj.mpr D.hadj]
  omega

private lemma mem_swap_side₁_of_not_mem {V : Type} [Fintype V] {T : SimpleGraph V} {r : ℕ}
    (D : BicenterData T r) {x : V} (hx : x ∉ D.side₁) : x ∈ D.swap.side₁ :=
  (lt_or_gt_of_ne (D.hne x)).resolve_left (by simpa [BicenterData.side₁] using hx)

private lemma c₂_not_mem_side₁ {V : Type} [Fintype V] {T : SimpleGraph V} {r : ℕ}
    (D : BicenterData T r) : D.c₂ ∉ D.side₁ := by
  intro h
  change T.dist D.c₂ D.c₁ < T.dist D.c₂ D.c₂ at h
  rw [SimpleGraph.dist_self] at h
  omega

private lemma not_mem_side₁_of_mem_swap {V : Type} [Fintype V] {T : SimpleGraph V} {r : ℕ}
    (D : BicenterData T r) {x : V} (hx : x ∈ D.swap.side₁) : x ∉ D.side₁ := by
  intro h1
  change T.dist x D.c₁ < T.dist x D.c₂ at h1
  change T.dist x D.c₂ < T.dist x D.c₁ at hx
  omega

private lemma card_A₁_add_swap {V : Type} [Fintype V] {T : SimpleGraph V} {r : ℕ}
    (D : BicenterData T r) : D.A₁.card + D.swap.A₁.card = Fintype.card V := by
  have hdisj : Disjoint D.A₁ D.swap.A₁ := by
    rw [Finset.disjoint_left]
    intro x h1 h2
    exact not_mem_side₁_of_mem_swap D ((mem_A₁_iff D.swap).mp h2) ((mem_A₁_iff D).mp h1)
  have hunion : D.A₁ ∪ D.swap.A₁ = Finset.univ := by
    ext x
    simp only [Finset.mem_union, Finset.mem_univ, iff_true, mem_A₁_iff]
    exact lt_or_gt_of_ne (D.hne x)
  rw [← Finset.card_union_of_disjoint hdisj, hunion, Finset.card_univ]

private lemma eq_center_of_adj_across {V : Type} [Fintype V] {T : SimpleGraph V} {r : ℕ}
    (D : BicenterData T r) {x y : V} (hx : x ∈ D.side₁) (hy : y ∈ D.swap.side₁)
    (hadj : T.Adj x y) : x = D.c₁ ∧ y = D.c₂ := by
  have h1 : T.dist x y = 1 := dist_eq_one_iff_adj.mpr hadj
  have h2 := D.hdist x y hx hy
  have hx0 : T.dist x D.c₁ = 0 := by omega
  have hy0 : T.dist D.c₂ y = 0 := by omega
  exact ⟨D.hT.connected.dist_eq_zero_iff.mp hx0, (D.hT.connected.dist_eq_zero_iff.mp hy0).symm⟩

private lemma dist_c₂_of_side₁ {V : Type} [Fintype V] {T : SimpleGraph V} {r : ℕ}
    (D : BicenterData T r) {x : V} (hx : x ∈ D.side₁) :
    T.dist x D.c₂ = T.dist x D.c₁ + 1 := by
  have h := D.hdist x D.c₂ hx (mem_side₁_self D.swap)
  rw [SimpleGraph.dist_self, add_zero] at h
  exact h

private lemma exists_far_vertex {V : Type} [Fintype V] {T : SimpleGraph V} {r : ℕ}
    (D : BicenterData T r) : ∃ a : V, a ∈ D.side₁ ∧ T.dist a D.c₁ = r := by
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
    exact ⟨x, hx, by omega⟩
  · have hdeq := D.hdist y x hy hx
    have h1 := D.hle₁ y hy
    have h2 := D.hle₂ x hx
    rw [SimpleGraph.dist_comm (u := x) (v := y)] at hxy_r
    rw [SimpleGraph.dist_comm (u := D.c₂) (v := x)] at hdeq
    exact ⟨y, hy, by omega⟩
  · exfalso; have := htri₂ x y hx hy; omega

private lemma exists_leg_in_side₁ {V : Type} [Fintype V] {T : SimpleGraph V} {r : ℕ}
    (D : BicenterData T r) :
    ∃ u : Fin (r + 1) → V,
      u 0 = D.c₁ ∧
      (∀ i : Fin (r + 1), u i ∈ D.side₁) ∧
      (∀ i : Fin (r + 1), T.dist (u i) D.c₁ = i.1) ∧
      Function.Injective u ∧
      (∀ i j : Fin (r + 1), T.Adj (u i) (u j) ↔ i.1 + 1 = j.1 ∨ j.1 + 1 = i.1) := by
  obtain ⟨a, ha_side, ha_dist⟩ := exists_far_vertex D
  have hdist_sub : (T.induce D.side₁).dist ⟨D.c₁, mem_side₁_self D⟩ ⟨a, ha_side⟩ = r := by
    rw [induce_dist_eq D.hT D.ht₁, SimpleGraph.dist_comm, ha_dist]
  obtain ⟨p, hp_path, hp_len⟩ := D.ht₁.connected.exists_path_of_dist ⟨D.c₁, mem_side₁_self D⟩ ⟨a, ha_side⟩
  have hplen : p.length = r := hp_len.trans hdist_sub
  let u : Fin (r + 1) → V := fun i => (p.getVert i.1).1
  have hu0 : u 0 = D.c₁ := by simp [u]
  have huside : ∀ i : Fin (r + 1), u i ∈ D.side₁ := fun i => (p.getVert i.1).2
  have hudist : ∀ i : Fin (r + 1), T.dist (u i) D.c₁ = i.1 := by
    intro i
    have hi : i.1 ≤ p.length := by omega
    have h1 := path_getVert_dist D.ht₁ p hp_path i.1 hi
    rw [induce_dist_eq D.hT D.ht₁, SimpleGraph.dist_comm] at h1
    exact h1
  have huinj : Function.Injective u := fun i j hij =>
    Fin.ext (by rw [← hudist i, ← hudist j, hij])
  have huadj : ∀ i j : Fin (r + 1), T.Adj (u i) (u j) ↔ i.1 + 1 = j.1 ∨ j.1 + 1 = i.1 := by
    intro i j
    constructor
    · intro hadj
      rcases tree_adj_dist_diff D.hT (r := D.c₁) hadj with h | h
      · right; rw [hudist i, hudist j] at h; exact h
      · left; rw [hudist i, hudist j] at h; exact h
    · rintro (h | h)
      · have hilt : i.1 < p.length := by omega
        have h1 := p.adj_getVert_succ hilt
        change T.Adj (u i) (p.getVert (i.1 + 1)).1 at h1
        have heq : (p.getVert (i.1 + 1)).1 = u j := by
          dsimp only [u]; rw [h]
        rwa [heq] at h1
      · have hjlt : j.1 < p.length := by omega
        have h1 := p.adj_getVert_succ hjlt
        change T.Adj (u j) (p.getVert (j.1 + 1)).1 at h1
        have heq : (p.getVert (j.1 + 1)).1 = u i := by
          dsimp only [u]; rw [h]
        rw [heq] at h1
        exact h1.symm
  exact ⟨u, hu0, huside, hudist, huinj, huadj⟩

private lemma limb_card_ge {V : Type} [Fintype V] {T : SimpleGraph V} {r : ℕ}
    (D : BicenterData T r) : r + 1 ≤ D.A₁.card := by
  obtain ⟨u, -, huside, -, huinj, -⟩ := exists_leg_in_side₁ D
  have hsub : Finset.univ.image u ⊆ D.A₁ := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨i, -, rfl⟩
    exact (mem_A₁_iff D).mpr (huside i)
  have hcard : (Finset.univ.image u).card = r + 1 := by
    rw [Finset.card_image_of_injective _ huinj, Finset.card_univ, Fintype.card_fin]
  rw [← hcard]
  exact Finset.card_le_card hsub

/- ### Part 3: Path-limb (`|A₁| = r + 1`) and near-path-limb (`|A₁| = r + 2`) structure -/

private lemma path_limb_spec {V : Type} [Fintype V] {T : SimpleGraph V} {r : ℕ}
    (D : BicenterData T r) (hsmall : D.A₁.card ≤ r + 1) :
    ∃ u : Fin (r + 1) → V,
      u 0 = D.c₁ ∧
      (∀ x : V, x ∈ D.side₁ ↔ ∃ i : Fin (r + 1), u i = x) ∧
      (∀ i : Fin (r + 1), T.dist (u i) D.c₁ = i.1) ∧
      Function.Injective u ∧
      (∀ i j : Fin (r + 1), T.Adj (u i) (u j) ↔ i.1 + 1 = j.1 ∨ j.1 + 1 = i.1) ∧
      (T.neighborSet (u ⟨r, Nat.lt_succ_self r⟩) = {u ⟨r - 1, by have := D.hr; omega⟩}) ∧
      (∀ i : Fin (r + 1), i.1 < r → (T.neighborSet (u i)).ncard = 2) ∧
      (∀ x ∈ D.side₁, (T.neighborSet x).ncard ≤ 2) := by
  obtain ⟨u, hu0, huside, hudist, huinj, huadj⟩ := exists_leg_in_side₁ D
  have hsub : Finset.univ.image u ⊆ D.A₁ := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨i, -, rfl⟩
    exact (mem_A₁_iff D).mpr (huside i)
  have himg_card : (Finset.univ.image u).card = r + 1 := by
    rw [Finset.card_image_of_injective _ huinj, Finset.card_univ, Fintype.card_fin]
  have hEq : Finset.univ.image u = D.A₁ :=
    Finset.eq_of_subset_of_card_le hsub (by omega)
  have hmem : ∀ x : V, x ∈ D.side₁ ↔ ∃ i : Fin (r + 1), u i = x := by
    intro x
    rw [← mem_A₁_iff D, ← hEq, Finset.mem_image]
    simp
  have hlast_nb : T.neighborSet (u ⟨r, Nat.lt_succ_self r⟩) = {u ⟨r - 1, by have := D.hr; omega⟩} := by
    ext y
    simp only [mem_neighborSet, Set.mem_singleton_iff]
    constructor
    · intro hadj
      by_cases hy : y ∈ D.side₁
      · obtain ⟨j, rfl⟩ := (hmem y).mp hy
        rw [huadj] at hadj; dsimp only at hadj
        have hjeq : j = ⟨r - 1, by have := D.hr; omega⟩ := by
          apply Fin.ext; dsimp only; have := j.isLt; have := D.hr; omega
        rw [hjeq]
      · have hy2 := mem_swap_side₁_of_not_mem D hy
        obtain ⟨hc1, -⟩ := eq_center_of_adj_across D (huside ⟨r, Nat.lt_succ_self r⟩) hy2 hadj
        have h0 := hudist ⟨r, Nat.lt_succ_self r⟩
        rw [hc1, SimpleGraph.dist_self] at h0
        dsimp only at h0; have := D.hr; omega
    · rintro rfl
      rw [huadj]; right; dsimp only; have := D.hr; omega
  have hmid_deg : ∀ i : Fin (r + 1), i.1 < r → (T.neighborSet (u i)).ncard = 2 := by
    intro i hi
    by_cases hi0 : i.1 = 0
    · have hi' : i = 0 := Fin.ext hi0
      subst hi'
      have hnb : T.neighborSet (u 0) = {D.c₂, u ⟨1, by have := D.hr; omega⟩} := by
        ext y
        simp only [mem_neighborSet, Set.mem_insert_iff, Set.mem_singleton_iff]
        constructor
        · intro hadj
          by_cases hy : y ∈ D.side₁
          · obtain ⟨j, rfl⟩ := (hmem y).mp hy
            rw [huadj] at hadj; simp only [Fin.val_zero] at hadj
            right; congr 1; apply Fin.ext; dsimp only; omega
          · have hy2 := mem_swap_side₁_of_not_mem D hy
            exact Or.inl (eq_center_of_adj_across D (huside 0) hy2 hadj).2
        · rintro (rfl | rfl)
          · rw [hu0]; exact D.hadj
          · rw [huadj]; left; simp
      have hne : D.c₂ ≠ u ⟨1, by have := D.hr; omega⟩ := fun h =>
        c₂_not_mem_side₁ D (by rw [h]; exact huside ⟨1, by have := D.hr; omega⟩)
      rw [hnb, Set.ncard_pair hne]
    · have hnb : T.neighborSet (u i) =
          {u ⟨i.1 - 1, by omega⟩, u ⟨i.1 + 1, by omega⟩} := by
        ext y
        simp only [mem_neighborSet, Set.mem_insert_iff, Set.mem_singleton_iff]
        constructor
        · intro hadj
          by_cases hy : y ∈ D.side₁
          · obtain ⟨j, rfl⟩ := (hmem y).mp hy
            rw [huadj] at hadj
            rcases hadj with h | h
            · right; congr 1; apply Fin.ext; dsimp only; omega
            · left; congr 1; apply Fin.ext; dsimp only; omega
          · have hy2 := mem_swap_side₁_of_not_mem D hy
            obtain ⟨hc1, -⟩ := eq_center_of_adj_across D (huside i) hy2 hadj
            have h0 := hudist i
            rw [hc1, SimpleGraph.dist_self] at h0
            omega
        · rintro (rfl | rfl)
          · rw [huadj]; right; dsimp only; omega
          · rw [huadj]; left; dsimp only
      have hne : u ⟨i.1 - 1, by omega⟩ ≠ u ⟨i.1 + 1, by omega⟩ := fun h => by
        have := congrArg Fin.val (huinj h); dsimp only at this; omega
      rw [hnb, Set.ncard_pair hne]
  have hle2 : ∀ x ∈ D.side₁, (T.neighborSet x).ncard ≤ 2 := by
    intro x hx
    obtain ⟨i, rfl⟩ := (hmem x).mp hx
    by_cases hir : i.1 < r
    · rw [hmid_deg i hir]
    · have hieq : i = ⟨r, Nat.lt_succ_self r⟩ := Fin.ext (by dsimp only; have := i.isLt; omega)
      rw [hieq, hlast_nb, Set.ncard_singleton]; omega
  exact ⟨u, hu0, hmem, hudist, huinj, huadj, hlast_nb, hmid_deg, hle2⟩

private lemma exists_diam_preserving_leaf_of_big_limb {V : Type} [Fintype V] {T : SimpleGraph V}
    {r : ℕ} (D : BicenterData T r) (hbig : r + 2 ≤ D.A₁.card) :
    ∃ v ∈ D.side₁, (T.neighborSet v).ncard = 1 ∧ ∃ a ∈ D.side₁, a ≠ v ∧ T.dist a D.c₁ = r := by
  obtain ⟨u, hu0, huside, hudist, huinj, huadj⟩ := exists_leg_in_side₁ D
  let P : Finset V := Finset.univ.image u
  have hPsub : P ⊆ D.A₁ := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨i, -, rfl⟩
    exact (mem_A₁_iff D).mpr (huside i)
  have hPcard : P.card = r + 1 := by
    rw [Finset.card_image_of_injective _ huinj, Finset.card_univ, Fintype.card_fin]
  have hrem_ne : (D.A₁ \ P).Nonempty := by
    rw [← Finset.card_pos, Finset.card_sdiff_of_subset hPsub]
    omega
  obtain ⟨v, hv_mem, hv_max⟩ := Finset.exists_max_image (D.A₁ \ P) (fun x => T.dist x D.c₁) hrem_ne
  have hv_side : v ∈ D.side₁ := (mem_A₁_iff D).mp (Finset.mem_sdiff.mp hv_mem).1
  have hv_notP : v ∉ P := (Finset.mem_sdiff.mp hv_mem).2
  have hv_nec₁ : v ≠ D.c₁ := fun h => hv_notP (Finset.mem_image.mpr ⟨0, Finset.mem_univ _, hu0.trans h.symm⟩)
  obtain ⟨pv, ⟨hpv_adj, hpv_dist⟩, hpv_uniq⟩ := tree_unique_parent D.hT hv_nec₁
  have hv_nb : T.neighborSet v = {pv} := by
    ext y
    simp only [mem_neighborSet, Set.mem_singleton_iff]
    constructor
    · intro hadj
      rcases tree_adj_dist_diff D.hT (r := D.c₁) hadj with h | h
      · exact hpv_uniq y ⟨hadj, h⟩
      · exfalso
        -- y has strictly larger distance to c₁ than v
        by_cases hy_side : y ∈ D.side₁
        · by_cases hyP : y ∈ P
          · -- If y ∈ P, then v is the unique parent of y toward c₁, so v ∈ P!
            rcases Finset.mem_image.mp hyP with ⟨j, -, rfl⟩
            have hjpos : 0 < j.1 := by
              have hdj := hudist j; omega
            have hj_nec₁ : u j ≠ D.c₁ := fun h0 => by
              have hdj := hudist j; rw [h0, SimpleGraph.dist_self] at hdj; omega
            have hpred_adj : T.Adj (u j) (u ⟨j.1 - 1, by omega⟩) := by
              rw [huadj]; right; dsimp only; omega
            have hpred_dist : T.dist (u ⟨j.1 - 1, by omega⟩) D.c₁ + 1 = T.dist (u j) D.c₁ := by
              rw [hudist, hudist]; dsimp only; omega
            have huniq_y := tree_unique_parent D.hT hj_nec₁
            have hv_eq : v = u ⟨j.1 - 1, by omega⟩ :=
              (huniq_y.unique ⟨hadj.symm, h⟩ ⟨hpred_adj, hpred_dist⟩)
            exact hv_notP (Finset.mem_image.mpr ⟨⟨j.1 - 1, by omega⟩, Finset.mem_univ _, hv_eq.symm⟩)
          · have hy_rem : y ∈ D.A₁ \ P := Finset.mem_sdiff.mpr ⟨(mem_A₁_iff D).mpr hy_side, hyP⟩
            have hle := hv_max y hy_rem
            omega
        · have hy2 := mem_swap_side₁_of_not_mem D hy_side
          exact hv_nec₁ (eq_center_of_adj_across D hv_side hy2 hadj).1
    · rintro rfl; exact hpv_adj
  refine ⟨v, hv_side, by rw [hv_nb, Set.ncard_singleton], u ⟨r, Nat.lt_succ_self r⟩,
    huside _, ?_, hudist _⟩
  intro hEq
  exact hv_notP (Finset.mem_image.mpr ⟨⟨r, Nat.lt_succ_self r⟩, Finset.mem_univ _, hEq⟩)

private lemma limb_card_eq_r_add_two_spec {V : Type} [Fintype V] {T : SimpleGraph V} {r : ℕ}
    (D : BicenterData T r) (hcard : D.A₁.card = r + 2) :
    ∃ (u : Fin (r + 1) → V) (x : V) (i : Fin r),
      u 0 = D.c₁ ∧
      x ∈ D.side₁ ∧
      (∀ k : Fin (r + 1), u k ∈ D.side₁) ∧
      (∀ k : Fin (r + 1), T.dist (u k) D.c₁ = k.1) ∧
      Function.Injective u ∧
      (∀ k : Fin (r + 1), x ≠ u k) ∧
      (∀ y : V, y ∈ D.side₁ ↔ y = x ∨ ∃ k : Fin (r + 1), u k = y) ∧
      T.neighborSet x = {u ⟨i.1, by omega⟩} ∧
      T.neighborSet (u ⟨r, Nat.lt_succ_self r⟩) = {u ⟨r - 1, by have := D.hr; omega⟩} ∧
      (T.neighborSet (u ⟨i.1, by omega⟩)).ncard = 3 ∧
      (∀ k : Fin (r + 1), k.1 ≠ i.1 → k.1 < r → (T.neighborSet (u k)).ncard = 2) ∧
      T.dist x D.c₁ = i.1 + 1 := by
  obtain ⟨u, hu0, huside, hudist, huinj, huadj⟩ := exists_leg_in_side₁ D
  let P : Finset V := Finset.univ.image u
  have hPsub : P ⊆ D.A₁ := by
    intro y hy
    rcases Finset.mem_image.mp hy with ⟨k, -, rfl⟩
    exact (mem_A₁_iff D).mpr (huside k)
  have hPcard : P.card = r + 1 := by
    rw [Finset.card_image_of_injective _ huinj, Finset.card_univ, Fintype.card_fin]
  have hrem_card : (D.A₁ \ P).card = 1 := by
    rw [Finset.card_sdiff_of_subset hPsub]; omega
  obtain ⟨x, hx_eq⟩ := Finset.card_eq_one.mp hrem_card
  have hx_mem : x ∈ D.A₁ \ P := by rw [hx_eq]; exact Finset.mem_singleton_self x
  have hx_side : x ∈ D.side₁ := (mem_A₁_iff D).mp (Finset.mem_sdiff.mp hx_mem).1
  have hx_notP : x ∉ P := (Finset.mem_sdiff.mp hx_mem).2
  have hx_ne : ∀ k : Fin (r + 1), x ≠ u k := fun k h =>
    hx_notP (Finset.mem_image.mpr ⟨k, Finset.mem_univ _, h.symm⟩)
  have hx_nec₁ : x ≠ D.c₁ := hu0 ▸ hx_ne 0
  have hmem_side : ∀ y : V, y ∈ D.side₁ ↔ y = x ∨ ∃ k : Fin (r + 1), u k = y := by
    intro y
    rw [← mem_A₁_iff D]
    constructor
    · intro hy
      by_cases hyP : y ∈ P
      · rcases Finset.mem_image.mp hyP with ⟨k, -, rfl⟩
        exact Or.inr ⟨k, rfl⟩
      · have hyrem : y ∈ D.A₁ \ P := Finset.mem_sdiff.mpr ⟨hy, hyP⟩
        rw [hx_eq, Finset.mem_singleton] at hyrem
        exact Or.inl hyrem
    · rintro (rfl | ⟨k, rfl⟩)
      · exact (mem_A₁_iff D).mpr hx_side
      · exact (mem_A₁_iff D).mpr (huside k)
  obtain ⟨px, ⟨hpx_adj, hpx_dist⟩, hpx_uniq⟩ := tree_unique_parent D.hT hx_nec₁
  have hpx_side : px ∈ D.side₁ := by
    by_contra hnot
    exact hx_nec₁ (eq_center_of_adj_across D hx_side (mem_swap_side₁_of_not_mem D hnot) hpx_adj).1
  have hpx_inP : ∃ k : Fin (r + 1), u k = px := by
    rcases (hmem_side px).mp hpx_side with rfl | hk
    · exact absurd rfl hpx_adj.ne
    · exact hk
  obtain ⟨i0, hi0_eq⟩ := hpx_inP
  have hi0_lt : i0.1 < r := by
    have h1 := D.hle₁ x hx_side
    have h2 := hudist i0
    rw [hi0_eq] at h2
    omega
  let i : Fin r := ⟨i0.1, hi0_lt⟩
  have hui_eq : u ⟨i.1, by omega⟩ = px := by
    have : (⟨i.1, by omega⟩ : Fin (r + 1)) = i0 := Fin.ext rfl
    rw [this, hi0_eq]
  have hx_dist : T.dist x D.c₁ = i.1 + 1 := by
    rw [← hpx_dist, ← hui_eq, hudist]
  have hx_nb : T.neighborSet x = {u ⟨i.1, by omega⟩} := by
    ext y
    simp only [mem_neighborSet, Set.mem_singleton_iff]
    constructor
    · intro hadj
      rcases tree_adj_dist_diff D.hT (r := D.c₁) hadj with h | h
      · rw [hui_eq]; exact hpx_uniq y ⟨hadj, h⟩
      · exfalso
        by_cases hy_side : y ∈ D.side₁
        · rcases (hmem_side y).mp hy_side with rfl | ⟨j, rfl⟩
          · exact hadj.ne rfl
          · have hjpos : 0 < j.1 := by have := hudist j; omega
            have hj_nec₁ : u j ≠ D.c₁ := fun h0 => by
              have := hudist j; rw [h0, SimpleGraph.dist_self] at this; omega
            have hpred_adj : T.Adj (u j) (u ⟨j.1 - 1, by omega⟩) := by
              rw [huadj]; right; dsimp only; omega
            have hpred_dist : T.dist (u ⟨j.1 - 1, by omega⟩) D.c₁ + 1 = T.dist (u j) D.c₁ := by
              rw [hudist, hudist]; dsimp only; omega
            have huniq_y := tree_unique_parent D.hT hj_nec₁
            have hx_eq' : x = u ⟨j.1 - 1, by omega⟩ :=
              huniq_y.unique ⟨hadj.symm, h⟩ ⟨hpred_adj, hpred_dist⟩
            exact hx_ne ⟨j.1 - 1, by omega⟩ hx_eq'
        · exact hx_nec₁ (eq_center_of_adj_across D hx_side (mem_swap_side₁_of_not_mem D hy_side) hadj).1
    · rintro rfl; rw [hui_eq]; exact hpx_adj
  have hlast_nb : T.neighborSet (u ⟨r, Nat.lt_succ_self r⟩) = {u ⟨r - 1, by have := D.hr; omega⟩} := by
    ext y
    simp only [mem_neighborSet, Set.mem_singleton_iff]
    constructor
    · intro hadj
      by_cases hy_side : y ∈ D.side₁
      · rcases (hmem_side y).mp hy_side with hyx | ⟨j, rfl⟩
        · rw [hyx] at hadj
          have hmem' : u ⟨r, Nat.lt_succ_self r⟩ ∈ T.neighborSet x := hadj.symm
          rw [hx_nb, Set.mem_singleton_iff] at hmem'
          have := congrArg Fin.val (huinj hmem'); dsimp only at this; omega
        · rw [huadj] at hadj; dsimp only at hadj
          congr 1; apply Fin.ext; dsimp only; have := j.isLt; have := D.hr; omega
      · obtain ⟨hc1, -⟩ := eq_center_of_adj_across D (huside ⟨r, Nat.lt_succ_self r⟩)
          (mem_swap_side₁_of_not_mem D hy_side) hadj
        have := hudist ⟨r, Nat.lt_succ_self r⟩; rw [hc1, SimpleGraph.dist_self] at this; dsimp only at this; have := D.hr; omega
    · rintro rfl; rw [huadj]; right; dsimp only; have := D.hr; omega
  -- Helper for neighbors of u k (k < r)
  have hnb_of_uk : ∀ k : Fin (r + 1), k.1 < r →
      (T.neighborSet (u k) \ {x}).ncard = 2 := by
    intro k hk
    by_cases hk0 : k.1 = 0
    · have hk' : k = 0 := Fin.ext hk0; subst hk'
      have hset : T.neighborSet (u 0) \ {x} = {D.c₂, u ⟨1, by have := D.hr; omega⟩} := by
        ext y
        simp only [Set.mem_sdiff, mem_neighborSet, Set.mem_singleton_iff, Set.mem_insert_iff]
        constructor
        · rintro ⟨hadj, hyx⟩
          by_cases hy : y ∈ D.side₁
          · rcases (hmem_side y).mp hy with rfl | ⟨j, rfl⟩
            · exact absurd rfl hyx
            · rw [huadj] at hadj; simp only [Fin.val_zero] at hadj; right; congr 1; apply Fin.ext; dsimp only; omega
          · exact Or.inl (eq_center_of_adj_across D (huside 0) (mem_swap_side₁_of_not_mem D hy) hadj).2
        · rintro (rfl | rfl)
          · refine ⟨by rw [hu0]; exact D.hadj, fun h => c₂_not_mem_side₁ D (by rw [h]; exact hx_side)⟩
          · exact ⟨by rw [huadj]; left; simp, (hx_ne _).symm⟩
      have hne : D.c₂ ≠ u ⟨1, by have := D.hr; omega⟩ := fun h =>
        c₂_not_mem_side₁ D (by rw [h]; exact huside _)
      rw [hset, Set.ncard_pair hne]
    · have hset : T.neighborSet (u k) \ {x} =
          {u ⟨k.1 - 1, by omega⟩, u ⟨k.1 + 1, by omega⟩} := by
        ext y
        simp only [Set.mem_sdiff, mem_neighborSet, Set.mem_singleton_iff, Set.mem_insert_iff]
        constructor
        · rintro ⟨hadj, hyx⟩
          by_cases hy : y ∈ D.side₁
          · rcases (hmem_side y).mp hy with rfl | ⟨j, rfl⟩
            · exact absurd rfl hyx
            · rw [huadj] at hadj
              rcases hadj with h | h
              · right; congr 1; apply Fin.ext; dsimp only; omega
              · left; congr 1; apply Fin.ext; dsimp only; omega
          · obtain ⟨hc1, -⟩ := eq_center_of_adj_across D (huside k) (mem_swap_side₁_of_not_mem D hy) hadj
            have := hudist k; rw [hc1, SimpleGraph.dist_self] at this; omega
        · rintro (rfl | rfl)
          · exact ⟨by rw [huadj]; right; dsimp only; omega, (hx_ne _).symm⟩
          · exact ⟨by rw [huadj]; left; dsimp only, (hx_ne _).symm⟩
      have hne : u ⟨k.1 - 1, by omega⟩ ≠ u ⟨k.1 + 1, by omega⟩ := fun h => by
        have := congrArg Fin.val (huinj h); dsimp only at this; omega
      rw [hset, Set.ncard_pair hne]
  have hdeg_i : (T.neighborSet (u ⟨i.1, by omega⟩)).ncard = 3 := by
    have hmemx : x ∈ T.neighborSet (u ⟨i.1, by omega⟩) := by
      change T.Adj (u ⟨i.1, by omega⟩) x
      rw [hui_eq]; exact hpx_adj.symm
    have h2 := hnb_of_uk ⟨i.1, by omega⟩ i.isLt
    have hEq : T.neighborSet (u ⟨i.1, by omega⟩) = insert x (T.neighborSet (u ⟨i.1, by omega⟩) \ {x}) := by
      ext y; by_cases hy : y = x <;> simp [hy, hmemx]
    rw [hEq, Set.ncard_insert_of_notMem (by simp) (Set.toFinite _), h2]
  have hdeg_other : ∀ k : Fin (r + 1), k.1 ≠ i.1 → k.1 < r → (T.neighborSet (u k)).ncard = 2 := by
    intro k hki hkr
    have hnotx : x ∉ T.neighborSet (u k) := by
      intro hadj
      have hmem' : u k ∈ T.neighborSet x := hadj.symm
      rw [hx_nb, Set.mem_singleton_iff] at hmem'
      have := congrArg Fin.val (huinj hmem'); dsimp only at this; exact hki this
    have hEq : T.neighborSet (u k) \ {x} = T.neighborSet (u k) :=
      Set.sdiff_singleton_eq_self hnotx
    rw [← hEq]; exact hnb_of_uk k hkr
  exact ⟨u, x, i, hu0, hx_side, huside, hudist, huinj, hx_ne, hmem_side, hx_nb, hlast_nb,
    hdeg_i, hdeg_other, hx_dist⟩

/- ### Part 4: Unique center (diameter `2r`) and bicenter (diameter `2r + 1`) characterization -/

private def IsUniqueCenter {V : Type} (T : SimpleGraph V) (c : V) (r : ℕ) : Prop :=
  (∀ x : V, T.dist x c ≤ r) ∧ (∀ z : V, z ≠ c → ∃ y : V, r < T.dist z y)

private lemma iso_uniqueCenter_eq {A B : Type} {R₁ : SimpleGraph A} {R₂ : SimpleGraph B}
    (φ : R₁ ≃g R₂) {c₁ : A} {c₂ : B} {r : ℕ}
    (h1 : IsUniqueCenter R₁ c₁ r) (h2 : IsUniqueCenter R₂ c₂ r) : φ c₁ = c₂ := by
  by_contra hne
  obtain ⟨y, hy⟩ := h2.2 (φ c₁) hne
  have hle := h1.1 (φ.symm y)
  rw [← iso_dist_eq φ (φ.symm y) c₁, φ.apply_symm_apply, SimpleGraph.dist_comm] at hle
  omega

private def IsBicenterPair {V : Type} (T : SimpleGraph V) (c₁ c₂ : V) (r : ℕ) : Prop :=
  (∀ x : V, T.dist x c₁ ≤ r + 1 ∧ T.dist x c₂ ≤ r + 1) ∧
  (∀ z : V, z ≠ c₁ → z ≠ c₂ → ∃ y : V, r + 1 < T.dist z y)

private lemma bicenterData_isBicenterPair {V : Type} [Fintype V] {T : SimpleGraph V} {r : ℕ}
    (D : BicenterData T r) : IsBicenterPair T D.c₁ D.c₂ r := by
  obtain ⟨a₁, ha₁_side, ha₁_dist⟩ := exists_far_vertex D
  obtain ⟨a₂, ha₂_side, ha₂_dist⟩ := exists_far_vertex D.swap
  dsimp only [BicenterData.swap] at ha₂_dist
  constructor
  · intro x
    rcases lt_or_gt_of_ne (D.hne x) with hx | hx
    · have h1 := D.hle₁ x hx
      have h2 := dist_c₂_of_side₁ D hx
      omega
    · have h2 := D.hle₂ x hx
      have h1 := dist_c₂_of_side₁ D.swap hx
      dsimp only [BicenterData.swap] at h1
      omega
  · intro z hz1 hz2
    rcases lt_or_gt_of_ne (D.hne z) with hz | hz
    · refine ⟨a₂, ?_⟩
      have hd := D.hdist z a₂ hz ha₂_side
      have hpos : 0 < T.dist z D.c₁ :=
        Nat.pos_of_ne_zero fun h0 => hz1 (D.hT.connected.dist_eq_zero_iff.mp h0)
      rw [SimpleGraph.dist_comm (u := D.c₂) (v := a₂)] at hd
      omega
    · refine ⟨a₁, ?_⟩
      have hd := D.swap.hdist z a₁ hz ha₁_side
      dsimp only [BicenterData.swap] at hd
      have hpos : 0 < T.dist z D.c₂ :=
        Nat.pos_of_ne_zero fun h0 => hz2 (D.hT.connected.dist_eq_zero_iff.mp h0)
      rw [SimpleGraph.dist_comm (u := D.c₁) (v := a₁)] at hd
      omega

private lemma iso_bicenterPair_eq {A B : Type} {R₁ : SimpleGraph A} {R₂ : SimpleGraph B}
    (φ : R₁ ≃g R₂) {c₁ c₂ : A} {d₁ d₂ : B} {r : ℕ} (hcne : c₁ ≠ c₂)
    (h1 : IsBicenterPair R₁ c₁ c₂ r) (h2 : IsBicenterPair R₂ d₁ d₂ r) :
    (φ c₁ = d₁ ∧ φ c₂ = d₂) ∨ (φ c₁ = d₂ ∧ φ c₂ = d₁) := by
  have hmem : ∀ c : A, (∀ x : A, R₁.dist x c ≤ r + 1) → φ c = d₁ ∨ φ c = d₂ := by
    intro c hc
    by_contra hnot
    push Not at hnot
    obtain ⟨y, hy⟩ := h2.2 (φ c) hnot.1 hnot.2
    have hle := hc (φ.symm y)
    rw [← iso_dist_eq φ (φ.symm y) c, φ.apply_symm_apply, SimpleGraph.dist_comm] at hle
    omega
  have h1' := hmem c₁ fun x => (h1.1 x).1
  have h2' := hmem c₂ fun x => (h1.1 x).2
  have hne : φ c₁ ≠ φ c₂ := fun h => hcne (φ.injective h)
  rcases h1' with h1' | h1' <;> rcases h2' with h2' | h2'
  · exact absurd (h1'.trans h2'.symm) hne
  · exact Or.inl ⟨h1', h2'⟩
  · exact Or.inr ⟨h1', h2'⟩
  · exact absurd (h1'.trans h2'.symm) hne

/- Card classification: deleting a leaf from a BicenterData tree -/

private lemma delete_leaf_diam_preserving {V : Type} [Fintype V] {T : SimpleGraph V} {r : ℕ}
    (D : BicenterData T r) (hV : 3 ≤ Fintype.card V)
    {v : V} (hv_side : v ∈ D.side₁) (hleaf : (T.neighborSet v).ncard = 1)
    (hother : ∃ a ∈ D.side₁, a ≠ v ∧ T.dist a D.c₁ = r) :
    let T' := T.induce ({v}ᶜ : Set V)
    ∃ (hc1 : D.c₁ ≠ v) (hc2 : D.c₂ ≠ v),
      T'.diam = 2 * r + 1 ∧
      IsBicenterPair T' ⟨D.c₁, hc1⟩ ⟨D.c₂, hc2⟩ r ∧
      ({x : ({v}ᶜ : Set V) | T'.dist x ⟨D.c₁, hc1⟩ < T'.dist x ⟨D.c₂, hc2⟩}.ncard = D.A₁.card - 1) ∧
      ({x : ({v}ᶜ : Set V) | T'.dist x ⟨D.c₂, hc2⟩ < T'.dist x ⟨D.c₁, hc1⟩}.ncard = D.swap.A₁.card) := by
  have hV2 : 2 ≤ Fintype.card V := by omega
  have hc1 : D.c₁ ≠ v := by
    rintro rfl
    obtain ⟨a, ha_side, ha_ne, ha_dist⟩ := hother
    obtain ⟨w, hw_path, hw_len⟩ := D.ht₁.connected.exists_path_of_dist ⟨D.c₁, mem_side₁_self D⟩ ⟨a, ha_side⟩
    have hwpos : 0 < w.length := by
      rw [hw_len, induce_dist_eq D.hT D.ht₁, SimpleGraph.dist_comm, ha_dist]; exact D.hr
    have hnb1 : T.Adj D.c₁ (w.getVert 1).1 := by simpa using w.adj_getVert_succ hwpos
    have hnb2 : T.Adj D.c₁ D.c₂ := D.hadj
    have heq := leaf_adj_unique hleaf hnb1 hnb2
    exact c₂_not_mem_side₁ D (by rw [← heq]; exact (w.getVert 1).2)
  have hc2 : D.c₂ ≠ v := fun h => c₂_not_mem_side₁ D (by rw [h]; exact hv_side)
  have hT' := delete_leaf_isTree D.hT hV2 hleaf
  have hdist_eq : ∀ x y : ({v}ᶜ : Set V), (T.induce ({v}ᶜ : Set V)).dist x y = T.dist x.1 y.1 :=
    delete_leaf_dist D.hT hV2 hleaf
  obtain ⟨a₁, ha₁_side, ha₁_ne, ha₁_dist⟩ := hother
  obtain ⟨a₂, ha₂_side, ha₂_dist⟩ := exists_far_vertex D.swap
  dsimp only [BicenterData.swap] at ha₂_dist
  have ha₂_ne : a₂ ≠ v := fun h => not_mem_side₁_of_mem_swap D ha₂_side (by rw [h]; exact hv_side)
  have hdiam' : (T.induce ({v}ᶜ : Set V)).diam = 2 * r + 1 := by
    apply le_antisymm
    · have hne : Nonempty ({v}ᶜ : Set V) := ⟨⟨D.c₁, hc1⟩⟩
      obtain ⟨x, y, hxy⟩ := (T.induce ({v}ᶜ : Set V)).exists_dist_eq_diam
      rw [← hxy, hdist_eq, ← D.hdiam]
      exact connected_dist_le_diam D.hT.connected _ _
    · have h1 := connected_dist_le_diam hT'.connected ⟨a₁, ha₁_ne⟩ ⟨a₂, ha₂_ne⟩
      rw [hdist_eq, D.hdist a₁ a₂ ha₁_side ha₂_side, SimpleGraph.dist_comm (u := D.c₂) (v := a₂),
        ha₁_dist, ha₂_dist] at h1
      omega
  have hbic : IsBicenterPair (T.induce ({v}ᶜ : Set V)) ⟨D.c₁, hc1⟩ ⟨D.c₂, hc2⟩ r := by
    constructor
    · intro x
      rw [hdist_eq, hdist_eq]
      exact (bicenterData_isBicenterPair D).1 x.1
    · intro z hz1 hz2
      have hz1' : z.1 ≠ D.c₁ := fun h => hz1 (Subtype.ext h)
      have hz2' : z.1 ≠ D.c₂ := fun h => hz2 (Subtype.ext h)
      rcases lt_or_gt_of_ne (D.hne z.1) with hz | hz
      · refine ⟨⟨a₂, ha₂_ne⟩, ?_⟩
        rw [hdist_eq, D.hdist z.1 a₂ hz ha₂_side, SimpleGraph.dist_comm (u := D.c₂) (v := a₂), ha₂_dist]
        have hpos : 0 < T.dist z.1 D.c₁ :=
          Nat.pos_of_ne_zero fun h0 => hz1' (D.hT.connected.dist_eq_zero_iff.mp h0)
        omega
      · refine ⟨⟨a₁, ha₁_ne⟩, ?_⟩
        rw [hdist_eq, D.swap.hdist z.1 a₁ hz ha₁_side]
        dsimp only [BicenterData.swap]
        rw [SimpleGraph.dist_comm (u := D.c₁) (v := a₁), ha₁_dist]
        have hpos : 0 < T.dist z.1 D.c₂ :=
          Nat.pos_of_ne_zero fun h0 => hz2' (D.hT.connected.dist_eq_zero_iff.mp h0)
        omega
  have hcard1 : {x : ({v}ᶜ : Set V) |
      (T.induce ({v}ᶜ : Set V)).dist x ⟨D.c₁, hc1⟩ <
      (T.induce ({v}ᶜ : Set V)).dist x ⟨D.c₂, hc2⟩}.ncard = D.A₁.card - 1 := by
    have himg : Subtype.val '' {x : ({v}ᶜ : Set V) |
        (T.induce ({v}ᶜ : Set V)).dist x ⟨D.c₁, hc1⟩ <
        (T.induce ({v}ᶜ : Set V)).dist x ⟨D.c₂, hc2⟩} = ((D.A₁.erase v : Finset V) : Set V) := by
      ext y
      simp only [Set.mem_image, Set.mem_ofPred_eq, Finset.mem_coe, Finset.mem_erase, mem_A₁_iff,
        hdist_eq]
      constructor
      · rintro ⟨⟨z, hzv⟩, hz, rfl⟩
        exact ⟨hzv, hz⟩
      · rintro ⟨hyv, hy⟩
        exact ⟨⟨y, hyv⟩, hy, rfl⟩
    rw [← Set.ncard_image_of_injective _ Subtype.val_injective, himg, Set.ncard_coe_finset,
      Finset.card_erase_of_mem ((mem_A₁_iff D).mpr hv_side)]
  have hcard2 : {x : ({v}ᶜ : Set V) |
      (T.induce ({v}ᶜ : Set V)).dist x ⟨D.c₂, hc2⟩ <
      (T.induce ({v}ᶜ : Set V)).dist x ⟨D.c₁, hc1⟩}.ncard = D.swap.A₁.card := by
    have himg : Subtype.val '' {x : ({v}ᶜ : Set V) |
        (T.induce ({v}ᶜ : Set V)).dist x ⟨D.c₂, hc2⟩ <
        (T.induce ({v}ᶜ : Set V)).dist x ⟨D.c₁, hc1⟩} = (D.swap.A₁ : Set V) := by
      ext y
      simp only [Set.mem_image, Set.mem_ofPred_eq, Finset.mem_coe, mem_A₁_iff, hdist_eq]
      constructor
      · rintro ⟨⟨z, _⟩, hz, rfl⟩
        exact hz
      · intro hy
        have hyv : y ≠ v := fun h => not_mem_side₁_of_mem_swap D hy (h ▸ hv_side)
        exact ⟨⟨y, hyv⟩, hy, rfl⟩
    rw [← Set.ncard_image_of_injective _ Subtype.val_injective, himg, Set.ncard_coe_finset]
  exact ⟨hc1, hc2, hdiam', hbic, hcard1, hcard2⟩

private lemma delete_unique_far_leaf {V : Type} [Fintype V] {T : SimpleGraph V} {r : ℕ}
    (D : BicenterData T r) (hV : 3 ≤ Fintype.card V)
    {v : V} (hv_side : v ∈ D.side₁) (hleaf : (T.neighborSet v).ncard = 1)
    (hfar : T.dist v D.c₁ = r)
    (huniq : ∀ a ∈ D.side₁, T.dist a D.c₁ = r → a = v) :
    let T' := T.induce ({v}ᶜ : Set V)
    ∃ (hc2 : D.c₂ ≠ v),
      T'.diam = 2 * r ∧
      IsUniqueCenter T' ⟨D.c₂, hc2⟩ r ∧
      (∀ pv : V, T.Adj v pv → (T.neighborSet pv).ncard = 2) := by
  have hV2 : 2 ≤ Fintype.card V := by omega
  have hc2 : D.c₂ ≠ v := fun h => c₂_not_mem_side₁ D (by rw [h]; exact hv_side)
  have hv_nec₁ : v ≠ D.c₁ := fun h => by rw [h, SimpleGraph.dist_self] at hfar; have := D.hr; omega
  have hdist_eq : ∀ x y : ({v}ᶜ : Set V), (T.induce ({v}ᶜ : Set V)).dist x y = T.dist x.1 y.1 :=
    delete_leaf_dist D.hT hV2 hleaf
  obtain ⟨pv, ⟨hpv_adj, hpv_dist⟩, hpv_uniq⟩ := tree_unique_parent D.hT hv_nec₁
  have hpv_ne : pv ≠ v := hpv_adj.ne.symm
  have hpv_side : pv ∈ D.side₁ := by
    by_contra hnot
    exact hv_nec₁ (eq_center_of_adj_across D hv_side (mem_swap_side₁_of_not_mem D hnot) hpv_adj).1
  have hpv_d1 : T.dist pv D.c₁ = r - 1 := by omega
  have hpv_d2 : T.dist pv D.c₂ = r := by
    rw [dist_c₂_of_side₁ D hpv_side, hpv_d1]; have := D.hr; omega
  obtain ⟨a₂, ha₂_side, ha₂_dist⟩ := exists_far_vertex D.swap
  have ha₂_ne : a₂ ≠ v := fun h => not_mem_side₁_of_mem_swap D ha₂_side (h ▸ hv_side)
  have hle_r : ∀ x : ({v}ᶜ : Set V), (T.induce ({v}ᶜ : Set V)).dist x ⟨D.c₂, hc2⟩ ≤ r := by
    intro x
    rw [hdist_eq]
    rcases lt_or_gt_of_ne (D.hne x.1) with hx | hx
    · have h1 := D.hle₁ x.1 hx
      have hne_r : T.dist x.1 D.c₁ ≠ r := fun hr' => x.2 (huniq x.1 hx hr')
      rw [dist_c₂_of_side₁ D hx]
      omega
    · exact D.hle₂ x.1 hx
  have hdiam' : (T.induce ({v}ᶜ : Set V)).diam = 2 * r := by
    apply le_antisymm
    · have hne : Nonempty ({v}ᶜ : Set V) := ⟨⟨D.c₂, hc2⟩⟩
      obtain ⟨x, y, hxy⟩ := (T.induce ({v}ᶜ : Set V)).exists_dist_eq_diam
      have hT' := delete_leaf_isTree D.hT hV2 hleaf
      have htri := hT'.connected.dist_triangle (u := x) (v := ⟨D.c₂, hc2⟩) (w := y)
      rw [SimpleGraph.dist_comm (u := ⟨D.c₂, hc2⟩) (v := y)] at htri
      have h1 := hle_r x
      have h2 := hle_r y
      omega
    · have h1 := connected_dist_le_diam (delete_leaf_isTree D.hT hV2 hleaf).connected ⟨pv, hpv_ne⟩ ⟨a₂, ha₂_ne⟩
      rw [hdist_eq, D.hdist pv a₂ hpv_side ha₂_side, SimpleGraph.dist_comm (u := D.c₂) (v := a₂),
        hpv_d1, ha₂_dist] at h1
      have := D.hr; omega
  have hctr : IsUniqueCenter (T.induce ({v}ᶜ : Set V)) ⟨D.c₂, hc2⟩ r := by
    refine ⟨hle_r, fun z hz => ?_⟩
    have hz' : z.1 ≠ D.c₂ := fun h => hz (Subtype.ext h)
    rcases lt_or_gt_of_ne (D.hne z.1) with hz1 | hz2
    · refine ⟨⟨a₂, ha₂_ne⟩, ?_⟩
      rw [hdist_eq, D.hdist z.1 a₂ hz1 ha₂_side, SimpleGraph.dist_comm (u := D.c₂) (v := a₂), ha₂_dist]
      omega
    · refine ⟨⟨pv, hpv_ne⟩, ?_⟩
      rw [hdist_eq, D.swap.hdist z.1 pv hz2 hpv_side]
      dsimp only [BicenterData.swap]
      rw [SimpleGraph.dist_comm (u := D.c₁) (v := pv), hpv_d1]
      have hpos : 0 < T.dist z.1 D.c₂ :=
        Nat.pos_of_ne_zero fun h0 => hz' (D.hT.connected.dist_eq_zero_iff.mp h0)
      have := D.hr; omega
  have hpv_deg2 : ∀ p : V, T.Adj v p → (T.neighborSet p).ncard = 2 := by
    intro p hadj
    have hpeq : p = pv := leaf_adj_unique hleaf hadj hpv_adj
    rw [hpeq]
    by_cases hp_c1 : pv = D.c₁
    · have hnb : T.neighborSet pv = {D.c₂, v} := by
        ext y
        simp only [mem_neighborSet, Set.mem_insert_iff, Set.mem_singleton_iff]
        constructor
        · intro hy
          by_cases hys : y ∈ D.side₁
          · right
            have hdy : T.dist y D.c₁ = 1 := by
              rw [← hp_c1]; exact dist_eq_one_iff_adj.mpr hy.symm
            have hr1 : r = 1 := by rw [hp_c1, SimpleGraph.dist_self] at hpv_dist; omega
            exact huniq y hys (by omega)
          · exact Or.inl (eq_center_of_adj_across D hpv_side (mem_swap_side₁_of_not_mem D hys) hy).2
        · rintro (rfl | rfl)
          · rw [hp_c1]; exact D.hadj
          · exact hpv_adj.symm
      rw [hnb, Set.ncard_pair hc2]
    · obtain ⟨gp, ⟨hgp_adj, hgp_dist⟩, hgp_uniq⟩ := tree_unique_parent D.hT hp_c1
      have hnb : T.neighborSet pv = {gp, v} := by
        ext y
        simp only [mem_neighborSet, Set.mem_insert_iff, Set.mem_singleton_iff]
        constructor
        · intro hy
          rcases tree_adj_dist_diff D.hT (r := D.c₁) hy with h | h
          · exact Or.inl (hgp_uniq y ⟨hy, h⟩)
          · right
            have hys : y ∈ D.side₁ := by
              by_contra hnot
              exact hp_c1 (eq_center_of_adj_across D hpv_side (mem_swap_side₁_of_not_mem D hnot) hy).1
            exact huniq y hys (by omega)
        · rintro (rfl | rfl)
          · exact hgp_adj
          · exact hpv_adj.symm
      have hne_gp : gp ≠ v := fun h => by rw [h] at hgp_dist; omega
      rw [hnb, Set.ncard_pair hne_gp]
  exact ⟨hc2, hdiam', hctr, hpv_deg2⟩

/- ### Part 5: Subcase I.1 — swapping two length-`r` path-branches at unique center -/

private lemma extend_iso_path_limb {V W : Type} [Fintype V] [Fintype W] {r : ℕ}
    {G : SimpleGraph V} {H : SimpleGraph W}
    (DG : BicenterData G r) (DH : BicenterData H r)
    (hV : 3 ≤ Fintype.card V) (hW : 3 ≤ Fintype.card W)
    (hG1 : DG.A₁.card ≤ r + 1) (hH1 : DH.A₁.card ≤ r + 1)
    {u : Fin (r + 1) → V} {v : Fin (r + 1) → W}
    (hu0 : u 0 = DG.c₁)
    (hu_mem : ∀ x : V, x ∈ DG.side₁ ↔ ∃ i : Fin (r + 1), u i = x)
    (hu_dist : ∀ i : Fin (r + 1), G.dist (u i) DG.c₁ = i.1)
    (hu_inj : Function.Injective u)
    (hu_adj : ∀ i j : Fin (r + 1), G.Adj (u i) (u j) ↔ i.1 + 1 = j.1 ∨ j.1 + 1 = i.1)
    (hu_last : G.neighborSet (u ⟨r, Nat.lt_succ_self r⟩) = {u ⟨r - 1, by have := DG.hr; omega⟩})
    (hv0 : v 0 = DH.c₁)
    (hv_mem : ∀ y : W, y ∈ DH.side₁ ↔ ∃ i : Fin (r + 1), v i = y)
    (hv_dist : ∀ i : Fin (r + 1), H.dist (v i) DH.c₁ = i.1)
    (hv_inj : Function.Injective v)
    (hv_adj : ∀ i j : Fin (r + 1), H.Adj (v i) (v j) ↔ i.1 + 1 = j.1 ∨ j.1 + 1 = i.1)
    (hv_last : H.neighborSet (v ⟨r, Nat.lt_succ_self r⟩) = {v ⟨r - 1, by have := DH.hr; omega⟩})
    (φ : G.induce ({u ⟨r, Nat.lt_succ_self r⟩}ᶜ : Set V) ≃g
         H.induce ({v ⟨r, Nat.lt_succ_self r⟩}ᶜ : Set W)) :
    Nonempty (G ≃g H) := by
  let ur : V := u ⟨r, Nat.lt_succ_self r⟩
  let vr : W := v ⟨r, Nat.lt_succ_self r⟩
  let G' := G.induce ({ur}ᶜ : Set V)
  let H' := H.induce ({vr}ᶜ : Set W)
  have hur_leaf : (G.neighborSet ur).ncard = 1 := by rw [hu_last, Set.ncard_singleton]
  have hvr_leaf : (H.neighborSet vr).ncard = 1 := by rw [hv_last, Set.ncard_singleton]
  have hur_side : ur ∈ DG.side₁ := (hu_mem ur).mpr ⟨⟨r, Nat.lt_succ_self r⟩, rfl⟩
  have hvr_side : vr ∈ DH.side₁ := (hv_mem vr).mpr ⟨⟨r, Nat.lt_succ_self r⟩, rfl⟩
  have hur_uniq : ∀ a ∈ DG.side₁, G.dist a DG.c₁ = r → a = ur := by
    intro a ha hda
    obtain ⟨i, rfl⟩ := (hu_mem a).mp ha
    have hi := hu_dist i
    congr 1; apply Fin.ext; dsimp only; omega
  have hvr_uniq : ∀ b ∈ DH.side₁, H.dist b DH.c₁ = r → b = vr := by
    intro b hb hdb
    obtain ⟨i, rfl⟩ := (hv_mem b).mp hb
    have hi := hv_dist i
    congr 1; apply Fin.ext; dsimp only; omega

  obtain ⟨hc2_ne, -, hctrG, -⟩ := delete_unique_far_leaf DG hV hur_side hur_leaf (hu_dist _) hur_uniq
  obtain ⟨hd2_ne, -, hctrH, -⟩ := delete_unique_far_leaf DH hW hvr_side hvr_leaf (hv_dist _) hvr_uniq
  have hφ_ctr : φ ⟨DG.c₂, hc2_ne⟩ = ⟨DH.c₂, hd2_ne⟩ := iso_uniqueCenter_eq φ hctrG hctrH
  -- Build a new iso ψ₀ : G' ≃g H' with ψ₀(u_{r-1}) = v_{r-1}
  have hu_ne_r : ∀ k : Fin r, u ⟨k.1, by omega⟩ ≠ ur := fun k h => by
    have := congrArg Fin.val (hu_inj h); dsimp only at this; omega
  have hv_ne_r : ∀ k : Fin r, v ⟨k.1, by omega⟩ ≠ vr := fun k h => by
    have := congrArg Fin.val (hv_inj h); dsimp only at this; omega
  let a : Fin r → ({vr}ᶜ : Set W) := fun k => φ ⟨u ⟨k.1, by omega⟩, hu_ne_r k⟩
  let b : Fin r → ({vr}ᶜ : Set W) := fun k => ⟨v ⟨k.1, by omega⟩, hv_ne_r k⟩
  have ha_inj : Function.Injective a := fun i j hij =>
    Fin.ext (by
      have := congrArg (fun z : ({ur}ᶜ : Set V) => z.1) (φ.injective hij)
      have := congrArg Fin.val (hu_inj this); dsimp only at this; exact this)
  have hb_inj : Function.Injective b := fun i j hij =>
    Fin.ext (by
      have := congrArg (fun z : ({vr}ᶜ : Set W) => z.1) hij
      have := congrArg Fin.val (hv_inj this); dsimp only at this; exact this)
  have hr0 : 0 < r := DG.hr
  have ha0_adj : H'.Adj ⟨DH.c₂, hd2_ne⟩ (a ⟨0, hr0⟩) := by
    rw [← hφ_ctr]
    exact φ.map_rel_iff.mpr (by change G.Adj DG.c₂ (u 0); rw [hu0]; exact DG.hadj.symm)
  have hb0_adj : H'.Adj ⟨DH.c₂, hd2_ne⟩ (b ⟨0, hr0⟩) := by
    change H.Adj DH.c₂ (v 0); rw [hv0]; exact DH.hadj.symm
  have ha_step : ∀ k : Fin r, ∀ hk : k.1 + 1 < r, H'.Adj (a k) (a ⟨k.1 + 1, hk⟩) := fun k hk =>
    φ.map_rel_iff.mpr ((hu_adj ⟨k.1, by omega⟩ ⟨k.1 + 1, by omega⟩).mpr (Or.inl rfl))
  have hb_step : ∀ k : Fin r, ∀ hk : k.1 + 1 < r, H'.Adj (b k) (b ⟨k.1 + 1, hk⟩) := fun k hk =>
    (hv_adj ⟨k.1, by omega⟩ ⟨k.1 + 1, by omega⟩).mpr (Or.inl rfl)
  -- Helper: neighbors of a k in H' are ONLY inside range a ∪ {d₂}, and similarly for b k!
  have hb_nb_closed : ∀ (k : Fin r) (y : ({vr}ᶜ : Set W)), H'.Adj (b k) y →
      (y = ⟨DH.c₂, hd2_ne⟩ ∧ k.1 = 0) ∨ ∃ j : Fin r, y = b j ∧ (k.1 + 1 = j.1 ∨ j.1 + 1 = k.1) := by
    intro k y hadj
    change H.Adj (v ⟨k.1, by omega⟩) y.1 at hadj
    by_cases hy : y.1 ∈ DH.side₁
    · obtain ⟨j, hj⟩ := (hv_mem y.1).mp hy
      have hjr : j.1 < r := by
        by_contra hge
        have hjeq : j = ⟨r, Nat.lt_succ_self r⟩ := Fin.ext (by dsimp only; have := j.isLt; omega)
        exact y.2 (hj.symm.trans (by rw [hjeq]))
      right
      refine ⟨⟨j.1, hjr⟩, Subtype.ext hj.symm, ?_⟩
      rw [← hj] at hadj
      exact (hv_adj ⟨k.1, by omega⟩ j).mp hadj
    · obtain ⟨hc1, hc2⟩ := eq_center_of_adj_across DH
        ((hv_mem _).mpr ⟨⟨k.1, by omega⟩, rfl⟩) (mem_swap_side₁_of_not_mem DH hy) hadj
      left
      refine ⟨Subtype.ext hc2, ?_⟩
      have := hv_dist ⟨k.1, by omega⟩; rw [hc1, SimpleGraph.dist_self] at this; exact this.symm
  have ha_nb_closed : ∀ (k : Fin r) (y : ({vr}ᶜ : Set W)), H'.Adj (a k) y →
      (y = ⟨DH.c₂, hd2_ne⟩ ∧ k.1 = 0) ∨ ∃ j : Fin r, y = a j ∧ (k.1 + 1 = j.1 ∨ j.1 + 1 = k.1) := by
    intro k y hadj
    have hpre : G.Adj (u ⟨k.1, by omega⟩) (φ.symm y).1 := by
      have := φ.symm.map_rel_iff.mpr hadj
      simpa [a] using this
    by_cases hy : (φ.symm y).1 ∈ DG.side₁
    · obtain ⟨j, hj⟩ := (hu_mem (φ.symm y).1).mp hy
      have hjr : j.1 < r := by
        by_contra hge
        have hjeq : j = ⟨r, Nat.lt_succ_self r⟩ := Fin.ext (by dsimp only; have := j.isLt; omega)
        exact (φ.symm y).2 (hj.symm.trans (by rw [hjeq]))
      right
      refine ⟨⟨j.1, hjr⟩, ?_, ?_⟩
      · have : φ.symm y = ⟨u ⟨j.1, by omega⟩, hu_ne_r ⟨j.1, hjr⟩⟩ := Subtype.ext hj.symm
        rw [← φ.apply_symm_apply y, this]
      · rw [← hj] at hpre
        exact (hu_adj ⟨k.1, by omega⟩ j).mp hpre
    · obtain ⟨hc1, hc2⟩ := eq_center_of_adj_across DG
        ((hu_mem _).mpr ⟨⟨k.1, by omega⟩, rfl⟩) (mem_swap_side₁_of_not_mem DG hy) hpre
      left
      refine ⟨?_, ?_⟩
      · have : φ.symm y = ⟨DG.c₂, hc2_ne⟩ := Subtype.ext hc2
        rw [← φ.apply_symm_apply y, this, hφ_ctr]
      · have := hu_dist ⟨k.1, by omega⟩; rw [hc1, SimpleGraph.dist_self] at this; exact this.symm
  -- Helper: finish once we have ψ₀ : G' ≃g H' with ψ₀(u_{r-1}) = v_{r-1}
  have finish : ∀ ψ₀ : G' ≃g H', ψ₀ ⟨u ⟨r - 1, by omega⟩, hu_ne_r ⟨r - 1, by omega⟩⟩ =
      ⟨v ⟨r - 1, by omega⟩, hv_ne_r ⟨r - 1, by omega⟩⟩ → Nonempty (G ≃g H) := by
    intro ψ₀ hψ_last
    let fwd : V → W := fun x => if hx : x = ur then vr else (ψ₀ ⟨x, hx⟩).1
    let bwd : W → V := fun y => if hy : y = vr then ur else (ψ₀.symm ⟨y, hy⟩).1
    have hli : Function.LeftInverse bwd fwd := by
      intro x
      by_cases hx : x = ur
      · simp [fwd, bwd, hx]
      · have hne : (ψ₀ ⟨x, hx⟩).1 ≠ vr := (ψ₀ ⟨x, hx⟩).2
        simp only [fwd, bwd, dif_neg hx, dif_neg hne]
        exact congrArg Subtype.val (ψ₀.symm_apply_apply ⟨x, hx⟩)
    have hri : Function.RightInverse bwd fwd := by
      intro y
      by_cases hy : y = vr
      · simp [fwd, bwd, hy]
      · have hne : (ψ₀.symm ⟨y, hy⟩).1 ≠ ur := (ψ₀.symm ⟨y, hy⟩).2
        simp only [fwd, bwd, dif_neg hy, dif_neg hne]
        exact congrArg Subtype.val (ψ₀.apply_symm_apply ⟨y, hy⟩)
    refine ⟨⟨⟨fwd, bwd, hli, hri⟩, ?_⟩⟩
    intro x₁ x₂
    by_cases h1 : x₁ = ur <;> by_cases h2 : x₂ = ur
    · subst h1; subst h2; simp [fwd]
    · subst h1
      have hne : (ψ₀ ⟨x₂, h2⟩).1 ≠ vr := (ψ₀ ⟨x₂, h2⟩).2
      simp only [Equiv.coe_fn_mk, fwd, dif_pos, dif_neg h2]
      constructor
      · intro hadj
        have hmem : (ψ₀ ⟨x₂, h2⟩).1 ∈ H.neighborSet vr := hadj
        rw [hv_last, Set.mem_singleton_iff] at hmem
        have hsub : ψ₀ ⟨x₂, h2⟩ = ψ₀ ⟨u ⟨r - 1, by omega⟩, hu_ne_r ⟨r - 1, by omega⟩⟩ := by
          rw [hψ_last]; exact Subtype.ext hmem
        have hx2 : x₂ = u ⟨r - 1, by omega⟩ := congrArg Subtype.val (ψ₀.injective hsub)
        rw [hx2]; exact (hu_adj ⟨r, Nat.lt_succ_self r⟩ ⟨r - 1, by omega⟩).mpr (Or.inr (by dsimp only; omega))
      · intro hadj
        have hmem : x₂ ∈ G.neighborSet ur := hadj
        rw [hu_last, Set.mem_singleton_iff] at hmem
        have hsub : (⟨x₂, h2⟩ : ({ur}ᶜ : Set V)) = ⟨u ⟨r - 1, by omega⟩, hu_ne_r ⟨r - 1, by omega⟩⟩ :=
          Subtype.ext hmem
        rw [hsub, hψ_last]
        exact (hv_adj ⟨r, Nat.lt_succ_self r⟩ ⟨r - 1, by omega⟩).mpr (Or.inr (by dsimp only; omega))
    · subst h2
      have hne : (ψ₀ ⟨x₁, h1⟩).1 ≠ vr := (ψ₀ ⟨x₁, h1⟩).2
      simp only [Equiv.coe_fn_mk, fwd, dif_neg h1, dif_pos]
      constructor
      · intro hadj
        have hmem : (ψ₀ ⟨x₁, h1⟩).1 ∈ H.neighborSet vr := hadj.symm
        rw [hv_last, Set.mem_singleton_iff] at hmem
        have hsub : ψ₀ ⟨x₁, h1⟩ = ψ₀ ⟨u ⟨r - 1, by omega⟩, hu_ne_r ⟨r - 1, by omega⟩⟩ := by
          rw [hψ_last]; exact Subtype.ext hmem
        have hx1 : x₁ = u ⟨r - 1, by omega⟩ := congrArg Subtype.val (ψ₀.injective hsub)
        rw [hx1]; exact ((hu_adj ⟨r, Nat.lt_succ_self r⟩ ⟨r - 1, by omega⟩).mpr (Or.inr (by dsimp only; omega))).symm
      · intro hadj
        have hmem : x₁ ∈ G.neighborSet ur := hadj.symm
        rw [hu_last, Set.mem_singleton_iff] at hmem
        have hsub : (⟨x₁, h1⟩ : ({ur}ᶜ : Set V)) = ⟨u ⟨r - 1, by omega⟩, hu_ne_r ⟨r - 1, by omega⟩⟩ :=
          Subtype.ext hmem
        rw [hsub, hψ_last]
        exact ((hv_adj ⟨r, Nat.lt_succ_self r⟩ ⟨r - 1, by omega⟩).mpr (Or.inr (by dsimp only; omega))).symm
    · simp only [Equiv.coe_fn_mk, fwd, dif_neg h1, dif_neg h2]
      exact ψ₀.map_rel_iff
  have ha_dist_d2 : ∀ k : Fin r, H'.dist ⟨DH.c₂, hd2_ne⟩ (a k) = k.1 + 1 := by
    intro k
    rw [← hφ_ctr, iso_dist_eq φ, delete_leaf_dist DG.hT (by omega) hur_leaf, SimpleGraph.dist_comm,
      dist_c₂_of_side₁ DG ((hu_mem _).mpr ⟨⟨k.1, by omega⟩, rfl⟩), hu_dist]
  have hb_dist_d2 : ∀ k : Fin r, H'.dist ⟨DH.c₂, hd2_ne⟩ (b k) = k.1 + 1 := by
    intro k
    rw [delete_leaf_dist DH.hT (by omega) hvr_leaf, SimpleGraph.dist_comm,
      dist_c₂_of_side₁ DH ((hv_mem _).mpr ⟨⟨k.1, by omega⟩, rfl⟩), hv_dist]
  -- Split on whether a 0 = b 0
  by_cases h0eq : a ⟨0, hr0⟩ = b ⟨0, hr0⟩
  · -- By induction on k, a k = b k for all k < r
    have haeqb : ∀ k : ℕ, ∀ hk : k < r, a ⟨k, hk⟩ = b ⟨k, hk⟩ := by
      intro k
      induction k with
      | zero => intro _; exact h0eq
      | succ k ih =>
        intro hk
        have hprev := ih (by omega)
        have hadj : H'.Adj (b ⟨k, by omega⟩) (a ⟨k + 1, hk⟩) := by
          rw [← hprev]; exact ha_step ⟨k, by omega⟩ hk
        rcases hb_nb_closed ⟨k, by omega⟩ (a ⟨k + 1, hk⟩) hadj with ⟨hc2, hk0⟩ | ⟨j, hj, hstep⟩
        · exfalso
          have h1 := ha_dist_d2 ⟨k + 1, hk⟩
          rw [hc2, SimpleGraph.dist_self] at h1
          dsimp only at h1; omega
        · rcases hstep with hstep | hstep
          · have hjeq : j = ⟨k + 1, hk⟩ := Fin.ext (by dsimp only at hstep ⊢; omega)
            rwa [hjeq] at hj
          · exfalso
            have h1 := ha_dist_d2 ⟨k + 1, hk⟩
            have h2 := hb_dist_d2 j
            rw [hj] at h1; dsimp only at h1 hstep; omega
    exact finish φ (haeqb (r - 1) (by omega))
  · -- a and b have disjoint ranges!
    have hT'H : H'.IsTree := delete_leaf_isTree DH.hT (by omega) hvr_leaf
    have hdisj : ∀ i j : Fin r, a i ≠ b j := by
      intro i j hij
      have hkeq : i.1 = j.1 := by
        have h1 := ha_dist_d2 i; have h2 := hb_dist_d2 j; rw [hij] at h1; omega
      have : ∀ k : ℕ, ∀ hk : k < r, a ⟨k, hk⟩ = b ⟨k, hk⟩ → a ⟨0, hr0⟩ = b ⟨0, hr0⟩ := by
        intro k
        induction k with
        | zero => intro _ h; exact h
        | succ k ih =>
          intro hk hEq
          have hne_c : a ⟨k + 1, hk⟩ ≠ ⟨DH.c₂, hd2_ne⟩ := fun h => by
            have := ha_dist_d2 ⟨k + 1, hk⟩; rw [h, SimpleGraph.dist_self] at this; dsimp only at this; omega
          have huniq_p := tree_unique_parent hT'H hne_c
          have ha_p : H'.Adj (a ⟨k + 1, hk⟩) (a ⟨k, by omega⟩) ∧
              H'.dist (a ⟨k, by omega⟩) ⟨DH.c₂, hd2_ne⟩ + 1 = H'.dist (a ⟨k + 1, hk⟩) ⟨DH.c₂, hd2_ne⟩ := by
            refine ⟨(ha_step ⟨k, by omega⟩ hk).symm, ?_⟩
            rw [SimpleGraph.dist_comm (u := a _), SimpleGraph.dist_comm (u := a _), ha_dist_d2, ha_dist_d2]
          have hb_p : H'.Adj (a ⟨k + 1, hk⟩) (b ⟨k, by omega⟩) ∧
              H'.dist (b ⟨k, by omega⟩) ⟨DH.c₂, hd2_ne⟩ + 1 = H'.dist (a ⟨k + 1, hk⟩) ⟨DH.c₂, hd2_ne⟩ := by
            rw [hEq]
            refine ⟨(hb_step ⟨k, by omega⟩ hk).symm, ?_⟩
            rw [SimpleGraph.dist_comm (u := b _), SimpleGraph.dist_comm (u := b _), hb_dist_d2, hb_dist_d2]
          exact ih (by omega) (huniq_p.unique ha_p hb_p)
      have hieq : i = ⟨i.1, i.isLt⟩ := rfl
      have hjeq : j = ⟨i.1, i.isLt⟩ := Fin.ext hkeq.symm
      rw [hieq, hjeq] at hij
      exact h0eq (this i.1 i.isLt hij)
    have ha_ne_d2 : ∀ k : Fin r, a k ≠ ⟨DH.c₂, hd2_ne⟩ := fun k h => by
      have := ha_dist_d2 k; rw [h, SimpleGraph.dist_self] at this; omega
    have hb_ne_d2 : ∀ k : Fin r, b k ≠ ⟨DH.c₂, hd2_ne⟩ := fun k h => by
      have := hb_dist_d2 k; rw [h, SimpleGraph.dist_self] at this; omega
    -- Define the involution τ on ({vr}ᶜ : Set W) swapping a k ↔ b k
    let τfun : ({vr}ᶜ : Set W) → ({vr}ᶜ : Set W) := fun y =>
      if hA : ∃ k : Fin r, a k = y then b hA.choose
      else if hB : ∃ k : Fin r, b k = y then a hB.choose
      else y
    have hτ_a : ∀ k : Fin r, τfun (a k) = b k := by
      intro k
      have hA : ∃ j : Fin r, a j = a k := ⟨k, rfl⟩
      simp only [τfun, dif_pos hA]
      congr 1; exact ha_inj hA.choose_spec
    have hτ_b : ∀ k : Fin r, τfun (b k) = a k := by
      intro k
      have hnotA : ¬ ∃ j : Fin r, a j = b k := by rintro ⟨j, hj⟩; exact hdisj j k hj
      have hB : ∃ j : Fin r, b j = b k := ⟨k, rfl⟩
      simp only [τfun, dif_neg hnotA, dif_pos hB]
      congr 1; exact hb_inj hB.choose_spec
    have hτ_other : ∀ y : ({vr}ᶜ : Set W), (∀ k, a k ≠ y) → (∀ k, b k ≠ y) → τfun y = y := by
      intro y hA hB
      have h1 : ¬ ∃ k, a k = y := by rintro ⟨k, hk⟩; exact hA k hk
      have h2 : ¬ ∃ k, b k = y := by rintro ⟨k, hk⟩; exact hB k hk
      simp only [τfun, dif_neg h1, dif_neg h2]
    have hτ_d2 : τfun ⟨DH.c₂, hd2_ne⟩ = ⟨DH.c₂, hd2_ne⟩ := hτ_other _ ha_ne_d2 hb_ne_d2
    have hτ_invol : Function.Involutive τfun := by
      intro y
      by_cases hA : ∃ k, a k = y
      · obtain ⟨k, rfl⟩ := hA; rw [hτ_a, hτ_b]
      · by_cases hB : ∃ k, b k = y
        · obtain ⟨k, rfl⟩ := hB; rw [hτ_b, hτ_a]
        · rw [hτ_other y (fun k h => hA ⟨k, h⟩) (fun k h => hB ⟨k, h⟩),
              hτ_other y (fun k h => hA ⟨k, h⟩) (fun k h => hB ⟨k, h⟩)]
    have hτ_adj_fwd : ∀ y₁ y₂ : ({vr}ᶜ : Set W), H'.Adj y₁ y₂ → H'.Adj (τfun y₁) (τfun y₂) := by
      intro y₁ y₂ hadj
      by_cases hA1 : ∃ k, a k = y₁
      · obtain ⟨k, rfl⟩ := hA1
        rcases ha_nb_closed k y₂ hadj with ⟨rfl, hk0⟩ | ⟨j, rfl, hstep⟩
        · rw [hτ_a, hτ_d2, show k = ⟨0, hr0⟩ from Fin.ext hk0]; exact hb0_adj.symm
        · rw [hτ_a, hτ_a]; exact (hv_adj ⟨k.1, by omega⟩ ⟨j.1, by omega⟩).mpr hstep
      · by_cases hB1 : ∃ k, b k = y₁
        · obtain ⟨k, rfl⟩ := hB1
          rcases hb_nb_closed k y₂ hadj with ⟨rfl, hk0⟩ | ⟨j, rfl, hstep⟩
          · rw [hτ_b, hτ_d2, show k = ⟨0, hr0⟩ from Fin.ext hk0]; exact ha0_adj.symm
          · rw [hτ_b, hτ_b]
            exact φ.map_rel_iff.mpr ((hu_adj ⟨k.1, by omega⟩ ⟨j.1, by omega⟩).mpr hstep)
        · by_cases hA2 : ∃ k, a k = y₂
          · obtain ⟨k, rfl⟩ := hA2
            rcases ha_nb_closed k y₁ hadj.symm with ⟨rfl, hk0⟩ | ⟨j, rfl, -⟩
            · rw [hτ_d2, hτ_a, show k = ⟨0, hr0⟩ from Fin.ext hk0]; exact hb0_adj
            · exact absurd ⟨j, rfl⟩ hA1
          · by_cases hB2 : ∃ k, b k = y₂
            · obtain ⟨k, rfl⟩ := hB2
              rcases hb_nb_closed k y₁ hadj.symm with ⟨rfl, hk0⟩ | ⟨j, rfl, -⟩
              · rw [hτ_d2, hτ_b, show k = ⟨0, hr0⟩ from Fin.ext hk0]; exact ha0_adj
              · exact absurd ⟨j, rfl⟩ hB1
            · rw [hτ_other y₁ (fun k h => hA1 ⟨k, h⟩) (fun k h => hB1 ⟨k, h⟩),
                  hτ_other y₂ (fun k h => hA2 ⟨k, h⟩) (fun k h => hB2 ⟨k, h⟩)]
              exact hadj
    let τe : ({vr}ᶜ : Set W) ≃ ({vr}ᶜ : Set W) := ⟨τfun, τfun, hτ_invol, hτ_invol⟩
    let τ : H' ≃g H' :=
      ⟨τe, fun {y₁ y₂} =>
        ⟨fun h => by
          have h' := hτ_adj_fwd (τfun y₁) (τfun y₂) h
          rwa [hτ_invol y₁, hτ_invol y₂] at h',
         hτ_adj_fwd y₁ y₂⟩⟩
    exact finish (φ.trans τ) (by
      change τfun (a ⟨r - 1, by omega⟩) = b ⟨r - 1, by omega⟩
      exact hτ_a ⟨r - 1, by omega⟩)

/- ### Part 6: Minimum distance from center to a degree-`≥ 3` vertex (Subcase I.2) -/

private noncomputable def minDistDeg3 {V : Type} [Fintype V] (T : SimpleGraph V) (c : V) : ℕ :=
  let S := Finset.univ.filter fun x : V => 3 ≤ (T.neighborSet x).ncard
  if h : S.Nonempty then (S.image fun x => T.dist c x).min' (h.image _) else 0

private lemma iso_minDistDeg3_eq {A B : Type} [Fintype A] [Fintype B]
    {R₁ : SimpleGraph A} {R₂ : SimpleGraph B} (φ : R₁ ≃g R₂) (c : A) :
    minDistDeg3 R₂ (φ c) = minDistDeg3 R₁ c := by
  unfold minDistDeg3
  set S₁ := Finset.univ.filter fun x : A => 3 ≤ (R₁.neighborSet x).ncard
  set S₂ := Finset.univ.filter fun y : B => 3 ≤ (R₂.neighborSet y).ncard
  have hS_img : S₂ = S₁.image φ := by
    ext y
    simp only [S₂, S₁, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro hy
      refine ⟨φ.symm y, ?_, φ.apply_symm_apply y⟩
      have h1 := iso_neighborSet_ncard φ (φ.symm y)
      rw [φ.apply_symm_apply] at h1
      omega
    · rintro ⟨x, hx, rfl⟩
      rw [iso_neighborSet_ncard φ x]; exact hx
  have hImg_eq : S₂.image (fun y => R₂.dist (φ c) y) = S₁.image (fun x => R₁.dist c x) := by
    rw [hS_img, Finset.image_image]
    apply Finset.image_congr
    intro x _
    exact iso_dist_eq φ c x
  by_cases h1 : S₁.Nonempty
  · have h2 : S₂.Nonempty := by rw [hS_img]; exact h1.image _
    rw [dif_pos h2, dif_pos h1]
    have hmin_congr : ∀ {A B : Finset ℕ} (hA : A.Nonempty) (hB : B.Nonempty), A = B →
        A.min' hA = B.min' hB := by rintro A _ hA hB rfl; rfl
    exact hmin_congr _ _ hImg_eq
  · have h2 : ¬ S₂.Nonempty := by rw [hS_img]; simpa using h1
    rw [dif_neg h2, dif_neg h1]

/- ### Part 7: Branch 1 (both `G` and `H` have a path-limb) -/

private lemma case_both_path_limb {V W : Type} [Fintype V] [Fintype W] {r : ℕ}
    (hV : 3 ≤ Fintype.card V)
    {G : SimpleGraph V} {H : SimpleGraph W} (σ : V ≃ W)
    (hσ : ∀ v : V, Nonempty (G.induce {v}ᶜ ≃g H.induce {σ v}ᶜ))
    (hnonpath : ∃ v : V, 3 ≤ (G.neighborSet v).ncard)
    (DG : BicenterData G r) (DH : BicenterData H r)
    (hG1 : DG.A₁.card ≤ r + 1) (hH1 : DH.A₁.card ≤ r + 1) :
    Nonempty (G ≃g H) := by
  have hW : 3 ≤ Fintype.card W := by rw [← Fintype.card_congr σ]; exact hV
  obtain ⟨u, hu0, hu_mem, hu_dist, hu_inj, hu_adj, hu_last, hu_mid, hu_le2⟩ := path_limb_spec DG hG1
  obtain ⟨v, hv0, hv_mem, hv_dist, hv_inj, hv_adj, hv_last, hv_mid, hv_le2⟩ := path_limb_spec DH hH1
  let ur : V := u ⟨r, Nat.lt_succ_self r⟩
  let vr : W := v ⟨r, Nat.lt_succ_self r⟩
  have hur_leaf : (G.neighborSet ur).ncard = 1 := by rw [hu_last, Set.ncard_singleton]
  have hvr_leaf : (H.neighborSet vr).ncard = 1 := by rw [hv_last, Set.ncard_singleton]
  have hur_side : ur ∈ DG.side₁ := (hu_mem ur).mpr ⟨⟨r, Nat.lt_succ_self r⟩, rfl⟩
  have hvr_side : vr ∈ DH.side₁ := (hv_mem vr).mpr ⟨⟨r, Nat.lt_succ_self r⟩, rfl⟩
  have hur_uniq : ∀ a ∈ DG.side₁, G.dist a DG.c₁ = r → a = ur := fun a ha hda => by
    obtain ⟨i, rfl⟩ := (hu_mem a).mp ha
    have := hu_dist i; congr 1; apply Fin.ext; dsimp only; omega
  have hvr_uniq : ∀ b ∈ DH.side₁, H.dist b DH.c₁ = r → b = vr := fun b hb hdb => by
    obtain ⟨i, rfl⟩ := (hv_mem b).mp hb
    have := hv_dist i; congr 1; apply Fin.ext; dsimp only; omega
  obtain ⟨hc2_ne, hdiam_Gur, hctr_Gur, -⟩ :=
    delete_unique_far_leaf DG hV hur_side hur_leaf (hu_dist _) hur_uniq
  obtain ⟨hd2_ne, hdiam_Hvr, hctr_Hvr, -⟩ :=
    delete_unique_far_leaf DH hW hvr_side hvr_leaf (hv_dist _) hvr_uniq
  let w : W := σ ur
  obtain ⟨φw⟩ := hσ ur
  by_cases hw_vr : w = vr
  · exact extend_iso_path_limb DG DH hV hW hG1 hH1 hu0 hu_mem hu_dist hu_inj hu_adj hu_last
      hv0 hv_mem hv_dist hv_inj hv_adj hv_last (φw.trans (iso_induce_congr (by rw [show σ ur = vr from hw_vr])))
  · -- w ≠ vr; since H - w ≅ G - ur is a tree of diam 2r, w must be the unique far leaf of DH.swap!
    have hHw_tree : (H.induce ({w}ᶜ : Set W)).IsTree :=
      iso_isTree φw (delete_leaf_isTree DG.hT (by omega) hur_leaf)
    have hw_leaf : (H.neighborSet w).ncard = 1 := by
      have hpos : 0 < (H.neighborSet w).ncard := by
        obtain ⟨y, hy⟩ := connected_exists_adj DH.hT.connected (a := w) (b := if w = DH.c₁ then DH.c₂ else DH.c₁)
          (by split_ifs with h; exact h ▸ DH.hadj.ne; exact h)
        exact Set.ncard_pos (Set.toFinite _) |>.mpr ⟨y, hy⟩
      by_contra hne1
      exact delete_nonleaf_not_isTree DH.hT (by omega) hHw_tree
    have hHw_diam : (H.induce ({w}ᶜ : Set W)).diam = 2 * r :=
      (iso_diam_eq φw).trans hdiam_Gur
    have hw_side2 : w ∈ DH.swap.side₁ := by
      by_contra hnot
      have hw1 : w ∈ DH.side₁ := (lt_or_gt_of_ne (DH.hne w)).resolve_right (by simpa [BicenterData.side₁, BicenterData.swap] using hnot)
      obtain ⟨j, hj⟩ := (hv_mem w).mp hw1
      have hjlt : j.1 < r := by
        by_contra hge
        exact hw_vr (hj.symm.trans (by congr 1; apply Fin.ext; dsimp only; have := j.isLt; omega))
      have hdeg2 := hv_mid j hjlt
      rw [hj] at hdeg2; omega
    have hw_far : H.dist w DH.c₂ = r ∧ ∀ b ∈ DH.swap.side₁, H.dist b DH.c₂ = r → b = w := by
      by_contra hnot
      have hother : ∃ b ∈ DH.swap.side₁, b ≠ w ∧ H.dist b DH.c₂ = r := by
        by_cases hfw : H.dist w DH.c₂ = r
        · push Not at hnot
          obtain ⟨b, hb1, hb2, hb3⟩ := hnot hfw
          exact ⟨b, hb1, hb3, hb2⟩
        · obtain ⟨b, hb1, hb2⟩ := exists_far_vertex DH.swap
          exact ⟨b, hb1, fun h => hfw (h ▸ hb2), hb2⟩
      obtain ⟨-, -, hdiam_bad, -, -, -⟩ := delete_leaf_diam_preserving DH.swap hW hw_side2 hw_leaf hother
      omega
    obtain ⟨hd1_ne, -, hctr_Hw, hw_parent_deg2⟩ :=
      delete_unique_far_leaf DH.swap hW hw_side2 hw_leaf hw_far.1 hw_far.2
    -- Now inspect u' := σ⁻¹ vr
    let u' : V := σ.symm vr
    obtain ⟨φu'0⟩ := hσ u'
    have hσu' : σ u' = vr := σ.apply_symm_apply vr
    let φu' : G.induce ({u'}ᶜ : Set V) ≃g H.induce ({vr}ᶜ : Set W) :=
      φu'0.trans (iso_induce_congr (by rw [hσu']))
    by_cases hu'_ur : u' = ur
    · exact extend_iso_path_limb DG DH hV hW hG1 hH1 hu0 hu_mem hu_dist hu_inj hu_adj hu_last
        hv0 hv_mem hv_dist hv_inj hv_adj hv_last ((iso_induce_congr (by rw [hu'_ur])).symm.trans φu')
    · exfalso
      have hGu'_tree : (G.induce ({u'}ᶜ : Set V)).IsTree :=
        iso_isTree φu'.symm (delete_leaf_isTree DH.hT (by omega) hvr_leaf)
      have hu'_leaf : (G.neighborSet u').ncard = 1 := by
        have hpos : 0 < (G.neighborSet u').ncard := by
          obtain ⟨x, hx⟩ := connected_exists_adj DG.hT.connected (a := u') (b := if u' = DG.c₁ then DG.c₂ else DG.c₁)
            (by split_ifs with h; exact h ▸ DG.hadj.ne; exact h)
          exact Set.ncard_pos (Set.toFinite _) |>.mpr ⟨x, hx⟩
        by_contra hne1
        exact delete_nonleaf_not_isTree DG.hT (by omega) hGu'_tree
      have hGu'_diam : (G.induce ({u'}ᶜ : Set V)).diam = 2 * r :=
        (iso_diam_eq φu'.symm).trans hdiam_Hvr
      have hu'_side2 : u' ∈ DG.swap.side₁ := by
        by_contra hnot
        have hu'1 : u' ∈ DG.side₁ := (lt_or_gt_of_ne (DG.hne u')).resolve_right (by simpa [BicenterData.side₁, BicenterData.swap] using hnot)
        obtain ⟨j, hj⟩ := (hu_mem u').mp hu'1
        have hjlt : j.1 < r := by
          by_contra hge
          exact hu'_ur (hj.symm.trans (by congr 1; apply Fin.ext; dsimp only; have := j.isLt; omega))
        have hdeg2 := hu_mid j hjlt
        rw [hj] at hdeg2; omega
      have hu'_far : G.dist u' DG.c₂ = r ∧ ∀ a ∈ DG.swap.side₁, G.dist a DG.c₂ = r → a = u' := by
        by_contra hnot
        have hother : ∃ a ∈ DG.swap.side₁, a ≠ u' ∧ G.dist a DG.c₂ = r := by
          by_cases hfu : G.dist u' DG.c₂ = r
          · push Not at hnot
            obtain ⟨a, ha1, ha2, ha3⟩ := hnot hfu
            exact ⟨a, ha1, ha3, ha2⟩
          · obtain ⟨a, ha1, ha2⟩ := exists_far_vertex DG.swap
            exact ⟨a, ha1, fun h => hfu (h ▸ ha2), ha2⟩
        obtain ⟨-, -, hdiam_bad, -, -, -⟩ := delete_leaf_diam_preserving DG.swap hV hu'_side2 hu'_leaf hother
        omega
      obtain ⟨hc1_ne, -, hctr_Gu', hu'_parent_deg2⟩ :=
        delete_unique_far_leaf DG.swap hV hu'_side2 hu'_leaf hu'_far.1 hu'_far.2
      -- Compare minDistDeg3 in G - ur ≅ H - w and G - u' ≅ H - vr!
      have hφw_ctr : φw ⟨DG.c₂, hc2_ne⟩ = ⟨DH.c₁, hd1_ne⟩ := iso_uniqueCenter_eq φw hctr_Gur hctr_Hw
      have hφu'_ctr : φu' ⟨DG.c₁, hc1_ne⟩ = ⟨DH.c₂, hd2_ne⟩ := iso_uniqueCenter_eq φu' hctr_Gu' hctr_Hvr
      have hm1 : minDistDeg3 (H.induce ({w}ᶜ : Set W)) ⟨DH.c₁, hd1_ne⟩ =
          minDistDeg3 (G.induce ({ur}ᶜ : Set V)) ⟨DG.c₂, hc2_ne⟩ := by
        rw [← hφw_ctr]; exact iso_minDistDeg3_eq φw _
      have hm2 : minDistDeg3 (H.induce ({vr}ᶜ : Set W)) ⟨DH.c₂, hd2_ne⟩ =
          minDistDeg3 (G.induce ({u'}ᶜ : Set V)) ⟨DG.c₁, hc1_ne⟩ := by
        rw [← hφu'_ctr]; exact iso_minDistDeg3_eq φu' _
      -- Key claim: minDistDeg3 (G - u', c₁) = minDistDeg3 (G - ur, c₂) + 1
      -- and minDistDeg3 (H - w, d₁) = minDistDeg3 (H - vr, d₂) + 1!
      have hshift : ∀ {U : Type} [Fintype U] {T : SimpleGraph U} (D : BicenterData T r)
          (hU : 3 ≤ Fintype.card U)
          (hT_le2 : ∀ x ∈ D.side₁, (T.neighborSet x).ncard ≤ 2)
          (hT_deg3 : ∃ x : U, 3 ≤ (T.neighborSet x).ncard)
          {x1 x2 : U} (hx1_side : x1 ∈ D.side₁) (hx2_side : x2 ∈ D.swap.side₁)
          (hx1_leaf : (T.neighborSet x1).ncard = 1) (hx2_leaf : (T.neighborSet x2).ncard = 1)
          (hx1_p : ∀ p, T.Adj x1 p → (T.neighborSet p).ncard = 2)
          (hx2_p : ∀ p, T.Adj x2 p → (T.neighborSet p).ncard = 2)
          (hc2' : D.c₂ ≠ x1) (hc1' : D.c₁ ≠ x2),
          minDistDeg3 (T.induce ({x2}ᶜ : Set U)) ⟨D.c₁, hc1'⟩ =
          minDistDeg3 (T.induce ({x1}ᶜ : Set U)) ⟨D.c₂, hc2'⟩ + 1 := by
        intro U _ T D hU hT_le2 hT_deg3 x1 x2 hx1_side hx2_side hx1_leaf hx2_leaf hx1_p hx2_p hc2' hc1'
        unfold minDistDeg3
        set S1 := Finset.univ.filter fun z : ({x1}ᶜ : Set U) =>
          3 ≤ ((T.induce ({x1}ᶜ : Set U)).neighborSet z).ncard
        set S2 := Finset.univ.filter fun z : ({x2}ᶜ : Set U) =>
          3 ≤ ((T.induce ({x2}ᶜ : Set U)).neighborSet z).ncard
        set S0 := Finset.univ.filter fun z : U => 3 ≤ (T.neighborSet z).ncard
        have hS0_ne : S0.Nonempty := by
          obtain ⟨z, hz⟩ := hT_deg3; exact ⟨z, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hz⟩⟩
        have hS0_side2 : ∀ z ∈ S0, z ∈ D.swap.side₁ := fun z hz => by
          have h3 := (Finset.mem_filter.mp hz).2
          by_contra hnot
          have hz1 : z ∈ D.side₁ := (lt_or_gt_of_ne (D.hne z)).resolve_right (by simpa [BicenterData.side₁, BicenterData.swap] using hnot)
          have := hT_le2 z hz1; omega
        have hS1_img : S1.image (fun z => (T.induce ({x1}ᶜ : Set U)).dist ⟨D.c₂, hc2'⟩ z) =
            S0.image (fun z => T.dist D.c₂ z) := by
          ext d
          simp only [Finset.mem_image, S1, S0, Finset.mem_filter, Finset.mem_univ, true_and]
          constructor
          · rintro ⟨z, hz3, rfl⟩
            have hle : ((T.induce ({x1}ᶜ : Set U)).neighborSet z).ncard ≤ (T.neighborSet z.1).ncard := by
              by_cases hadj : T.Adj z.1 x1
              · have := neighborSet_induce_compl_ncard_of_adj hadj; omega
              · rw [neighborSet_induce_compl_ncard_of_not_adj hadj]
            refine ⟨z.1, by omega, ?_⟩
            exact (delete_leaf_dist D.hT (by omega) hx1_leaf ⟨D.c₂, hc2'⟩ z).symm
          · rintro ⟨z, hz3, rfl⟩
            have hzx1 : z ≠ x1 := fun h => by subst h; omega
            have hnadj : ¬ T.Adj z x1 := fun hadj => by have := hx1_p z hadj.symm; omega
            refine ⟨⟨z, hzx1⟩, ?_, delete_leaf_dist D.hT (by omega) hx1_leaf ⟨D.c₂, hc2'⟩ ⟨z, hzx1⟩⟩
            rw [neighborSet_induce_compl_ncard_of_not_adj hnadj]; exact hz3
        have hS2_img : S2.image (fun z => (T.induce ({x2}ᶜ : Set U)).dist ⟨D.c₁, hc1'⟩ z) =
            (S0.image (fun z => T.dist D.c₂ z)).image (· + 1) := by
          ext d
          simp only [Finset.mem_image, S2, S0, Finset.mem_filter, Finset.mem_univ, true_and]
          constructor
          · rintro ⟨z, hz3, rfl⟩
            have hle : ((T.induce ({x2}ᶜ : Set U)).neighborSet z).ncard ≤ (T.neighborSet z.1).ncard := by
              by_cases hadj : T.Adj z.1 x2
              · have := neighborSet_induce_compl_ncard_of_adj hadj; omega
              · rw [neighborSet_induce_compl_ncard_of_not_adj hadj]
            have hz0 : z.1 ∈ S0 := Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩
            have hz_s2 := hS0_side2 z.1 hz0
            refine ⟨T.dist D.c₂ z.1, ⟨z.1, by omega, rfl⟩, ?_⟩
            rw [delete_leaf_dist D.hT (by omega) hx2_leaf ⟨D.c₁, hc1'⟩ z]
            dsimp only
            have hstep := dist_c₂_of_side₁ D.swap hz_s2
            dsimp only [BicenterData.swap] at hstep
            rw [SimpleGraph.dist_comm (u := D.c₁), SimpleGraph.dist_comm (u := D.c₂)]
            exact hstep.symm
          · rintro ⟨d', ⟨z, hz3, rfl⟩, rfl⟩
            have hzx2 : z ≠ x2 := fun h => by subst h; omega
            have hnadj : ¬ T.Adj z x2 := fun hadj => by have := hx2_p z hadj.symm; omega
            have hz_s2 := hS0_side2 z (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hz3⟩)
            refine ⟨⟨z, hzx2⟩, ?_, ?_⟩
            · rw [neighborSet_induce_compl_ncard_of_not_adj hnadj]; exact hz3
            · rw [delete_leaf_dist D.hT (by omega) hx2_leaf ⟨D.c₁, hc1'⟩ ⟨z, hzx2⟩, SimpleGraph.dist_comm,
                dist_c₂_of_side₁ D.swap hz_s2, SimpleGraph.dist_comm]
        have hS1_ne : S1.Nonempty := by
          obtain ⟨z, hz⟩ := hS0_ne
          have hzx1 : z ≠ x1 := fun h => by have := (Finset.mem_filter.mp hz).2; subst h; omega
          have hnadj : ¬ T.Adj z x1 := fun hadj => by
            have := (Finset.mem_filter.mp hz).2; have := hx1_p z hadj.symm; omega
          refine ⟨⟨z, hzx1⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
          rw [neighborSet_induce_compl_ncard_of_not_adj hnadj]; exact (Finset.mem_filter.mp hz).2
        have hS2_ne : S2.Nonempty := by
          obtain ⟨z, hz⟩ := hS0_ne
          have hzx2 : z ≠ x2 := fun h => by have := (Finset.mem_filter.mp hz).2; subst h; omega
          have hnadj : ¬ T.Adj z x2 := fun hadj => by
            have := (Finset.mem_filter.mp hz).2; have := hx2_p z hadj.symm; omega
          refine ⟨⟨z, hzx2⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
          rw [neighborSet_induce_compl_ncard_of_not_adj hnadj]; exact (Finset.mem_filter.mp hz).2
        rw [dif_pos hS2_ne, dif_pos hS1_ne]
        set M := S0.image (fun z => T.dist D.c₂ z)
        have hM_ne : M.Nonempty := hS0_ne.image _
        have hmin1 : (S1.image (fun z => (T.induce ({x1}ᶜ : Set U)).dist ⟨D.c₂, hc2'⟩ z)).min' (hS1_ne.image _) =
            M.min' hM_ne := by
          have hmin_congr : ∀ {A B : Finset ℕ} (hA : A.Nonempty) (hB : B.Nonempty), A = B →
              A.min' hA = B.min' hB := by rintro A _ hA hB rfl; rfl
          exact hmin_congr _ _ hS1_img
        have hmin2 : (S2.image (fun z => (T.induce ({x2}ᶜ : Set U)).dist ⟨D.c₁, hc1'⟩ z)).min' (hS2_ne.image _) =
            M.min' hM_ne + 1 := by
          apply le_antisymm
          · apply Finset.min'_le
            rw [hS2_img]
            exact Finset.mem_image_of_mem _ (Finset.min'_mem M hM_ne)
          · apply Finset.le_min'
            intro d hd
            rw [hS2_img] at hd
            rcases Finset.mem_image.mp hd with ⟨d', hd', rfl⟩
            have := Finset.min'_le M d' hd'
            omega
        rw [hmin1, hmin2]
      have hG_deg3 := hnonpath
      have hH_deg3 : ∃ y : W, 3 ≤ (H.neighborSet y).ncard := by
        obtain ⟨x, hx⟩ := hnonpath
        have hx_ne_ur : x ≠ ur := fun h => by rw [h] at hx; omega
        have hx_nadj_ur : ¬ G.Adj x ur := fun hadj => by
          have := (delete_unique_far_leaf DG hV hur_side hur_leaf (hu_dist _) hur_uniq).2.2.2 x hadj.symm
          omega
        have hx3' : 3 ≤ ((G.induce ({ur}ᶜ : Set V)).neighborSet ⟨x, hx_ne_ur⟩).ncard := by
          rw [neighborSet_induce_compl_ncard_of_not_adj (x := ⟨x, hx_ne_ur⟩) hx_nadj_ur]; exact hx
        have hφx3 : 3 ≤ ((H.induce ({w}ᶜ : Set W)).neighborSet (φw ⟨x, hx_ne_ur⟩)).ncard := by
          rw [iso_neighborSet_ncard φw]; exact hx3'
        refine ⟨(φw ⟨x, hx_ne_ur⟩).1, ?_⟩
        by_cases hadj : H.Adj (φw ⟨x, hx_ne_ur⟩).1 w
        · have hstep := neighborSet_induce_compl_ncard_of_adj (v := w) (x := φw ⟨x, hx_ne_ur⟩) hadj
          dsimp only [w] at hstep hφx3 ⊢; omega
        · rw [← neighborSet_induce_compl_ncard_of_not_adj (v := w) (x := φw ⟨x, hx_ne_ur⟩) hadj]; exact hφx3
      have hur_p : ∀ p, G.Adj ur p → (G.neighborSet p).ncard = 2 :=
        (delete_unique_far_leaf DG hV hur_side hur_leaf (hu_dist _) hur_uniq).2.2.2
      have hvr_p : ∀ p, H.Adj vr p → (H.neighborSet p).ncard = 2 :=
        (delete_unique_far_leaf DH hW hvr_side hvr_leaf (hv_dist _) hvr_uniq).2.2.2
      have hG_shift := hshift DG hV hu_le2 hG_deg3 hur_side hu'_side2 hur_leaf hu'_leaf
        hur_p hu'_parent_deg2 hc2_ne hc1_ne
      have hH_shift := hshift DH hW hv_le2 hH_deg3 hvr_side hw_side2 hvr_leaf hw_leaf
        hvr_p hw_parent_deg2 hd2_ne hd1_ne
      omega

/- ### Part 8: Branch 2 (`|G₁| = r + 1` and `|H₁|, |H₂| ≥ r + 2`) -/

private lemma case_one_path_limb_impossible {V W : Type} [Fintype V] [Fintype W] {r : ℕ}
    (hV : 3 ≤ Fintype.card V)
    {G : SimpleGraph V} {H : SimpleGraph W} (σ : V ≃ W)
    (hσ : ∀ v : V, Nonempty (G.induce {v}ᶜ ≃g H.induce {σ v}ᶜ))
    (hdeg : ∀ v : V, (G.neighborSet v).ncard = (H.neighborSet (σ v)).ncard)
    (DG : BicenterData G r) (DH : BicenterData H r)
    (hG1 : DG.A₁.card ≤ r + 1)
    (hH1 : r + 2 ≤ DH.A₁.card) (hH2 : r + 2 ≤ DH.swap.A₁.card) : False := by
  have hW : 3 ≤ Fintype.card W := by rw [← Fintype.card_congr σ]; exact hV
  have hG1_eq : DG.A₁.card = r + 1 := le_antisymm hG1 (limb_card_ge DG)
  obtain ⟨u, hu0, hu_mem, hu_dist, hu_inj, hu_adj, hu_last, hu_mid, hu_le2⟩ := path_limb_spec DG hG1
  let ur : V := u ⟨r, Nat.lt_succ_self r⟩
  have hur_leaf : (G.neighborSet ur).ncard = 1 := by rw [hu_last, Set.ncard_singleton]
  have hur_side : ur ∈ DG.side₁ := (hu_mem ur).mpr ⟨⟨r, Nat.lt_succ_self r⟩, rfl⟩
  have hur_uniq : ∀ a ∈ DG.side₁, G.dist a DG.c₁ = r → a = ur := fun a ha hda => by
    obtain ⟨i, rfl⟩ := (hu_mem a).mp ha
    have := hu_dist i; congr 1; apply Fin.ext; dsimp only; omega
  obtain ⟨hc2_ne, hdiam_Gur, hctr_Gur, hur_p⟩ :=
    delete_unique_far_leaf DG hV hur_side hur_leaf (hu_dist _) hur_uniq
  -- Step 2.1: Every bicentral card of G has a limb of size r + 1; hence |H₁| = r + 2 and |H₂| = r + 2!
  have hH_limb_eq : ∀ (D' : BicenterData H r), r + 2 ≤ D'.A₁.card → r + 2 ≤ D'.swap.A₁.card →
      D'.A₁.card = r + 2 := by
    intro D' hbig1 hbig2
    obtain ⟨v1, hv1_side, hv1_leaf, a, ha_side, ha_ne, ha_dist⟩ :=
      exists_diam_preserving_leaf_of_big_limb D' hbig1
    obtain ⟨hd1_ne, hd2_ne, hdiam_Hv1, hbic_Hv1, hcard_H1, hcard_H2⟩ :=
      delete_leaf_diam_preserving D' hW hv1_side hv1_leaf ⟨a, ha_side, ha_ne, ha_dist⟩
    let v1' : V := σ.symm v1
    obtain ⟨φ0⟩ := hσ v1'
    have hσv1' : σ v1' = v1 := σ.apply_symm_apply v1
    let φ : G.induce ({v1'}ᶜ : Set V) ≃g H.induce ({v1}ᶜ : Set W) :=
      φ0.trans (iso_induce_congr (by rw [hσv1']))
    have hGv1'_tree : (G.induce ({v1'}ᶜ : Set V)).IsTree :=
      iso_isTree φ.symm (delete_leaf_isTree D'.hT (by omega) hv1_leaf)
    have hv1'_leaf : (G.neighborSet v1').ncard = 1 := by
      have := hdeg v1'; rw [hσv1'] at this; omega
    have hGv1'_diam : (G.induce ({v1'}ᶜ : Set V)).diam = 2 * r + 1 :=
      (iso_diam_eq φ.symm).trans hdiam_Hv1
    have hv1'_side2 : v1' ∈ DG.swap.side₁ := by
      by_contra hnot
      have hv1'_s1 : v1' ∈ DG.side₁ :=
        (lt_or_gt_of_ne (DG.hne v1')).resolve_right (by simpa [BicenterData.side₁, BicenterData.swap] using hnot)
      obtain ⟨j, hj⟩ := (hu_mem v1').mp hv1'_s1
      by_cases hjlt : j.1 < r
      · have := hu_mid j hjlt; rw [hj] at this; omega
      · have hjeq : v1' = ur := hj.symm.trans (by congr 1; apply Fin.ext; dsimp only; have := j.isLt; omega)
        have hdiam_eq : (G.induce ({v1'}ᶜ : Set V)).diam = (G.induce ({ur}ᶜ : Set V)).diam :=
          iso_diam_eq (iso_induce_congr (by rw [hjeq])).symm
        omega
    have hv1'_other : ∃ b ∈ DG.swap.side₁, b ≠ v1' ∧ G.dist b DG.c₂ = r := by
      by_contra hnot
      push Not at hnot
      obtain ⟨b, hb_side, hb_dist⟩ := exists_far_vertex DG.swap
      have hbeq : b = v1' := by
        by_contra hne; exact hnot b hb_side hne hb_dist
      rw [hbeq] at hb_dist
      have huniq_b : ∀ x ∈ DG.swap.side₁, G.dist x DG.c₂ = r → x = v1' := fun x hx hdx => by
        by_contra hne; exact hnot x hx hne hdx
      obtain ⟨-, hdiam_bad, -, -⟩ :=
        delete_unique_far_leaf DG.swap hV hv1'_side2 hv1'_leaf hb_dist huniq_b
      omega
    obtain ⟨gc2_ne, gc1_ne, -, hbic_Gv1', -, hcard_G1⟩ :=
      delete_leaf_diam_preserving DG.swap hV hv1'_side2 hv1'_leaf hv1'_other
    have hcne : (⟨DG.c₂, gc2_ne⟩ : ({v1'}ᶜ : Set V)) ≠ ⟨DG.c₁, gc1_ne⟩ := fun h =>
      DG.hadj.ne (congrArg Subtype.val h).symm
    rcases iso_bicenterPair_eq φ hcne hbic_Gv1' hbic_Hv1 with ⟨hmap2, hmap1⟩ | ⟨hmap2, hmap1⟩
    · -- φ maps DG.c₁ ↦ D'.c₂, so DG.A₁ (size r+1) maps to D'.swap.A₁ (size ≥ r+2) -> impossible!
      have hset_eq : φ '' {x : ({v1'}ᶜ : Set V) |
          (G.induce ({v1'}ᶜ : Set V)).dist x ⟨DG.c₁, gc1_ne⟩ <
          (G.induce ({v1'}ᶜ : Set V)).dist x ⟨DG.c₂, gc2_ne⟩} =
          {y : ({v1}ᶜ : Set W) |
          (H.induce ({v1}ᶜ : Set W)).dist y ⟨D'.c₂, hd2_ne⟩ <
          (H.induce ({v1}ᶜ : Set W)).dist y ⟨D'.c₁, hd1_ne⟩} := by
        ext y
        simp only [Set.mem_image, Set.mem_ofPred_eq]
        constructor
        · rintro ⟨x, hx, rfl⟩
          rw [← hmap1, ← hmap2, iso_dist_eq φ, iso_dist_eq φ]; exact hx
        · intro hy
          refine ⟨φ.symm y, ?_, φ.apply_symm_apply y⟩
          have h1 : (G.induce ({v1'}ᶜ : Set V)).dist (φ.symm y) ⟨DG.c₁, gc1_ne⟩ =
              (H.induce ({v1}ᶜ : Set W)).dist y ⟨D'.c₂, hd2_ne⟩ := by
            rw [← iso_dist_eq φ, φ.apply_symm_apply, hmap1]
          have h2 : (G.induce ({v1'}ᶜ : Set V)).dist (φ.symm y) ⟨DG.c₂, gc2_ne⟩ =
              (H.induce ({v1}ᶜ : Set W)).dist y ⟨D'.c₁, hd1_ne⟩ := by
            rw [← iso_dist_eq φ, φ.apply_symm_apply, hmap2]
          omega
      have heq_card := congrArg Set.ncard hset_eq
      rw [Set.ncard_image_of_injective _ φ.injective, hcard_G1, hcard_H2] at heq_card
      change DG.A₁.card = D'.swap.A₁.card at heq_card
      omega
    · -- φ maps DG.c₁ ↦ D'.c₁, so DG.A₁ (size r+1) maps to D'.A₁ \ {v1} (size D'.A₁.card - 1)!
      have hset_eq : φ '' {x : ({v1'}ᶜ : Set V) |
          (G.induce ({v1'}ᶜ : Set V)).dist x ⟨DG.c₁, gc1_ne⟩ <
          (G.induce ({v1'}ᶜ : Set V)).dist x ⟨DG.c₂, gc2_ne⟩} =
          {y : ({v1}ᶜ : Set W) |
          (H.induce ({v1}ᶜ : Set W)).dist y ⟨D'.c₁, hd1_ne⟩ <
          (H.induce ({v1}ᶜ : Set W)).dist y ⟨D'.c₂, hd2_ne⟩} := by
        ext y
        simp only [Set.mem_image, Set.mem_ofPred_eq]
        constructor
        · rintro ⟨x, hx, rfl⟩
          rw [← hmap1, ← hmap2, iso_dist_eq φ, iso_dist_eq φ]; exact hx
        · intro hy
          refine ⟨φ.symm y, ?_, φ.apply_symm_apply y⟩
          have h1 : (G.induce ({v1'}ᶜ : Set V)).dist (φ.symm y) ⟨DG.c₁, gc1_ne⟩ =
              (H.induce ({v1}ᶜ : Set W)).dist y ⟨D'.c₁, hd1_ne⟩ := by
            rw [← iso_dist_eq φ, φ.apply_symm_apply, hmap1]
          have h2 : (G.induce ({v1'}ᶜ : Set V)).dist (φ.symm y) ⟨DG.c₂, gc2_ne⟩ =
              (H.induce ({v1}ᶜ : Set W)).dist y ⟨D'.c₂, hd2_ne⟩ := by
            rw [← iso_dist_eq φ, φ.apply_symm_apply, hmap2]
          omega
      have heq_card := congrArg Set.ncard hset_eq
      rw [Set.ncard_image_of_injective _ φ.injective, hcard_G1, hcard_H1] at heq_card
      change DG.A₁.card = D'.A₁.card - 1 at heq_card
      omega
  have hH1_eq : DH.A₁.card = r + 2 := hH_limb_eq DH hH1 hH2
  have hH2_eq : DH.swap.A₁.card = r + 2 := hH_limb_eq DH.swap hH2 hH1
  -- Step 2.2: Inspect the unique diameter-2r card H - w ≅ G - ur; WLOG w ∈ DH.swap.side₁!
  let w : W := σ ur
  obtain ⟨φw⟩ := hσ ur
  have hHw_tree : (H.induce ({w}ᶜ : Set W)).IsTree :=
    iso_isTree φw (delete_leaf_isTree DG.hT (by omega) hur_leaf)
  have hw_leaf : (H.neighborSet w).ncard = 1 := by
    change (H.neighborSet (σ ur)).ncard = 1; rw [← hdeg ur]; exact hur_leaf
  have hHw_diam : (H.induce ({w}ᶜ : Set W)).diam = 2 * r :=
    (iso_diam_eq φw).trans hdiam_Gur
  -- WLOG assume w ∈ DH.swap.side₁ by factoring the remaining argument into a symmetric helper
  have core : ∀ (DH' : BicenterData H r),
      DH'.A₁.card = r + 2 → DH'.swap.A₁.card = r + 2 → w ∈ DH'.swap.side₁ → False := by
    intro DH' hDH1 hDH2 hw_side2
    obtain ⟨a, x, i, ha0, hx_side, ha_side, ha_dist, ha_inj, hx_ne, ha_mem, hx_nb, ha_last,
      ha_deg3, ha_deg2, hx_dist⟩ := limb_card_eq_r_add_two_spec DH' hDH1
    obtain ⟨b, y, j, hb0, hy_side, hb_side, hb_dist, hb_inj, hy_ne, hb_mem, hy_nb, hb_last,
      hb_deg3, hb_deg2, hy_dist⟩ := limb_card_eq_r_add_two_spec DH'.swap hDH2
    let ai : W := a ⟨i.1, by omega⟩
    let bj : W := b ⟨j.1, by omega⟩
    let ar : W := a ⟨r, Nat.lt_succ_self r⟩
    let br : W := b ⟨r, Nat.lt_succ_self r⟩
    have hai_ne_bj : ai ≠ bj := fun h =>
      not_mem_side₁_of_mem_swap DH' (hb_side ⟨j.1, by omega⟩)
        (show bj ∈ DH'.side₁ by rw [← h]; exact ha_side ⟨i.1, by omega⟩)
    -- Characterize ALL degree-≥3 vertices of H: ONLY ai and bj (both deg 3)!
    have hH_deg3_iff : ∀ z : W, 3 ≤ (H.neighborSet z).ncard ↔ z = ai ∨ z = bj := by
      intro z
      constructor
      · intro hz3
        rcases lt_or_gt_of_ne (DH'.hne z) with hz1 | hz2
        · rcases (ha_mem z).mp hz1 with rfl | ⟨k, rfl⟩
          · rw [hx_nb, Set.ncard_singleton] at hz3; omega
          · by_cases hki : k.1 = i.1
            · left; congr 1; apply Fin.ext; exact hki
            · by_cases hkr : k.1 < r
              · have := ha_deg2 k hki hkr; omega
              · have hkeq : k = ⟨r, Nat.lt_succ_self r⟩ := Fin.ext (by dsimp only; have := k.isLt; omega)
                rw [hkeq, ha_last, Set.ncard_singleton] at hz3; omega
        · rcases (hb_mem z).mp hz2 with rfl | ⟨k, rfl⟩
          · rw [hy_nb, Set.ncard_singleton] at hz3; omega
          · by_cases hkj : k.1 = j.1
            · right; congr 1; apply Fin.ext; exact hkj
            · by_cases hkr : k.1 < r
              · have := hb_deg2 k hkj hkr; omega
              · have hkeq : k = ⟨r, Nat.lt_succ_self r⟩ := Fin.ext (by dsimp only; have := k.isLt; omega)
                rw [hkeq, hb_last, Set.ncard_singleton] at hz3; omega
      · rintro (rfl | rfl)
        · rw [ha_deg3]
        · rw [hb_deg3]
    -- Characterize ALL leaves of H: ONLY x, ar, y, br!
    have hH_leaf_iff : ∀ z : W, (H.neighborSet z).ncard = 1 ↔ z = x ∨ z = ar ∨ z = y ∨ z = br := by
      intro z
      constructor
      · intro hz1
        rcases lt_or_gt_of_ne (DH'.hne z) with hs1 | hs2
        · rcases (ha_mem z).mp hs1 with rfl | ⟨k, rfl⟩
          · exact Or.inl rfl
          · by_cases hki : k.1 = i.1
            · have : a k = ai := by congr 1; apply Fin.ext; exact hki
              rw [this, ha_deg3] at hz1; omega
            · by_cases hkr : k.1 < r
              · have := ha_deg2 k hki hkr; omega
              · right; left; congr 1; apply Fin.ext; dsimp only; have := k.isLt; omega
        · rcases (hb_mem z).mp hs2 with rfl | ⟨k, rfl⟩
          · exact Or.inr (Or.inr (Or.inl rfl))
          · by_cases hkj : k.1 = j.1
            · have : b k = bj := by congr 1; apply Fin.ext; exact hkj
              rw [this, hb_deg3] at hz1; omega
            · by_cases hkr : k.1 < r
              · have := hb_deg2 k hkj hkr; omega
              · right; right; right; congr 1; apply Fin.ext; dsimp only; have := k.isLt; omega
      · rintro (rfl | rfl | rfl | rfl)
        · rw [hx_nb, Set.ncard_singleton]
        · rw [ha_last, Set.ncard_singleton]
        · rw [hy_nb, Set.ncard_singleton]
        · rw [hb_last, Set.ncard_singleton]
    -- Since w ∈ DH'.swap.side₁ is a leaf with diam(H - w) = 2r, w must be br and j ≤ r - 2!
    have hw_far : H.dist w DH'.c₂ = r ∧ ∀ z ∈ DH'.swap.side₁, H.dist z DH'.c₂ = r → z = w := by
      by_contra hnot
      have hother : ∃ z ∈ DH'.swap.side₁, z ≠ w ∧ H.dist z DH'.c₂ = r := by
        by_cases hfw : H.dist w DH'.c₂ = r
        · push Not at hnot
          obtain ⟨z, hz1, hz2, hz3⟩ := hnot hfw
          exact ⟨z, hz1, hz3, hz2⟩
        · obtain ⟨z, hz1, hz2⟩ := exists_far_vertex DH'.swap
          exact ⟨z, hz1, fun h => hfw (h ▸ hz2), hz2⟩
      obtain ⟨-, -, hdiam_bad, -, -, -⟩ := delete_leaf_diam_preserving DH'.swap hW hw_side2 hw_leaf hother
      omega
    have hw_eq_br : w = br := (hw_far.2 br (hb_side _) (hb_dist _)).symm
    have hj_le : j.1 + 2 ≤ r := by
      by_contra hgt
      have hjeq : j.1 + 1 = r := by have := j.isLt; omega
      have hy_r : H.dist y DH'.c₂ = r := hy_dist.trans hjeq
      have hy_eq_w : y = w := hw_far.2 y hy_side hy_r
      exact hy_ne ⟨r, Nat.lt_succ_self r⟩ (hy_eq_w.trans hw_eq_br)
    obtain ⟨hd1_ne, -, hctr_Hw, hw_p⟩ :=
      delete_unique_far_leaf DH'.swap hW hw_side2 hw_leaf hw_far.1 hw_far.2
    have hφw_ctr : φw ⟨DG.c₂, hc2_ne⟩ = ⟨DH'.c₁, hd1_ne⟩ := iso_uniqueCenter_eq φw hctr_Gur hctr_Hw
    -- In H - w: BOTH ai and bj stay deg 3, at distances i and j + 1 from d₁!
    have hai_ne_w : ai ≠ w := fun h => not_mem_side₁_of_mem_swap DH' hw_side2 (by rw [← h]; exact ha_side _)
    have hbj_ne_w : bj ≠ w := fun h => by
      rw [hw_eq_br] at h
      have := congrArg Fin.val (hb_inj h); dsimp only at this; have := j.isLt; omega
    have hai_nadj_w : ¬ H.Adj ai w := fun hadj => by
      have := hw_p ai hadj.symm; rw [ha_deg3] at this; omega
    have hbj_nadj_w : ¬ H.Adj bj w := fun hadj => by
      have := hw_p bj hadj.symm; rw [hb_deg3] at this; omega
    have hai_deg3_Hw : 3 ≤ ((H.induce ({w}ᶜ : Set W)).neighborSet ⟨ai, hai_ne_w⟩).ncard := by
      rw [neighborSet_induce_compl_ncard_of_not_adj hai_nadj_w, ha_deg3]
    have hbj_deg3_Hw : 3 ≤ ((H.induce ({w}ᶜ : Set W)).neighborSet ⟨bj, hbj_ne_w⟩).ncard := by
      rw [neighborSet_induce_compl_ncard_of_not_adj hbj_nadj_w, hb_deg3]
    -- Pull back ai, bj via φw.symm to get the EXACT two deg-3 vertices p, q of G (both in DG.swap.side₁)!
    let p : V := (φw.symm ⟨ai, hai_ne_w⟩).1
    let q : V := (φw.symm ⟨bj, hbj_ne_w⟩).1
    have hp_ne_q : p ≠ q := fun h => by
      have hsub : φw.symm ⟨ai, hai_ne_w⟩ = φw.symm ⟨bj, hbj_ne_w⟩ := Subtype.ext h
      exact hai_ne_bj (congrArg Subtype.val (φw.symm.injective hsub))
    have hp_deg3 : 3 ≤ (G.neighborSet p).ncard := by
      have h1 : 3 ≤ ((G.induce ({ur}ᶜ : Set V)).neighborSet (φw.symm ⟨ai, hai_ne_w⟩)).ncard := by
        rw [iso_neighborSet_ncard φw.symm]; exact hai_deg3_Hw
      by_cases hadj : G.Adj p ur
      · have hstep := neighborSet_induce_compl_ncard_of_adj (v := ur) (x := φw.symm ⟨ai, hai_ne_w⟩) hadj
        dsimp only [p] at hstep ⊢; omega
      · rw [← neighborSet_induce_compl_ncard_of_not_adj (v := ur) (x := φw.symm ⟨ai, hai_ne_w⟩) hadj]; exact h1
    have hq_deg3 : 3 ≤ (G.neighborSet q).ncard := by
      have h1 : 3 ≤ ((G.induce ({ur}ᶜ : Set V)).neighborSet (φw.symm ⟨bj, hbj_ne_w⟩)).ncard := by
        rw [iso_neighborSet_ncard φw.symm]; exact hbj_deg3_Hw
      by_cases hadj : G.Adj q ur
      · have hstep := neighborSet_induce_compl_ncard_of_adj (v := ur) (x := φw.symm ⟨bj, hbj_ne_w⟩) hadj
        dsimp only [q] at hstep ⊢; omega
      · rw [← neighborSet_induce_compl_ncard_of_not_adj (v := ur) (x := φw.symm ⟨bj, hbj_ne_w⟩) hadj]; exact h1
    have hp_side2 : p ∈ DG.swap.side₁ := by
      by_contra hnot
      have hp1 : p ∈ DG.side₁ := (lt_or_gt_of_ne (DG.hne p)).resolve_right (by simpa [BicenterData.side₁, BicenterData.swap] using hnot)
      have := hu_le2 p hp1; omega
    have hq_side2 : q ∈ DG.swap.side₁ := by
      by_contra hnot
      have hq1 : q ∈ DG.side₁ := (lt_or_gt_of_ne (DG.hne q)).resolve_right (by simpa [BicenterData.side₁, BicenterData.swap] using hnot)
      have := hu_le2 q hq1; omega
    -- Compute exact distances: G.dist p c₂ = i and G.dist q c₂ = j + 1!
    have hp_dist : G.dist p DG.c₂ = i.1 := by
      have h1 := iso_dist_eq φw.symm ⟨ai, hai_ne_w⟩ ⟨DH'.c₁, hd1_ne⟩
      have hctr' : φw.symm ⟨DH'.c₁, hd1_ne⟩ = ⟨DG.c₂, hc2_ne⟩ := by
        rw [← hφw_ctr, φw.symm_apply_apply]
      rw [hctr', delete_leaf_dist DG.hT (by omega) hur_leaf,
          delete_leaf_dist DH'.hT (by omega) hw_leaf] at h1
      exact h1.trans (ha_dist ⟨i.1, by omega⟩)
    have hq_dist : G.dist q DG.c₂ = j.1 + 1 := by
      have h1 := iso_dist_eq φw.symm ⟨bj, hbj_ne_w⟩ ⟨DH'.c₁, hd1_ne⟩
      have hctr' : φw.symm ⟨DH'.c₁, hd1_ne⟩ = ⟨DG.c₂, hc2_ne⟩ := by
        rw [← hφw_ctr, φw.symm_apply_apply]
      rw [hctr', delete_leaf_dist DG.hT (by omega) hur_leaf,
          delete_leaf_dist DH'.hT (by omega) hw_leaf] at h1
      rw [h1, dist_c₂_of_side₁ DH'.swap (hb_side _), hb_dist]
    -- Also p and q are the ONLY vertices of degree ≥ 3 in G (and both have degree = 3)!
    have hG_deg3_iff : ∀ z : V, 3 ≤ (G.neighborSet z).ncard ↔ z = p ∨ z = q := by
      intro z
      constructor
      · intro hz3
        have hS_G : (Finset.univ.filter fun t : V => 3 ≤ (G.neighborSet t).ncard).card = 2 := by
          have hS_H : (Finset.univ.filter fun t : W => 3 ≤ (H.neighborSet t).ncard) = {ai, bj} := by
            ext t; simp [hH_deg3_iff]
          have hcard_H : (Finset.univ.filter fun t : W => 3 ≤ (H.neighborSet t).ncard).card = 2 := by
            rw [hS_H, Finset.card_pair hai_ne_bj]
          rw [← hcard_H]
          refine Finset.card_bij (fun t _ => σ t) ?_ ?_ ?_
          · intro t ht; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht ⊢
            rw [← hdeg t]; exact ht
          · intro t₁ _ t₂ _ h; exact σ.injective h
          · intro t ht; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht
            refine ⟨σ.symm t, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, σ.apply_symm_apply t⟩
            have := hdeg (σ.symm t); rw [σ.apply_symm_apply] at this; omega
        have hsub : ({p, q} : Finset V) ⊆ Finset.univ.filter fun t : V => 3 ≤ (G.neighborSet t).ncard := by
          intro t ht; simp only [Finset.mem_insert, Finset.mem_singleton] at ht
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          rcases ht with rfl | rfl <;> assumption
        have hEq := Finset.eq_of_subset_of_card_le hsub (by rw [Finset.card_pair hp_ne_q, hS_G])
        have hzmem : z ∈ ({p, q} : Finset V) := by rw [hEq]; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hz3⟩
        simpa using hzmem
      · rintro (rfl | rfl) <;> assumption
    have hG_deg_eq3 : (G.neighborSet p).ncard = 3 ∧ (G.neighborSet q).ncard = 3 := by
      have hle3 : ∀ z : V, (G.neighborSet z).ncard ≤ 3 := fun z => by
        rw [hdeg z]
        by_cases hz3 : 3 ≤ (H.neighborSet (σ z)).ncard
        · rcases (hH_deg3_iff (σ z)).mp hz3 with h | h
          · rw [h, ha_deg3]
          · rw [h, hb_deg3]
        · omega
      exact ⟨le_antisymm (hle3 p) hp_deg3, le_antisymm (hle3 q) hq_deg3⟩
    -- Step 2.3: Bicentral card H - x has unique deg-3 vertex bj at distance j from bicenter!
    -- Therefore j ∈ {G.dist p c₂, G.dist q c₂} = {i, j + 1}, forcing i = j!
    have hx_leaf : (H.neighborSet x).ncard = 1 := by rw [hx_nb, Set.ncard_singleton]
    have hx_other : ∃ z ∈ DH'.side₁, z ≠ x ∧ H.dist z DH'.c₁ = r :=
      ⟨ar, ha_side _, (hx_ne _).symm, ha_dist _⟩
    obtain ⟨hd1_x, hd2_x, hdiam_Hx, hbic_Hx, -, -⟩ :=
      delete_leaf_diam_preserving DH' hW hx_side hx_leaf hx_other
    let x' : V := σ.symm x
    obtain ⟨φx0⟩ := hσ x'
    have hσx' : σ x' = x := σ.apply_symm_apply x
    let φx : G.induce ({x'}ᶜ : Set V) ≃g H.induce ({x}ᶜ : Set W) :=
      φx0.trans (iso_induce_congr (by rw [hσx']))
    have hx'_leaf : (G.neighborSet x').ncard = 1 := by have := hdeg x'; rw [hσx'] at this; omega
    have hx'_diam : (G.induce ({x'}ᶜ : Set V)).diam = 2 * r + 1 := (iso_diam_eq φx.symm).trans hdiam_Hx
    have hx'_side2 : x' ∈ DG.swap.side₁ := by
      by_contra hnot
      have hx'1 : x' ∈ DG.side₁ := (lt_or_gt_of_ne (DG.hne x')).resolve_right (by simpa [BicenterData.side₁, BicenterData.swap] using hnot)
      obtain ⟨k, hk⟩ := (hu_mem x').mp hx'1
      by_cases hkr : k.1 < r
      · have := hu_mid k hkr; rw [hk] at this; omega
      · have hkeq : x' = ur := hk.symm.trans (by congr 1; apply Fin.ext; dsimp only; have := k.isLt; omega)
        have hdiam_eq : (G.induce ({x'}ᶜ : Set V)).diam = (G.induce ({ur}ᶜ : Set V)).diam :=
          iso_diam_eq (iso_induce_congr (by rw [hkeq])).symm
        omega
    have hx'_other : ∃ z ∈ DG.swap.side₁, z ≠ x' ∧ G.dist z DG.c₂ = r := by
      by_contra hnot
      push Not at hnot
      obtain ⟨z, hz_side, hz_dist⟩ := exists_far_vertex DG.swap
      have hzeq : z = x' := by by_contra hne; exact hnot z hz_side hne hz_dist
      rw [hzeq] at hz_dist
      obtain ⟨-, hdiam_bad, -, -⟩ := delete_unique_far_leaf DG.swap hV hx'_side2 hx'_leaf hz_dist
        (fun t ht hdt => by by_contra hne; exact hnot t ht hne hdt)
      omega
    obtain ⟨gc2_x, gc1_x, -, hbic_Gx', -, -⟩ :=
      delete_leaf_diam_preserving DG.swap hV hx'_side2 hx'_leaf hx'_other
    have hbj_ne_x : bj ≠ x := fun h =>
      not_mem_side₁_of_mem_swap DH' (hb_side ⟨j.1, by omega⟩) (show bj ∈ DH'.side₁ by rw [h]; exact hx_side)
    have hbj_nadj_x : ¬ H.Adj bj x := fun hadj => by
      have hmem : bj ∈ H.neighborSet x := hadj.symm
      rw [hx_nb, Set.mem_singleton_iff] at hmem
      exact hai_ne_bj hmem.symm
    have hbj_deg3_Hx : 3 ≤ ((H.induce ({x}ᶜ : Set W)).neighborSet ⟨bj, hbj_ne_x⟩).ncard := by
      rw [neighborSet_induce_compl_ncard_of_not_adj hbj_nadj_x, hb_deg3]
    let z_x : V := (φx.symm ⟨bj, hbj_ne_x⟩).1
    have hzx_deg3 : 3 ≤ (G.neighborSet z_x).ncard := by
      have h1 : 3 ≤ ((G.induce ({x'}ᶜ : Set V)).neighborSet (φx.symm ⟨bj, hbj_ne_x⟩)).ncard := by
        rw [iso_neighborSet_ncard φx.symm]; exact hbj_deg3_Hx
      by_cases hadj : G.Adj z_x x'
      · have hstep := neighborSet_induce_compl_ncard_of_adj (v := x') (x := φx.symm ⟨bj, hbj_ne_x⟩) hadj
        dsimp only [z_x] at hstep ⊢; omega
      · rw [← neighborSet_induce_compl_ncard_of_not_adj (v := x') (x := φx.symm ⟨bj, hbj_ne_x⟩) hadj]; exact h1
    -- Distance from z_x to bicenter {c₁, c₂} equals distance from bj to bicenter {d₁, d₂} = j!
    have hzx_dist_eq_j : G.dist z_x DG.c₂ = j.1 := by
      have hcne : (⟨DG.c₂, gc2_x⟩ : ({x'}ᶜ : Set V)) ≠ ⟨DG.c₁, gc1_x⟩ := fun h =>
        DG.hadj.ne (congrArg Subtype.val h).symm
      have hzx_s2 : z_x ∈ DG.swap.side₁ := by
        rcases (hG_deg3_iff z_x).mp hzx_deg3 with h | h <;> rw [h] <;> assumption
      have hmin_G : min ((G.induce ({x'}ᶜ : Set V)).dist (φx.symm ⟨bj, hbj_ne_x⟩) ⟨DG.c₂, gc2_x⟩)
          ((G.induce ({x'}ᶜ : Set V)).dist (φx.symm ⟨bj, hbj_ne_x⟩) ⟨DG.c₁, gc1_x⟩) = G.dist z_x DG.c₂ := by
        rw [delete_leaf_dist DG.hT (by omega) hx'_leaf, delete_leaf_dist DG.hT (by omega) hx'_leaf,
          dist_c₂_of_side₁ DG.swap hzx_s2]
        exact min_eq_left (Nat.le_succ _)
      have hmin_H : min ((H.induce ({x}ᶜ : Set W)).dist ⟨bj, hbj_ne_x⟩ ⟨DH'.c₁, hd1_x⟩)
          ((H.induce ({x}ᶜ : Set W)).dist ⟨bj, hbj_ne_x⟩ ⟨DH'.c₂, hd2_x⟩) = j.1 := by
        rw [delete_leaf_dist DH'.hT (by omega) hx_leaf, delete_leaf_dist DH'.hT (by omega) hx_leaf,
          dist_c₂_of_side₁ DH'.swap (hb_side _), hb_dist]
        exact min_eq_right (Nat.le_succ _)
      rcases iso_bicenterPair_eq φx hcne hbic_Gx' hbic_Hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have hd1 : (G.induce ({x'}ᶜ : Set V)).dist (φx.symm ⟨bj, hbj_ne_x⟩) ⟨DG.c₂, gc2_x⟩ =
            (H.induce ({x}ᶜ : Set W)).dist ⟨bj, hbj_ne_x⟩ ⟨DH'.c₁, hd1_x⟩ := by
          rw [← iso_dist_eq φx, φx.apply_symm_apply, h1]
        have hd2 : (G.induce ({x'}ᶜ : Set V)).dist (φx.symm ⟨bj, hbj_ne_x⟩) ⟨DG.c₁, gc1_x⟩ =
            (H.induce ({x}ᶜ : Set W)).dist ⟨bj, hbj_ne_x⟩ ⟨DH'.c₂, hd2_x⟩ := by
          rw [← iso_dist_eq φx, φx.apply_symm_apply, h2]
        rw [← hmin_G, hd1, hd2, hmin_H]
      · have hd1 : (G.induce ({x'}ᶜ : Set V)).dist (φx.symm ⟨bj, hbj_ne_x⟩) ⟨DG.c₂, gc2_x⟩ =
            (H.induce ({x}ᶜ : Set W)).dist ⟨bj, hbj_ne_x⟩ ⟨DH'.c₂, hd2_x⟩ := by
          rw [← iso_dist_eq φx, φx.apply_symm_apply, h1]
        have hd2 : (G.induce ({x'}ᶜ : Set V)).dist (φx.symm ⟨bj, hbj_ne_x⟩) ⟨DG.c₁, gc1_x⟩ =
            (H.induce ({x}ᶜ : Set W)).dist ⟨bj, hbj_ne_x⟩ ⟨DH'.c₁, hd1_x⟩ := by
          rw [← iso_dist_eq φx, φx.apply_symm_apply, h2]
        rw [← hmin_G, hd1, hd2, min_comm, hmin_H]
    have hij : i.1 = j.1 := by
      rcases (hG_deg3_iff z_x).mp hzx_deg3 with h | h
      · rw [h] at hzx_dist_eq_j; omega
      · rw [h] at hzx_dist_eq_j; omega
    -- Now i = j ≤ r - 2! So G.dist p c₂ = i and G.dist q c₂ = i + 1!
    -- Step 2.4: Show EVERY bicentral card H - t of H has:
    --   (a) EVERY deg-3 vertex at distance i from the bicenter, AND
    --   (b) EVERY deg-3 vertex adjacent to a leaf of H - t!
    have hH_bic_card_prop : ∀ (t : W), (H.neighborSet t).ncard = 1 →
        (H.induce ({t}ᶜ : Set W)).diam = 2 * r + 1 →
        ∀ (ht1 : DH'.c₁ ≠ t) (ht2 : DH'.c₂ ≠ t) (z : ({t}ᶜ : Set W)),
          3 ≤ ((H.induce ({t}ᶜ : Set W)).neighborSet z).ncard →
          min ((H.induce ({t}ᶜ : Set W)).dist z ⟨DH'.c₁, ht1⟩)
              ((H.induce ({t}ᶜ : Set W)).dist z ⟨DH'.c₂, ht2⟩) = i.1 ∧
          ∃ l : ({t}ᶜ : Set W), (H.induce ({t}ᶜ : Set W)).Adj z l ∧
            ((H.induce ({t}ᶜ : Set W)).neighborSet l).ncard = 1 := by
      intro t ht_leaf ht_diam ht1 ht2 z hz3
      have hz3_H : 3 ≤ (H.neighborSet z.1).ncard := by
        by_cases hadj : H.Adj z.1 t
        · have := neighborSet_induce_compl_ncard_of_adj (x := z) hadj; omega
        · rw [← neighborSet_induce_compl_ncard_of_not_adj (x := z) hadj]; exact hz3
      have ht_cases := (hH_leaf_iff t).mp ht_leaf
      have hdist_t := delete_leaf_dist DH'.hT (by omega) ht_leaf
      rcases (hH_deg3_iff z.1).mp hz3_H with hz_eq | hz_eq
      · -- z = ai: since deg_{H-t}(ai) ≥ 3 and deg_H(ai) = 3, t ≠ x!
        have hai_adj_x : H.Adj ai x :=
          (show ai ∈ H.neighborSet x by rw [hx_nb]; exact Set.mem_singleton _).symm
        have ht_ne_x : t ≠ x := fun h => by
          have hadj : H.Adj z.1 t := by rw [hz_eq, h]; exact hai_adj_x
          have := neighborSet_induce_compl_ncard_of_adj (x := z) hadj
          rw [hz_eq, ha_deg3] at this; omega
        refine ⟨?_, ?_⟩
        · rw [hdist_t, hdist_t, hz_eq, dist_c₂_of_side₁ DH' (ha_side _), ha_dist]
          exact min_eq_left (Nat.le_succ _)
        · refine ⟨⟨x, ht_ne_x.symm⟩, ?_, ?_⟩
          · change H.Adj z.1 x; rw [hz_eq]; exact hai_adj_x
          · have hnadj_xt : ¬ H.Adj x t := fun hadj => by
              have hmem : t ∈ H.neighborSet x := hadj
              rw [hx_nb, Set.mem_singleton_iff] at hmem
              rw [hmem, ha_deg3] at ht_leaf; omega
            rw [neighborSet_induce_compl_ncard_of_not_adj hnadj_xt, hx_nb, Set.ncard_singleton]
      · -- z = bj: similarly t ≠ y, so y is a leaf of H - t adjacent to bj!
        have hbj_adj_y : H.Adj bj y :=
          (show bj ∈ H.neighborSet y by rw [hy_nb]; exact Set.mem_singleton _).symm
        have ht_ne_y : t ≠ y := fun h => by
          have hadj : H.Adj z.1 t := by rw [hz_eq, h]; exact hbj_adj_y
          have := neighborSet_induce_compl_ncard_of_adj (x := z) hadj
          rw [hz_eq, hb_deg3] at this; omega
        refine ⟨?_, ?_⟩
        · rw [hdist_t, hdist_t, hz_eq, dist_c₂_of_side₁ DH'.swap (hb_side _), hb_dist, hij]
          exact min_eq_right (Nat.le_succ _)
        · refine ⟨⟨y, ht_ne_y.symm⟩, ?_, ?_⟩
          · change H.Adj z.1 y; rw [hz_eq]; exact hbj_adj_y
          · have hnadj_yt : ¬ H.Adj y t := fun hadj => by
              have hmem : t ∈ H.neighborSet y := hadj
              rw [hy_nb, Set.mem_singleton_iff] at hmem
              rw [hmem, hb_deg3] at ht_leaf; omega
            rw [neighborSet_induce_compl_ncard_of_not_adj hnadj_yt, hy_nb, Set.ncard_singleton]
    -- Step 2.5: Transfer that property to ANY bicentral card G - v (v ∈ DG.swap.side₁) of G!
    have hG_bic_card_prop : ∀ (v : V), v ∈ DG.swap.side₁ → (G.neighborSet v).ncard = 1 →
        (∃ a' ∈ DG.swap.side₁, a' ≠ v ∧ G.dist a' DG.c₂ = r) →
        ∀ (z : ({v}ᶜ : Set V)),
          3 ≤ ((G.induce ({v}ᶜ : Set V)).neighborSet z).ncard →
          G.dist z.1 DG.c₂ = i.1 ∧
          ∃ l : ({v}ᶜ : Set V), (G.induce ({v}ᶜ : Set V)).Adj z l ∧
            ((G.induce ({v}ᶜ : Set V)).neighborSet l).ncard = 1 := by
      intro v hv_s2 hv_leaf hv_other z hz3
      obtain ⟨gc2_v, gc1_v, hdiam_Gv, hbic_Gv, -, -⟩ :=
        delete_leaf_diam_preserving DG.swap hV hv_s2 hv_leaf hv_other
      obtain ⟨φv⟩ := hσ v
      let t : W := σ v
      have ht_leaf : (H.neighborSet t).ncard = 1 := by rw [← hdeg v]; exact hv_leaf
      have ht_diam : (H.induce ({t}ᶜ : Set W)).diam = 2 * r + 1 :=
        (iso_diam_eq φv).trans hdiam_Gv
      -- t must have a bicenter pair in H - t with DH'.c₁, DH'.c₂!
      have ht_bic : ∃ (ht1 : DH'.c₁ ≠ t) (ht2 : DH'.c₂ ≠ t),
          IsBicenterPair (H.induce ({t}ᶜ : Set W)) ⟨DH'.c₁, ht1⟩ ⟨DH'.c₂, ht2⟩ r := by
        rcases lt_or_gt_of_ne (DH'.hne t) with ht_s1 | ht_s2
        · have ht_other : ∃ z' ∈ DH'.side₁, z' ≠ t ∧ H.dist z' DH'.c₁ = r := by
            by_contra hnot; push Not at hnot
            obtain ⟨z', hz'1, hz'2⟩ := exists_far_vertex DH'
            have hzeq : z' = t := by by_contra hne; exact hnot z' hz'1 hne hz'2
            rw [hzeq] at hz'2
            obtain ⟨-, hdiam_bad, -, -⟩ := delete_unique_far_leaf DH' hW ht_s1 ht_leaf hz'2
              (fun s hs hds => by by_contra hne; exact hnot s hs hne hds)
            omega
          obtain ⟨ht1, ht2, -, hbic, -, -⟩ := delete_leaf_diam_preserving DH' hW ht_s1 ht_leaf ht_other
          exact ⟨ht1, ht2, hbic⟩
        · have ht_other : ∃ z' ∈ DH'.swap.side₁, z' ≠ t ∧ H.dist z' DH'.c₂ = r := by
            by_contra hnot; push Not at hnot
            obtain ⟨z', hz'1, hz'2⟩ := exists_far_vertex DH'.swap
            have hzeq : z' = t := by by_contra hne; exact hnot z' hz'1 hne hz'2
            rw [hzeq] at hz'2
            obtain ⟨-, hdiam_bad, -, -⟩ := delete_unique_far_leaf DH'.swap hW ht_s2 ht_leaf hz'2
              (fun s hs hds => by by_contra hne; exact hnot s hs hne hds)
            omega
          obtain ⟨ht2, ht1, -, hbic, -, -⟩ := delete_leaf_diam_preserving DH'.swap hW ht_s2 ht_leaf ht_other
          exact ⟨ht1, ht2, ⟨fun u => ⟨(hbic.1 u).2, (hbic.1 u).1⟩, fun u h1 h2 => hbic.2 u h2 h1⟩⟩
      obtain ⟨ht1, ht2, hbic_Ht⟩ := ht_bic
      have hφz3 : 3 ≤ ((H.induce ({t}ᶜ : Set W)).neighborSet (φv z)).ncard := by
        rw [iso_neighborSet_ncard φv]; exact hz3
      obtain ⟨hmin_H, l_H, hl_adj, hl_deg1⟩ := hH_bic_card_prop t ht_leaf ht_diam ht1 ht2 (φv z) hφz3
      have hz3_G : 3 ≤ (G.neighborSet z.1).ncard := by
        by_cases hadj : G.Adj z.1 v
        · have := neighborSet_induce_compl_ncard_of_adj (x := z) hadj; omega
        · rw [← neighborSet_induce_compl_ncard_of_not_adj (x := z) hadj]; exact hz3
      have hz_s2 : z.1 ∈ DG.swap.side₁ := by
        rcases (hG_deg3_iff z.1).mp hz3_G with h | h <;> rw [h] <;> assumption
      have hcne : (⟨DG.c₂, gc2_v⟩ : ({v}ᶜ : Set V)) ≠ ⟨DG.c₁, gc1_v⟩ := fun h =>
        DG.hadj.ne (congrArg Subtype.val h).symm
      have hdist_z : G.dist z.1 DG.c₂ = i.1 := by
        have hmin_G : min ((G.induce ({v}ᶜ : Set V)).dist z ⟨DG.c₂, gc2_v⟩)
            ((G.induce ({v}ᶜ : Set V)).dist z ⟨DG.c₁, gc1_v⟩) = G.dist z.1 DG.c₂ := by
          rw [delete_leaf_dist DG.hT (by omega) hv_leaf, delete_leaf_dist DG.hT (by omega) hv_leaf,
            dist_c₂_of_side₁ DG.swap hz_s2]
          exact min_eq_left (Nat.le_succ _)
        rcases iso_bicenterPair_eq φv hcne hbic_Gv hbic_Ht with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · rw [← hmin_G, ← iso_dist_eq φv z ⟨DG.c₂, gc2_v⟩, ← iso_dist_eq φv z ⟨DG.c₁, gc1_v⟩, h1, h2, hmin_H]
        · rw [← hmin_G, ← iso_dist_eq φv z ⟨DG.c₂, gc2_v⟩, ← iso_dist_eq φv z ⟨DG.c₁, gc1_v⟩, h1, h2, min_comm, hmin_H]
      refine ⟨hdist_z, φv.symm l_H, ?_, ?_⟩
      · rw [← φv.map_rel_iff, φv.apply_symm_apply]; exact hl_adj
      · rw [iso_neighborSet_ncard φv.symm]; exact hl_deg1
    -- Step 2.6: Count the leaves of G in DG.swap.side₁ (= 3 leaves) and derive the final contradiction!
    have hL_H : (Finset.univ.filter fun t : W => (H.neighborSet t).ncard = 1) = {x, ar, y, br} := by
      ext t; simp [hH_leaf_iff]
    have h_x_ne_ar : x ≠ ar := hx_ne _
    have h_y_ne_br : y ≠ br := hy_ne _
    have h_x_ne_y : x ≠ y := fun h => not_mem_side₁_of_mem_swap DH' hy_side (by rw [← h]; exact hx_side)
    have h_x_ne_br : x ≠ br := fun h =>
      not_mem_side₁_of_mem_swap DH' (hb_side ⟨r, Nat.lt_succ_self r⟩) (show br ∈ DH'.side₁ by rw [← h]; exact hx_side)
    have h_ar_ne_y : ar ≠ y := fun h =>
      not_mem_side₁_of_mem_swap DH' hy_side (by rw [← h]; exact ha_side ⟨r, Nat.lt_succ_self r⟩)
    have h_ar_ne_br : ar ≠ br := fun h =>
      not_mem_side₁_of_mem_swap DH' (hb_side ⟨r, Nat.lt_succ_self r⟩)
        (show br ∈ DH'.side₁ by rw [← h]; exact ha_side ⟨r, Nat.lt_succ_self r⟩)
    have hL_H_card : (Finset.univ.filter fun t : W => (H.neighborSet t).ncard = 1).card = 4 := by
      rw [hL_H, Finset.card_insert_of_notMem (by simp [h_x_ne_ar, h_x_ne_y, h_x_ne_br]),
        Finset.card_insert_of_notMem (by simp [h_ar_ne_y, h_ar_ne_br]),
        Finset.card_pair h_y_ne_br]
    let LG : Finset V := Finset.univ.filter fun t : V => (G.neighborSet t).ncard = 1
    have hLG_card : LG.card = 4 := by
      rw [← hL_H_card]
      refine Finset.card_bij (fun t _ => σ t) ?_ ?_ ?_
      · intro t ht; simp only [LG, Finset.mem_filter, Finset.mem_univ, true_and] at ht ⊢
        rw [← hdeg t]; exact ht
      · intro t₁ _ t₂ _ h; exact σ.injective h
      · intro t ht; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht
        refine ⟨σ.symm t, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, σ.apply_symm_apply t⟩
        have := hdeg (σ.symm t); rw [σ.apply_symm_apply] at this; omega
    let L2 : Finset V := LG.erase ur
    have hL2_card : L2.card = 3 := by
      have hur_LG : ur ∈ LG := Finset.mem_filter.mpr ⟨Finset.mem_univ ur, hur_leaf⟩
      change (LG.erase ur).card = 3
      rw [Finset.card_erase_of_mem hur_LG, hLG_card]
    have hL2_side2 : ∀ v ∈ L2, v ∈ DG.swap.side₁ ∧ (G.neighborSet v).ncard = 1 := by
      intro v hv
      have hv_ne_ur : v ≠ ur := (Finset.mem_erase.mp hv).1
      have hv_leaf : (G.neighborSet v).ncard = 1 := (Finset.mem_filter.mp (Finset.mem_erase.mp hv).2).2
      refine ⟨?_, hv_leaf⟩
      by_contra hnot
      have hv1 : v ∈ DG.side₁ :=
        (lt_or_gt_of_ne (DG.hne v)).resolve_right (by simpa [BicenterData.side₁, BicenterData.swap] using hnot)
      obtain ⟨k, rfl⟩ := (hu_mem v).mp hv1
      by_cases hkr : k.1 < r
      · have := hu_mid k hkr; omega
      · exact hv_ne_ur (by congr 1; apply Fin.ext; dsimp only; have := k.isLt; omega)
    -- Every diam-preserving leaf v ∈ L2 MUST be adjacent to q (otherwise q stays deg 3 at dist i+1 ≠ i)!
    have hdp_adj_q : ∀ v ∈ L2, (∃ a' ∈ DG.swap.side₁, a' ≠ v ∧ G.dist a' DG.c₂ = r) → G.Adj q v := by
      intro v hv hv_other
      by_contra hnadj
      obtain ⟨hv_s2, hv_leaf⟩ := hL2_side2 v hv
      have hq_ne_v : q ≠ v := fun h => by rw [h] at hq_deg3; omega
      have hq3' : 3 ≤ ((G.induce ({v}ᶜ : Set V)).neighborSet ⟨q, hq_ne_v⟩).ncard := by
        rw [neighborSet_induce_compl_ncard_of_not_adj hnadj]; exact hq_deg3
      obtain ⟨hdq_eq, -⟩ := hG_bic_card_prop v hv_s2 hv_leaf hv_other ⟨q, hq_ne_v⟩ hq3'
      dsimp only at hdq_eq
      omega
    -- q ≠ c₂ (since G.dist q c₂ = j + 1 ≥ 1), so q has a parent pq which is NOT a leaf of G!
    have hq_nec2 : q ≠ DG.c₂ := fun h => by rw [h, SimpleGraph.dist_self] at hq_dist; omega
    obtain ⟨pq, ⟨hpq_adj, hpq_dist⟩, -⟩ := tree_unique_parent DG.hT hq_nec2
    have hpq_not_leaf : (G.neighborSet pq).ncard ≠ 1 := by
      intro h1
      by_cases hpq_c2 : pq = DG.c₂
      · have hne : DG.c₁ ≠ q := fun h => not_mem_side₁_of_mem_swap DG hq_side2 (by rw [← h]; exact mem_side₁_self DG)
        exact hne (leaf_adj_unique h1 (by rw [hpq_c2]; exact DG.hadj.symm) hpq_adj.symm)
      · obtain ⟨gp, ⟨hgp_adj, hgp_dist⟩, -⟩ := tree_unique_parent DG.hT hpq_c2
        have hne : gp ≠ q := fun h => by rw [h] at hgp_dist; omega
        exact hne (leaf_adj_unique h1 hgp_adj hpq_adj.symm)
    -- So q has at most 2 neighbors in L2!
    let Qnb : Finset V := L2.filter (fun v => G.Adj q v)
    have hQnb_le2 : Qnb.card ≤ 2 := by
      have hsub : insert pq (Qnb : Set V) ⊆ G.neighborSet q := by
        rintro t (rfl | ht)
        · exact hpq_adj
        · exact (Finset.mem_filter.mp ht).2
      have hpq_not : pq ∉ (Qnb : Set V) := fun h =>
        hpq_not_leaf (hL2_side2 pq (Finset.mem_filter.mp h).1).2
      have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
      rw [Set.ncard_insert_of_notMem hpq_not (Set.toFinite _), Set.ncard_coe_finset, hG_deg_eq3.2] at hle
      omega
    -- Therefore L2 \ Qnb is nonempty, and every v ∈ L2 \ Qnb MUST be the unique depth-r vertex of G₂!
    have hnotQ_ne : (L2 \ Qnb).Nonempty := by
      have hQsub : Qnb ⊆ L2 := Finset.filter_subset _ _
      rw [← Finset.card_pos, Finset.card_sdiff_of_subset hQsub]
      omega
    obtain ⟨v_deep, hv_deep_mem⟩ := hnotQ_ne
    have hv_deep_L2 : v_deep ∈ L2 := (Finset.mem_sdiff.mp hv_deep_mem).1
    have hv_deep_nadj : ¬ G.Adj q v_deep := fun h =>
      (Finset.mem_sdiff.mp hv_deep_mem).2 (Finset.mem_filter.mpr ⟨hv_deep_L2, h⟩)
    have hv_deep_uniq : ∀ a' ∈ DG.swap.side₁, G.dist a' DG.c₂ = r → a' = v_deep := by
      intro a' ha' hda'
      by_contra hne
      exact hv_deep_nadj (hdp_adj_q v_deep hv_deep_L2 ⟨a', ha', hne, hda'⟩)
    have hv_deep_dist : G.dist v_deep DG.c₂ = r := by
      obtain ⟨a', ha', hda'⟩ := exists_far_vertex DG.swap
      rw [← hv_deep_uniq a' ha' hda']; exact hda'
    -- Any OTHER leaf v₁ ∈ L2 \ {v_deep} is diam-preserving, hence adjacent to q!
    have hL2_rest_card : (L2.erase v_deep).card = 2 := by
      rw [Finset.card_erase_of_mem hv_deep_L2, hL2_card]
    obtain ⟨v₁, v₂, hv12_ne, hL2_rest_eq⟩ := Finset.card_eq_two.mp hL2_rest_card
    have hv1_L2 : v₁ ∈ L2 := (Finset.mem_erase.mp (by rw [hL2_rest_eq]; simp)).2
    have hv2_L2 : v₂ ∈ L2 := (Finset.mem_erase.mp (by rw [hL2_rest_eq]; simp)).2
    have hv1_ne_deep : v₁ ≠ v_deep := (Finset.mem_erase.mp (by rw [hL2_rest_eq]; simp)).1
    have hv2_ne_deep : v₂ ≠ v_deep := (Finset.mem_erase.mp (by rw [hL2_rest_eq]; simp)).1
    have hv1_adj_q : G.Adj q v₁ :=
      hdp_adj_q v₁ hv1_L2 ⟨v_deep, (hL2_side2 v_deep hv_deep_L2).1, hv1_ne_deep.symm, hv_deep_dist⟩
    have hv2_adj_q : G.Adj q v₂ :=
      hdp_adj_q v₂ hv2_L2 ⟨v_deep, (hL2_side2 v_deep hv_deep_L2).1, hv2_ne_deep.symm, hv_deep_dist⟩
    -- Now in G - v₁ (a bicentral card!), p stays degree 3 (v₁'s unique neighbor is q ≠ p)!
    have hp_ne_v1 : p ≠ v₁ := fun h => by rw [h] at hp_deg3; have := (hL2_side2 v₁ hv1_L2).2; omega
    have hp_nadj_v1 : ¬ G.Adj p v₁ := fun hadj =>
      hp_ne_q (leaf_adj_unique (hL2_side2 v₁ hv1_L2).2 hadj.symm hv1_adj_q.symm)
    have hp3_Gv1 : 3 ≤ ((G.induce ({v₁}ᶜ : Set V)).neighborSet ⟨p, hp_ne_v1⟩).ncard := by
      rw [neighborSet_induce_compl_ncard_of_not_adj hp_nadj_v1]; exact hp_deg3
    obtain ⟨-, l, hl_adj, hl_deg1⟩ := hG_bic_card_prop v₁ (hL2_side2 v₁ hv1_L2).1 (hL2_side2 v₁ hv1_L2).2
      ⟨v_deep, (hL2_side2 v_deep hv_deep_L2).1, hv1_ne_deep.symm, hv_deep_dist⟩ ⟨p, hp_ne_v1⟩ hp3_Gv1
    -- l is a leaf of G - v₁ adjacent to p!
    -- Show l.1 cannot be q (since deg_{G - v₁}(q) = 2 ≠ 1):
    have hl_ne_q : l.1 ≠ q := by
      intro hq_eq
      have hq_ne_v1 : q ≠ v₁ := hv1_adj_q.ne
      have hsub : l = ⟨q, hq_ne_v1⟩ := Subtype.ext hq_eq
      rw [hsub] at hl_deg1
      have := neighborSet_induce_compl_ncard_of_adj (v := v₁) (x := ⟨q, hq_ne_v1⟩) hv1_adj_q
      rw [hl_deg1, hG_deg_eq3.2] at this
      omega
    -- Since l.1 ≠ q and v₁'s only neighbor is q, l.1 is not adjacent to v₁, so l.1 is a leaf of G!
    have hl_nadj_v1 : ¬ G.Adj l.1 v₁ := fun hadj =>
      hl_ne_q (leaf_adj_unique (hL2_side2 v₁ hv1_L2).2 hadj.symm hv1_adj_q.symm)
    have hl_leaf_G : (G.neighborSet l.1).ncard = 1 := by
      rw [← neighborSet_induce_compl_ncard_of_not_adj hl_nadj_v1]; exact hl_deg1
    have hl_in_LG : l.1 ∈ LG := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hl_leaf_G⟩
    -- Check the 4 elements of LG = {ur, v_deep, v₁, v₂}:
    by_cases hl_ur : l.1 = ur
    · -- l.1 = ur ∈ DG.side₁, p ∈ DG.swap.side₁ -> adj across forces ur = DG.c₁, impossible!
      obtain ⟨hc1, -⟩ := eq_center_of_adj_across DG hur_side hp_side2 (by rw [← hl_ur]; exact hl_adj.symm)
      have hdur : G.dist ur DG.c₁ = r := hu_dist ⟨r, Nat.lt_succ_self r⟩
      rw [hc1, SimpleGraph.dist_self] at hdur; have := DG.hr; omega
    · have hl_L2 : l.1 ∈ L2 := Finset.mem_erase.mpr ⟨hl_ur, hl_in_LG⟩
      by_cases hl_deep : l.1 = v_deep
      · -- l.1 = v_deep has dist r from c₂, while p has dist i ≤ r - 2!
        have htri : G.dist v_deep DG.c₂ ≤ G.dist v_deep p + G.dist p DG.c₂ :=
          DG.hT.connected.dist_triangle
        have h1 : G.dist v_deep p = 1 := dist_eq_one_iff_adj.mpr (by rw [← hl_deep]; exact hl_adj.symm)
        omega
      · have hl_rest : l.1 ∈ L2.erase v_deep := Finset.mem_erase.mpr ⟨hl_deep, hl_L2⟩
        rw [hL2_rest_eq, Finset.mem_insert, Finset.mem_singleton] at hl_rest
        rcases hl_rest with hl1 | hl2
        · exact l.2 hl1
        · -- l.1 = v₂, whose unique neighbor in G is q, contradicting G.Adj p v₂ and p ≠ q!
          exact hp_ne_q (leaf_adj_unique (hL2_side2 v₂ hv2_L2).2 (by rw [← hl2]; exact hl_adj.symm) hv2_adj_q.symm)
  rcases lt_or_gt_of_ne (DH.hne w) with hw1 | hw2
  · exact core DH.swap hH2_eq hH1_eq hw1
  · exact core DH hH1_eq hH2_eq hw2

/- ### Part 9: Main theorem for `H4` -/

theorem main :
    OMA.R_ReconstructionConjecture_reconstruction_conjecture_variants_tree_R1_H4_R1.H4 := by
  intro V W _ _ hV G H σ hTG hTH hσ hdeg hnonpath r hr1 hGdiam hHdiam _hkelly
    c₁ c₂ hc_adj _hc_ctr hc_ne hc_le1 hc_le2 hc_t1 hc_t2 hc_dist
    d₁ d₂ hd_adj _hd_ctr hd_ne hd_le1 hd_le2 hd_t1 hd_t2 hd_dist hsmall
  let DG : BicenterData G r :=
    ⟨c₁, c₂, hr1, hTG, hGdiam, hc_adj, hc_ne, hc_le1, hc_le2, hc_t1, hc_t2, hc_dist⟩
  let DH : BicenterData H r :=
    ⟨d₁, d₂, hr1, hTH, hHdiam, hd_adj, hd_ne, hd_le1, hd_le2, hd_t1, hd_t2, hd_dist⟩
  -- Helper when DG' has |DG'.A₁| ≤ r + 1
  have solve_left : ∀ (DG' : BicenterData G r), DG'.A₁.card ≤ r + 1 → Nonempty (G ≃g H) := by
    intro DG' hG'1
    by_cases hH1 : DH.A₁.card ≤ r + 1
    · exact case_both_path_limb hV σ hσ hnonpath DG' DH hG'1 hH1
    · by_cases hH2 : DH.swap.A₁.card ≤ r + 1
      · exact case_both_path_limb hV σ hσ hnonpath DG' DH.swap hG'1 hH2
      · exfalso
        exact case_one_path_limb_impossible hV σ hσ hdeg DG' DH hG'1 (by omega) (by omega)
  -- Helper when DH' has |DH'.A₁| ≤ r + 1 (by symmetry, swap G and H via σ.symm)
  have solve_right : ∀ (DH' : BicenterData H r), DH'.A₁.card ≤ r + 1 → Nonempty (G ≃g H) := by
    intro DH' hH'1
    have hW : 3 ≤ Fintype.card W := by rw [← Fintype.card_congr σ]; exact hV
    have hσ' : ∀ y : W, Nonempty (H.induce {y}ᶜ ≃g G.induce {σ.symm y}ᶜ) := fun y => by
      obtain ⟨φ⟩ := hσ (σ.symm y)
      exact ⟨(iso_induce_congr (by rw [σ.apply_symm_apply])).trans φ.symm⟩
    have hdeg' : ∀ y : W, (H.neighborSet y).ncard = (G.neighborSet (σ.symm y)).ncard := fun y => by
      have := hdeg (σ.symm y); rw [σ.apply_symm_apply] at this; exact this.symm
    have hnonpathH : ∃ y : W, 3 ≤ (H.neighborSet y).ncard := by
      obtain ⟨v, hv⟩ := hnonpath
      exact ⟨σ v, by rw [← hdeg v]; exact hv⟩
    by_cases hG1 : DG.A₁.card ≤ r + 1
    · obtain ⟨φ⟩ := case_both_path_limb hW σ.symm hσ' hnonpathH DH' DG hH'1 hG1
      exact ⟨φ.symm⟩
    · by_cases hG2 : DG.swap.A₁.card ≤ r + 1
      · obtain ⟨φ⟩ := case_both_path_limb hW σ.symm hσ' hnonpathH DH' DG.swap hH'1 hG2
        exact ⟨φ.symm⟩
      · exfalso
        exact case_one_path_limb_impossible hW σ.symm hσ' hdeg' DH' DG hH'1 (by omega) (by omega)
  rcases hsmall with h1 | h2 | h3 | h4
  · exact solve_left DG (by rw [A₁_card_eq_ncard]; exact h1)
  · exact solve_left DG.swap (by rw [A₁_card_eq_ncard]; exact h2)
  · exact solve_right DH (by rw [A₁_card_eq_ncard]; exact h3)
  · exact solve_right DH.swap (by rw [A₁_card_eq_ncard]; exact h4)

end TreeH4Proof

theorem OMA.solution :
    OMA.R_ReconstructionConjecture_reconstruction_conjecture_variants_tree_R1_H4_R1.H4 :=
  TreeH4Proof.main
