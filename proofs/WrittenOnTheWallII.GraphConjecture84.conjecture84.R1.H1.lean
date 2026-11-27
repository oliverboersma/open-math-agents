import OMAReductions.R_WrittenOnTheWallII_GraphConjecture84_conjecture84_R1

/-! The leaf case of the radius bound for induced trees. -/

namespace OMA.W84H1

open SimpleGraph
open OMA.R_WrittenOnTheWallII_GraphConjecture84_conjecture84_R1

variable {V : Type} {G : SimpleGraph V}

/-- Distance from the start to the indexed vertex of a geodesic.
Adapted from the merged H2 proof by @ivillar. -/
private lemma geo_dist (hc : G.Connected) {u v : V} (p : G.Walk u v)
    (hp : p.length = G.dist u v) {i : ℕ} (hi : i ≤ p.length) :
    G.dist u (p.getVert i) = i := by
  have h₁ := dist_le (p.take i)
  rw [Walk.take_length, min_eq_left hi] at h₁
  have h₂ := dist_le (p.drop i)
  rw [Walk.drop_length] at h₂
  have h₃ := hc.dist_triangle (u := u) (v := p.getVert i) (w := v)
  omega

private lemma geo_dist_end (hc : G.Connected) {u v : V} (p : G.Walk u v)
    (hp : p.length = G.dist u v) {i : ℕ} (hi : i ≤ p.length) :
    G.dist (p.getVert i) v = p.length - i := by
  have h₁ := geo_dist hc p hp hi
  have h₂ := dist_le (p.drop i)
  rw [Walk.drop_length] at h₂
  have h₃ := hc.dist_triangle (u := u) (v := p.getVert i) (w := v)
  omega

private lemma far_vertex [Finite V] (hc : G.Connected) {r : ℕ}
    (hr : r ≤ G.radius.toNat) (x : V) : ∃ y, r ≤ G.dist x y := by
  obtain ⟨y, hy⟩ := G.exists_edist_eq_eccent_of_finite x
  refine ⟨y, hr.trans ?_⟩
  have h := ENat.toNat_le_toNat (G.radius_le_eccent (u := x))
    (hy ▸ edist_ne_top_iff_reachable.mpr (hc x y))
  simpa [← hy, ← (hc x y).coe_dist_eq_edist] using h

private def Avoid (G : SimpleGraph V) (a x y : V) : Prop :=
  ∃ p : G.Walk x y, a ∉ p.support

private lemma Avoid.symm {a x y : V} (h : Avoid G a x y) : Avoid G a y x := by
  obtain ⟨p, hp⟩ := h
  exact ⟨p.reverse, by simpa using hp⟩

private lemma Avoid.trans {a x y z : V} (h₁ : Avoid G a x y) (h₂ : Avoid G a y z) :
    Avoid G a x z := by
  obtain ⟨p, hp⟩ := h₁
  obtain ⟨q, hq⟩ := h₂
  exact ⟨p.append q, by simp [Walk.mem_support_append_iff, hp, hq]⟩

private lemma Avoid.adj {a x y : V} (h : G.Adj x y) (hx : x ≠ a) (hy : y ≠ a) :
    Avoid G a x y :=
  ⟨h.toWalk, by simp [Adj.toWalk, hx.symm, hy.symm]⟩

private lemma connected_delete_iff {a c : V} (hca : c ≠ a) :
    (G.induce ({a}ᶜ : Set V)).Connected ↔ ∀ x, x ≠ a → Avoid G a c x := by
  let c' : ({a}ᶜ : Set V) := ⟨c, hca⟩
  let e := SimpleGraph.Embedding.induce (G := G) ({a}ᶜ : Set V)
  constructor
  · intro hc x hx
    obtain ⟨p⟩ := hc c' ⟨x, hx⟩
    have hmap : a ∉ (p.map e.toHom).support := by
      simp only [Walk.support_map, List.mem_map]
      rintro ⟨w, _, hw⟩
      exact w.property hw
    exact ⟨p.map e.toHom, hmap⟩
  · intro h
    apply (connected_iff_exists_forall_reachable _).2
    refine ⟨c', fun x => ?_⟩
    obtain ⟨p, hp⟩ := h x x.property
    exact ⟨(p.induce _ (fun z hz => show z ≠ a from fun he => hp (he ▸ hz))).copy rfl rfl⟩

private lemma avoid_of_dist_lt (hc : G.Connected) {a x y : V}
    (h : G.dist x y < G.dist x a) : Avoid G a x y := by
  obtain ⟨p, hp⟩ := hc.exists_walk_length_eq_dist x y
  refine ⟨p, fun ha => ?_⟩
  obtain ⟨i, rfl, hi⟩ := Walk.mem_support_iff_exists_getVert.mp ha
  have := geo_dist hc p hp hi
  omega

private lemma dist_through (hc : G.Connected) {a x y : V} (h : ¬Avoid G a x y) :
    G.dist x y = G.dist x a + G.dist a y := by
  classical
  obtain ⟨p, hp⟩ := hc.exists_walk_length_eq_dist x y
  have ha : a ∈ p.support := by
    by_contra hn
    exact h ⟨p, hn⟩
  obtain ⟨q, t, rfl⟩ := Walk.mem_support_iff_exists_append.mp ha
  have h₁ := dist_le q
  have h₂ := dist_le t
  have h₃ := hc.dist_triangle (u := x) (v := a) (w := y)
  rw [Walk.length_append] at hp
  omega

private lemma first_step (hc : G.Connected) {a y : V} (hay : a ≠ y) :
    ∃ z, G.Adj a z ∧ Avoid G a z y := by
  obtain ⟨p, hp⟩ := hc.exists_walk_length_eq_dist a y
  have hl : 0 < p.length := hp ▸ hc.pos_dist_of_ne hay
  refine ⟨p.getVert 1, p.adj_snd (Walk.not_nil_of_ne hay), p.drop 1, ?_⟩
  intro ha
  obtain ⟨i, hi, hil⟩ := Walk.mem_support_iff_exists_getVert.mp ha
  rw [Walk.drop_getVert] at hi
  have hb : 1 + i ≤ p.length := by simp only [Walk.drop_length] at hil; omega
  have := geo_dist hc p hp hb
  rw [hi, dist_self] at this
  omega

private lemma off_neighbor (hc : G.Connected) {a c : V} (hca : c ≠ a)
    (hcut : ¬(G.induce ({a}ᶜ : Set V)).Connected) :
    ∃ z, G.Adj a z ∧ ¬Avoid G a c z := by
  have hn := mt (connected_delete_iff hca).2 hcut
  push Not at hn
  obtain ⟨y, hya, hy⟩ := hn
  obtain ⟨z, haz, hz⟩ := first_step hc hya.symm
  exact ⟨z, haz, fun h => hy (h.trans hz)⟩

private lemma unique_far [Finite V] (hc : G.Connected) {r : ℕ}
    (hR : r ≤ G.radius.toNat) {v : V}
    (hdel : (G.induce ({v}ᶜ : Set V)).radius.toNat < r)
    (hd : (G.induce ({v}ᶜ : Set V)).Connected) :
    ∃ c, G.dist c v = r ∧ ∀ x, x ≠ v → G.dist c x < r := by
  let K := G.induce ({v}ᶜ : Set V)
  let := hd.nonempty
  obtain ⟨c, hcent⟩ := K.exists_eccent_eq_radius
  have hnear (x : V) (hx : x ≠ v) : G.dist c x < r := by
    let x' : ({v}ᶜ : Set V) := ⟨x, hx⟩
    let e := (SimpleGraph.Embedding.induce (G := G) ({v}ᶜ : Set V)).toHom
    have h := (edist_hom_le e c x').trans (K.edist_le_eccent (u := c) (v := x'))
    rw [hcent] at h
    have hfin := K.radius_ne_top_iff.mpr hd
    have := ENat.toNat_le_toNat h hfin
    exact this.trans_lt hdel
  obtain ⟨y, hy⟩ := far_vertex hc hR (c : V)
  have hyv : y = v := by by_contra hn; exact (Nat.not_lt_of_ge hy) (hnear y hn)
  subst y
  have hvc : v ≠ (c : V) := (show (c : V) ≠ v from c.property).symm
  obtain ⟨p, hp⟩ := hc.exists_walk_length_eq_dist (c : V) v
  have hprefix := geo_dist hc p hp (i := p.length - 1) (by omega)
  have hprev : p.getVert (p.length - 1) ≠ v := by
    intro he
    rw [he] at hprefix
    omega
  have := hnear _ hprev
  exact ⟨c, by omega, hnear⟩

private lemma avoid_of_dist_le (hc : G.Connected) {a x y : V} (hya : y ≠ a)
    (h : G.dist x y ≤ G.dist x a) : Avoid G a x y := by
  by_contra hn
  have := dist_through hc hn
  have := hc.pos_dist_of_ne hya.symm
  omega

private lemma farthest_deletable [Finite V] (hc : G.Connected) {r : ℕ}
    (hr : 0 < r) (hR : r ≤ G.radius.toNat) (l : V) :
    ∃ v, v ≠ l ∧ (G.induce ({v}ᶜ : Set V)).Connected := by
  obtain ⟨v, hv⟩ := G.exists_edist_eq_eccent_of_finite l
  have hm (x : V) : G.dist l x ≤ G.dist l v := by
    have he : G.edist l x ≤ G.edist l v := hv ▸ G.edist_le_eccent
    simpa [← (hc l x).coe_dist_eq_edist, ← (hc l v).coe_dist_eq_edist] using
      ENat.toNat_le_toNat he (edist_ne_top_iff_reachable.mpr (hc l v))
  obtain ⟨w, hw⟩ := far_vertex hc hR l
  have hp : 0 < G.dist l v := hr.trans_le (hw.trans (hm w))
  have hne : l ≠ v := by intro h; simp [h] at hp
  exact ⟨v, hne.symm, (connected_delete_iff hne).2 fun x hx =>
    avoid_of_dist_le hc hx (hm x)⟩

private lemma two_neighbors_of_delete [Finite V] (hc : G.Connected) {r : ℕ}
    (hr : 2 ≤ r) (hR : r ≤ G.radius.toNat) {x y : V} (hxy : G.Adj x y)
    (hd : (G.induce ({x}ᶜ : Set V)).Connected) :
    ∃ z, G.Adj y z ∧ z ≠ x := by
  obtain ⟨w, hw⟩ := far_vertex hc hR x
  have h₁ : G.dist x y = 1 := dist_eq_one_iff_adj.mpr hxy
  have h₂ : G.dist x x = 0 := dist_self
  have hwx : w ≠ x := by intro h; rw [h, h₂] at hw; omega
  have hyw : y ≠ w := by intro h; rw [← h, h₁] at hw; omega
  obtain ⟨p, hp⟩ := (connected_delete_iff hxy.ne.symm).1 hd w hwx
  exact ⟨p.getVert 1, p.adj_snd (Walk.not_nil_of_ne hyw),
    fun he => hp (he ▸ p.getVert_mem_support 1)⟩

/-- Fajtlowicz's propagation argument from A characterization of radius-critical
graphs. If deleting a vertex with at least two neighbors drops the radius below
the threshold, each of its neighbors can also be deleted while preserving
connectivity. -/
private lemma delete_neighbor [Finite V] (hc : G.Connected) {r : ℕ}
    (hr : 2 ≤ r) (hR : r ≤ G.radius.toNat) {v a b : V}
    (ha : G.Adj v a) (hb : G.Adj v b) (hab : a ≠ b)
    (hd : (G.induce ({v}ᶜ : Set V)).Connected)
    (hdel : (G.induce ({v}ᶜ : Set V)).radius.toNat < r) :
    (G.induce ({a}ᶜ : Set V)).Connected := by
  obtain ⟨c, hcv, hnear⟩ := unique_far hc hR hdel hd
  have hn (z : V) (hz : G.Adj v z) : G.dist c z = r - 1 := by
    have ht := hc.dist_triangle (u := c) (v := z) (w := v)
    rw [hcv, dist_eq_one_iff_adj.mpr hz.symm] at ht
    have := hnear z hz.ne.symm
    omega
  have hca : c ≠ a := by
    intro h
    have := hn a ha
    rw [← h, dist_self] at this
    omega
  have hs (z : V) (hz : z ≠ v) (hza : z ≠ a) : Avoid G a c z :=
    avoid_of_dist_le hc hza (by have := hnear z hz; rw [hn a ha]; omega)
  apply (connected_delete_iff hca).2
  intro z hza
  by_cases hz : z = v
  · subst z
    exact (hs b hb.ne.symm hab.symm).trans (Avoid.adj hb.symm hab.symm ha.ne)
  · exact hs z hz hza

private lemma nonleaf_is_cut [Finite V] (hc : G.Connected) {r : ℕ}
    (hr : 2 ≤ r) (hR : r ≤ G.radius.toNat) {l b : V}
    (huniq : ∀ z, G.Adj l z → z = b)
    (crit : ∀ v, v ≠ l → (G.induce ({v}ᶜ : Set V)).Connected →
      (G.induce ({v}ᶜ : Set V)).radius.toNat < r)
    {v a z : V} (ha : G.Adj v a) (hz : G.Adj v z) (haz : a ≠ z) :
    ¬(G.induce ({v}ᶜ : Set V)).Connected := by
  let bad (x : V) := (G.induce ({x}ᶜ : Set V)).Connected ∧
    ∃ a z, G.Adj x a ∧ G.Adj x z ∧ a ≠ z
  have hn : ¬bad l := by
    rintro ⟨_, a, z, ha, hz, hn⟩
    exact hn ((huniq a ha).trans (huniq z hz).symm)
  have hstep (x y : V) (hxy : G.Adj x y) (hx : bad x) : bad y := by
    have hxl : x ≠ l := fun h => hn (h ▸ hx)
    obtain ⟨hd, a, z, ha, hz, haz⟩ := hx
    have hdy : (G.induce ({y}ᶜ : Set V)).Connected := by
      by_cases hya : y = a
      · exact delete_neighbor hc hr hR hxy hz (hya.trans_ne haz) hd (crit x hxl hd)
      · exact delete_neighbor hc hr hR hxy ha hya hd (crit x hxl hd)
    obtain ⟨t, hyt, htx⟩ := two_neighbors_of_delete hc hr hR hxy hd
    exact ⟨hdy, x, t, hxy.symm, hyt, htx.symm⟩
  have hp {x y : V} (p : G.Walk x y) : bad x → bad y := by
    induction p with
    | nil => exact id
    | cons h _ ih => exact fun hx => ih (hstep _ _ h hx)
  intro hd
  exact hn (hp (hc v l).some ⟨hd, a, z, ha, hz, haz⟩)

private lemma geo_segment_le {u v : V} (p : G.Walk u v) {i j : ℕ} (hij : i ≤ j) :
    G.dist (p.getVert i) (p.getVert j) ≤ j - i := by
  have h := dist_le ((p.drop i).take (j - i))
  rw [Walk.take_length, Walk.drop_getVert, Nat.add_sub_of_le hij] at h
  exact h.trans inf_le_left

private lemma geo_getVert_adj (hc : G.Connected) {u v : V} (p : G.Walk u v)
    (hp : p.length = G.dist u v) {i j : ℕ} (hi : i ≤ p.length) (hj : j ≤ p.length)
    (h : G.Adj (p.getVert i) (p.getVert j)) : i ≤ j + 1 ∧ j ≤ i + 1 := by
  have h₁ := hc.dist_triangle (u := u) (v := p.getVert j) (w := p.getVert i)
  have h₂ := hc.dist_triangle (u := u) (v := p.getVert i) (w := p.getVert j)
  rw [geo_dist hc p hp hi, geo_dist hc p hp hj, dist_eq_one_iff_adj.mpr h.symm] at h₁
  rw [geo_dist hc p hp hi, geo_dist hc p hp hj, dist_eq_one_iff_adj.mpr h] at h₂
  exact ⟨h₁, h₂⟩

private lemma geo_tree [DecidableEq V] {u v : V} (p : G.Walk u v)
    (hp : p.length = G.dist u v) :
    (G.induce (p.support.toFinset : Set V)).IsTree ∧ p.support.toFinset.card = p.length + 1 :=
  ⟨p.induce_support_isTree_of_length_eq_dist hp, by
    rw [List.toFinset_card_of_nodup (p.isPath_of_length_eq_dist hp).support_nodup, Walk.length_support]⟩

/-- Attach the positive-index vertices of a geodesic to a tree, one at a time. -/
private lemma extend_by_geodesic [DecidableEq V] (hc : G.Connected) {c w : V}
    (q : G.Walk c w) (hq : q.length = G.dist c w) {s : Finset V}
    (hs : (G.induce (s : Set V)).IsTree) {a : V} (ha : a ∈ s)
    (hfirst : G.Adj (q.getVert 1) a)
    (hdisj : ∀ i, 0 < i → i ≤ q.length → q.getVert i ∉ s)
    (honly : ∀ i, 0 < i → i ≤ q.length → ∀ x ∈ s,
      G.Adj (q.getVert i) x → i = 1 ∧ x = a) :
    ∃ t : Finset V, (G.induce (t : Set V)).IsTree ∧ s ⊆ t ∧
      t.card = s.card + q.length ∧ ∀ x ∈ t, x ∈ s ∨ x ∈ q.support := by
  have h (n : ℕ) (hn : n ≤ q.length) :
      ∃ t : Finset V, (G.induce (t : Set V)).IsTree ∧ t.card = s.card + n ∧
        ∀ x, x ∈ t ↔ x ∈ s ∨ ∃ i, 0 < i ∧ i ≤ n ∧ q.getVert i = x := by
    induction n with
    | zero =>
      exact ⟨s, hs, by simp, fun x => by simp⟩
    | succ n ih =>
      obtain ⟨t, ht, hcard, hmem⟩ := ih (by omega)
      let z := q.getVert (n + 1)
      have hnew : z ∉ t := by
        intro hz
        rcases (hmem z).1 hz with hzs | ⟨i, hi, hin, he⟩
        · exact hdisj _ (by omega) hn hzs
        · have h₁ := geo_dist hc q hq (i := i) (by omega)
          have h₂ := geo_dist hc q hq hn
          change q.getVert i = q.getVert (n + 1) at he
          rw [he, h₂] at h₁
          omega
      have hparent : ∃ y ∈ t, G.Adj z y ∧ ∀ x ∈ t, G.Adj z x → x = y := by
        cases n with
        | zero =>
          refine ⟨a, (hmem a).2 (Or.inl ha), hfirst, ?_⟩
          intro x hx hzx
          rcases (hmem x).1 hx with hxs | ⟨i, hi, hin, _⟩
          · exact (honly 1 (by omega) hn x hxs hzx).2
          · omega
        | succ n =>
          refine ⟨q.getVert (n + 1), (hmem _).2 (Or.inr ⟨n + 1, by omega, le_rfl, rfl⟩),
            (q.adj_getVert_succ (i := n + 1) (by omega)).symm, ?_⟩
          intro x hx hzx
          rcases (hmem x).1 hx with hxs | ⟨i, hi, hin, rfl⟩
          · have he := (honly (n + 1 + 1) (by omega) hn x hxs hzx).1
            omega
          · have he := (geo_getVert_adj hc q hq hn (by omega) hzx).1
            congr 1
            omega
      obtain ⟨y, hy, hzy, hu⟩ := hparent
      refine ⟨insert z t, ht.induce_insert_of_unique_adj hnew hy hzy hu,
        by rw [Finset.card_insert_of_notMem hnew, hcard]; omega, ?_⟩
      intro x
      rw [Finset.mem_insert, hmem]
      constructor
      · rintro (rfl | hx | ⟨i, hi, hin, rfl⟩)
        · exact Or.inr ⟨n + 1, by omega, le_rfl, rfl⟩
        · exact Or.inl hx
        · exact Or.inr ⟨i, hi, by omega, rfl⟩
      · rintro (hx | ⟨i, hi, hin, rfl⟩)
        · exact Or.inr (Or.inl hx)
        · by_cases he : i = n + 1
          · exact Or.inl (by simp [z, he])
          · exact Or.inr (Or.inr ⟨i, hi, by omega, rfl⟩)
  obtain ⟨t, ht, hcard, hmem⟩ := h q.length le_rfl
  refine ⟨t, ht, fun x hx => (hmem x).2 (Or.inl hx), hcard, ?_⟩
  intro x hx
  rcases (hmem x).1 hx with hx | ⟨i, _, _, rfl⟩
  · exact Or.inl hx
  · exact Or.inr (q.getVert_mem_support i)

/-- The cut-vertex case of Chung's two-geodesic argument, as presented in
Erdős, Saks and Sós, Maximum induced trees in graphs, Theorem 2.2. -/
private lemma tree_at_cut [Finite V] [DecidableEq V] (hc : G.Connected) {r : ℕ}
    (hr : 2 ≤ r) (hR : r ≤ G.radius.toNat) {c v : V} (hcv : G.dist c v = r)
    (hnear : ∀ x, x ≠ v → G.dist c x < r) (p : G.Walk c v)
    (hp : p.length = G.dist c v)
    (hcut : ¬(G.induce ({p.getVert 1}ᶜ : Set V)).Connected) :
    ∃ t : Finset V, (G.induce (t : Set V)).IsTree ∧ 2 * r ≤ t.card := by
  let a := p.getVert 1
  let b := p.getVert 2
  have hca : G.dist c a = 1 := geo_dist hc p hp (by omega)
  have hav : G.dist a v = r - 1 := by
    have h := geo_dist_end hc p hp (i := 1) (by omega)
    simpa [a, hp, hcv] using h
  have hcb : G.dist c b = 2 := geo_dist hc p hp (by omega)
  have hab : G.Adj a b := p.adj_getVert_succ (by omega)
  have hba : G.dist b a = 1 := dist_eq_one_iff_adj.mpr hab.symm
  have hadj : G.Adj c a := dist_eq_one_iff_adj.mp hca
  have hav' : a ≠ v := fun h => by rw [h, dist_self] at hav; omega
  by_cases hside : Avoid G a c v
  · -- The two geodesics stay on the center's side except for the cut vertex itself.
    obtain ⟨z, haz, hz⟩ := off_neighbor hc hadj.ne hcut
    have hzv : z ≠ v := fun h => hz (h ▸ hside)
    have hcz : G.dist c z = 2 := by
      rw [dist_through hc hz, hca, dist_eq_one_iff_adj.mpr haz]
    have hr₃ : 3 ≤ r := by have := hnear z hzv; omega
    obtain ⟨w, hw⟩ := far_vertex hc hR b
    have hwv : w ≠ v := by
      intro h
      have hbv := geo_dist_end hc p hp (i := 2) (by omega)
      rw [h] at hw
      change r ≤ G.dist (p.getVert 2) v at hw
      omega
    obtain ⟨q, hq⟩ := hc.exists_walk_length_eq_dist c w
    have hq_lt : q.length < r := hq ▸ hnear w hwv
    have hq_ge : r ≤ q.length + 2 := by
      have h := hc.dist_triangle (u := b) (v := c) (w := w)
      rw [G.dist_comm (u := b) (v := c), hcb, ← hq] at h
      omega
    have hq_pos : 0 < q.length := by omega
    have hqa : a ∉ q.support := by
      intro h
      obtain ⟨i, hi, hil⟩ := Walk.mem_support_iff_exists_getVert.mp h
      have h₁ := geo_dist hc q hq hil
      have h₂ := geo_dist_end hc q hq hil
      rw [hi, hca] at h₁
      rw [hi] at h₂
      have h₃ := hc.dist_triangle (u := b) (v := a) (w := w)
      omega
    have hqside (i : ℕ) : Avoid G a c (q.getVert i) := by
      refine ⟨q.take i, ?_⟩
      rw [Walk.support_take]
      exact fun h => hqa (List.mem_of_mem_take h)
    have hpside (i : ℕ) (hi : i ≤ p.length) (hi₁ : i ≠ 1) :
        Avoid G a c (p.getVert i) := by
      by_cases hi₀ : i = 0
      · subst i
        simpa using (show Avoid G a c c from ⟨Walk.nil, by simp [hadj.ne.symm]⟩)
      have h₁ := geo_dist_end hc p hp hi
      have h₂ : G.dist v (p.getVert i) < G.dist v a := by
        rw [G.dist_comm (u := v) (v := p.getVert i), G.dist_comm (u := v) (v := a), h₁, hav]
        omega
      exact hside.trans (avoid_of_dist_lt hc h₂)
    have hcross (i j : ℕ) (hi : i ≤ p.length) (hj : j ≤ q.length)
        (hij : G.Adj (p.getVert i) (q.getVert j)) : i ≤ 1 ∧ (i = 1 → j ≤ 1) := by
      have h₁ := hc.dist_triangle (u := c) (v := q.getVert j) (w := p.getVert i)
      rw [geo_dist hc p hp hi, geo_dist hc q hq hj, dist_eq_one_iff_adj.mpr hij.symm] at h₁
      have h₂ := hc.dist_triangle (u := b) (v := p.getVert i) (w := w)
      have h₃ := hc.dist_triangle (u := p.getVert i) (v := q.getVert j) (w := w)
      rw [dist_eq_one_iff_adj.mpr hij, geo_dist_end hc q hq hj] at h₃
      constructor
      · by_contra hn
        have hseg := geo_segment_le p (i := 2) (j := i) (by omega)
        change G.dist b (p.getVert i) ≤ i - 2 at hseg
        omega
      · intro hei
        subst i
        change G.dist b w ≤ G.dist b a + G.dist a w at h₂
        change G.dist a w ≤ 1 + (q.length - j) at h₃
        omega
    have hdisj (i j : ℕ) (hi : i ≤ p.length) (hj : j ≤ q.length) (hj₀ : 0 < j) :
        p.getVert i ≠ q.getVert j := by
      intro he
      have h₁ := geo_dist hc p hp hi
      have h₂ := geo_dist hc q hq hj
      rw [he, h₂] at h₁
      subst i
      rcases eq_or_ne j 1 with rfl | hn
      · apply hqa
        change p.getVert 1 ∈ q.support
        rw [he]
        exact q.getVert_mem_support 1
      · have h := q.adj_getVert_succ (i := j - 1) (by omega)
        rw [Nat.sub_add_cancel (by omega : 1 ≤ j), ← he] at h
        have := (hcross j (j - 1) hi (by omega) h.symm).1
        omega
    classical
    -- If the first vertices are adjacent, replace the turn through the center by that edge.
    let d := if G.Adj a (q.getVert 1) then 1 else 0
    have hd : d ≤ 1 := by dsimp [d]; split <;> omega
    let s := (p.drop d).support.toFinset
    have hsdist : (p.drop d).length = G.dist (p.getVert d) v := by
      rw [Walk.drop_length, geo_dist_end hc p hp (by omega : d ≤ p.length)]
    obtain ⟨hst, hscard⟩ := geo_tree (p.drop d) hsdist
    change s.card = (p.drop d).length + 1 at hscard
    rw [Walk.drop_length] at hscard
    have hsmem (x : V) (hx : x ∈ s) :
        ∃ i, d ≤ i ∧ i ≤ p.length ∧ p.getVert i = x := by
      have hx' : x ∈ (p.drop d).support := List.mem_toFinset.mp hx
      obtain ⟨i, he, hi⟩ := Walk.mem_support_iff_exists_getVert.mp hx'
      rw [Walk.drop_getVert] at he
      rw [Walk.drop_length] at hi
      exact ⟨d + i, by omega, by omega, he⟩
    have hamem : a ∈ s := by
      apply List.mem_toFinset.mpr
      have h := (p.drop d).getVert_mem_support (1 - d)
      rw [Walk.drop_getVert, Nat.add_sub_of_le hd] at h
      exact h
    have hfirst : G.Adj (q.getVert 1) (p.getVert d) := by
      by_cases he : G.Adj a (q.getVert 1)
      · simpa [d, he, a] using he.symm
      · simpa [d, he] using (q.adj_snd (Walk.not_nil_iff_lt_length.mpr hq_pos)).symm
    have hunique (j : ℕ) (hj₀ : 0 < j) (hj : j ≤ q.length) (x : V) (hx : x ∈ s)
        (he : G.Adj (q.getVert j) x) : j = 1 ∧ x = p.getVert d := by
      obtain ⟨i, hdi, hi, rfl⟩ := hsmem x hx
      have ⟨hi₁, hj₁⟩ := hcross i j hi hj he.symm
      rcases eq_or_ne i 1 with rfl | hn
      · have hj_eq : j = 1 := by have := hj₁ rfl; omega
        subst j
        have hd₁ : d = 1 := if_pos he.symm
        exact ⟨rfl, by rw [hd₁]⟩
      · have hi₀ : i = 0 := by omega
        subst i
        have hd₀ : d = 0 := by omega
        have hdist := dist_eq_one_iff_adj.mpr he.symm
        rw [Walk.getVert_zero, geo_dist hc q hq hj] at hdist
        exact ⟨hdist, by rw [hd₀]⟩
    obtain ⟨t, ht, hst', hcard, htmem⟩ :=
      extend_by_geodesic hc q hq hst (List.mem_toFinset.mpr (p.drop d).start_mem_support)
        hfirst (fun j hj₀ hj h => by
          obtain ⟨i, _, hi, he⟩ := hsmem _ h
          exact hdisj i j hi hj hj₀ he) hunique
    have htside (x : V) (hx : x ∈ t) (hxa : x ≠ a) : Avoid G a c x := by
      rcases htmem x hx with hs' | hq'
      · obtain ⟨i, _, hi, rfl⟩ := hsmem x hs'
        exact hpside i hi (fun h => hxa (h ▸ rfl))
      · obtain ⟨i, rfl, _⟩ := Walk.mem_support_iff_exists_getVert.mp hq'
        exact hqside i
    have hzt : z ∉ t := fun h => hz (htside z h haz.ne.symm)
    have htnew := ht.induce_insert_of_unique_adj hzt (hst' hamem) haz.symm
      (fun {x} hx hzx => by
        by_contra hxa
        exact hz ((htside x hx hxa).trans (Avoid.adj hzx.symm hxa haz.ne.symm)))
    refine ⟨insert z t, htnew, ?_⟩
    rw [Finset.card_insert_of_notMem hzt, hcard, hscard]
    by_cases he : G.Adj a (q.getVert 1)
    · have hd₁ : d = 1 := if_pos he
      have ht₁ := hc.dist_triangle (u := b) (v := a) (w := w)
      have ht₂ := hc.dist_triangle (u := a) (v := q.getVert 1) (w := w)
      rw [dist_eq_one_iff_adj.mpr he, geo_dist_end hc q hq (by omega : 1 ≤ q.length)] at ht₂
      omega
    · have hd₀ : d = 0 := if_neg he
      omega
  · -- Every path from the far vertex to the center's side goes through the cut vertex.
    obtain ⟨w, hw⟩ := far_vertex hc hR a
    have hwv : w ≠ v := by intro he; rw [he, hav] at hw; omega
    have hcw : Avoid G a c w := by
      by_contra hn
      have := dist_through hc hn
      have := hnear w hwv
      omega
    have hnvw : ¬Avoid G a v w := fun h => hside (hcw.trans h.symm)
    obtain ⟨q, hq⟩ := hc.exists_walk_length_eq_dist v w
    obtain ⟨ht, hcard⟩ := geo_tree q hq
    refine ⟨q.support.toFinset, ht, ?_⟩
    rw [hcard]
    have hlen := dist_through hc hnvw
    rw [G.dist_comm (u := v) (v := a), hav] at hlen
    omega

private def eraseIso [DecidableEq V] {s : Finset V} (x : (s : Set V)) :
    (G.induce (s : Set V)).induce ({x}ᶜ : Set (s : Set V)) ≃g
      G.induce (s.erase (x : V) : Set V) where
  toFun y := ⟨y.val.val, Finset.mem_erase.mpr
    ⟨fun he => y.property (Set.mem_singleton_iff.mpr (Subtype.ext he)), y.val.property⟩⟩
  invFun y := ⟨⟨y.val, (Finset.mem_erase.mp y.property).2⟩, fun he =>
    (Finset.mem_erase.mp y.property).1 (congrArg Subtype.val (Set.mem_singleton_iff.mp he))⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

private lemma lift_tree [Fintype V] [DecidableEq V] {s : Finset V}
    {t : Finset (s : Set V)} (ht : ((G.induce (s : Set V)).induce (t : Set (s : Set V))).IsTree) :
    t.card ≤ largestInducedTreeSize G := by
  let e : (s : Set V) ↪ V := ⟨Subtype.val, Subtype.val_injective⟩
  let u := t.map e
  have hmem (x : (s : Set V)) : (x : V) ∈ u ↔ x ∈ t := by simp [u, e]
  let i : (G.induce (s : Set V)).induce (t : Set (s : Set V)) ≃g G.induce (u : Set V) :=
    { toFun := fun x => ⟨x.val.val, (hmem x.val).2 x.property⟩
      invFun := fun y => by
        have hys : (y : V) ∈ s := by
          obtain ⟨v, _, hv⟩ := Finset.mem_map.1 y.property
          change (v : V) = y.val at hv
          exact hv ▸ v.property
        exact ⟨⟨y.val, hys⟩, (hmem ⟨y.val, hys⟩).1 y.property⟩
      left_inv := fun x => rfl
      right_inv := fun y => rfl
      map_rel_iff' := Iff.rfl }
  have hu := card_le_largestInducedTreeSize (i.isTree_iff.mp ht)
  simpa [u] using hu

private lemma leaf_radius_tree [Fintype V] [DecidableEq V] (hc : G.Connected)
    {l b : V} (hl : G.Adj l b) (huniq : ∀ z, G.Adj l z → z = b) :
    2 * G.radius.toNat ≤ largestInducedTreeSize G := by
  classical
  let r := G.radius.toNat
  by_cases hr : 2 ≤ r
  · let P (s : Finset V) := l ∈ s ∧ b ∈ s ∧ (G.induce (s : Set V)).Connected ∧
      r ≤ (G.induce (s : Set V)).radius.toNat
    have hP : P Finset.univ := by
      let i : G.induce ((Finset.univ : Finset V) : Set V) ≃g G :=
        { toFun := Subtype.val
          invFun := fun x => ⟨x, Finset.mem_univ x⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl
          map_rel_iff' := Iff.rfl }
      refine ⟨Finset.mem_univ _, Finset.mem_univ _, i.connected_iff.mpr hc, ?_⟩
      show r ≤ (G.induce ((Finset.univ : Finset V) : Set V)).radius.toNat
      rw [← radius_iso i]
    have hex : ∃ n, ∃ s : Finset V, P s ∧ s.card = n :=
      ⟨_, Finset.univ, hP, rfl⟩
    obtain ⟨s, hs, hs_card⟩ := Nat.find_spec hex
    have hminimal (t : Finset V) (ht : P t) : s.card ≤ t.card := by
      rw [hs_card]
      exact Nat.find_min' hex ⟨t, ht, rfl⟩
    obtain ⟨hls, hbs, hH, hR⟩ := hs
    let H := G.induce (s : Set V)
    let l' : (s : Set V) := ⟨l, hls⟩
    let b' : (s : Set V) := ⟨b, hbs⟩
    have hl' : H.Adj l' b' := hl
    have hu' (z : (s : Set V)) (h : H.Adj l' z) : z = b' :=
      Subtype.ext (huniq _ h)
    have hcrit (v : (s : Set V)) (hv : v ≠ l')
        (hd : (H.induce ({v}ᶜ : Set (s : Set V))).Connected) :
        (H.induce ({v}ᶜ : Set (s : Set V))).radius.toNat < r := by
      have hvb : v ≠ b' := by
        intro he
        subst v
        obtain ⟨z, hz, hzne⟩ := two_neighbors_of_delete hH hr hR hl'.symm hd
        exact hzne (hu' z hz)
      let i := eraseIso (G := G) v
      by_contra hn
      have ht : P (s.erase (v : V)) := by
        refine ⟨Finset.mem_erase.mpr ⟨fun h => hv (Subtype.ext h.symm), hls⟩,
          Finset.mem_erase.mpr ⟨fun h => hvb (Subtype.ext h.symm), hbs⟩,
          i.connected_iff.mp hd, ?_⟩
        rw [radius_iso i]
        exact Nat.le_of_not_gt hn
      exact (Nat.not_le_of_gt (Finset.card_erase_lt_of_mem v.property)) (hminimal _ ht)
    obtain ⟨v, hv, hd⟩ := farthest_deletable hH (by omega) hR l'
    obtain ⟨c, hcv, hnear⟩ := unique_far hH hR (hcrit v hv hd) hd
    obtain ⟨p, hp⟩ := hH.exists_walk_length_eq_dist c v
    have hca : H.Adj c (p.getVert 1) :=
      p.adj_snd (Walk.not_nil_iff_lt_length.mpr (by omega))
    have hab := p.adj_getVert_succ (i := 1) (by omega)
    have hcb : c ≠ p.getVert 2 := by
      intro h
      have hh := geo_dist hH p hp (i := 2) (by omega)
      rw [← h, SimpleGraph.dist_self] at hh
      omega
    have hcut := nonleaf_is_cut hH hr hR hu' hcrit hca.symm hab hcb
    obtain ⟨t, ht, hcard⟩ := tree_at_cut hH hr hR hcv hnear p hp hcut
    exact hcard.trans (lift_tree ht)
  · obtain ⟨s, hls, hbs, hs⟩ := hc.exists_induced_tree_containing_pair l b
    have h₂ : 2 ≤ s.card := by
      have hsub : ({l, b} : Finset V) ⊆ s := by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact hls
        · exact hbs
      have hh := Finset.card_le_card hsub
      simpa [hl.ne] using hh
    exact (show 2 * r ≤ 2 by omega).trans (h₂.trans (card_le_largestInducedTreeSize hs))

end OMA.W84H1

open SimpleGraph in
-- Credit: @MrSeizy
theorem OMA.solution : OMA.R_WrittenOnTheWallII_GraphConjecture84_conjecture84_R1.H1 := by
  intro V _ _ _ G _ hc _ hmin
  obtain ⟨l, hl⟩ := G.exists_minimal_degree_vertex
  have hcard : (G.neighborFinset l).card = 1 := by
    rw [card_neighborFinset_eq_degree, ← hl, hmin]
  obtain ⟨b, hb⟩ := Finset.card_eq_one.mp hcard
  have hh : ∀ z, G.Adj l z ↔ z = b := by
    intro z
    rw [← G.mem_neighborFinset l, hb, Finset.mem_singleton]
  have htree := OMA.W84H1.leaf_radius_tree hc ((hh b).2 rfl) (fun z => (hh z).1)
  rw [hmin, Nat.cast_one, div_one]
  exact_mod_cast htree
