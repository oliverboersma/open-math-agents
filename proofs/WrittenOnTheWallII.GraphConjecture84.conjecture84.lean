import FormalConjectures.WrittenOnTheWallII.GraphConjecture84

-- Port of the public proof by Yixing Zhang, based on the proof of Jonas J. Gebendorfer.
-- https://github.com/ProblemHunter/wowii84-lean/tree/722b098bafb5 (Apache-2.0).

/-!
# Written on the Wall II, Conjecture 84: the proof

Lean formalization of the proof of WOWII Conjecture 84 given by Jonas J. Gebendorfer,
*Induced trees in graphs with a cut vertex: A proof of Written on the Wall II, Conjecture 84*
(manuscript, 28 October 2026; posted at google-deepmind/formal-conjectures issue #7663).

Outline (following the manuscript):
* `δ(G) ≥ 2`: a diametral geodesic is an induced path on `rad(G) + 1` vertices, which
  already gives `δ(G) · tree(G) ≥ 2 rad(G)`.
* `δ(G) = 1`: the neighbour of a leaf is a cut vertex (except for small cases checked
  directly), and `two_mul_radius_le_largestInducedTreeSize_of_cut_vertex` proves the
  stronger bound `tree(G) ≥ 2 rad(G)` for every connected graph with a cut vertex
  (Gebendorfer, Theorem 1), by a minimal-counterexample argument: reduction to a
  2-connected core with pendant paths, radius-drop witnesses, equal pendant lengths,
  and Chung's bound (Erdős–Saks–Sós 1986, Theorem 2.2), of which the induced-tree
  consequence `tree(H) ≥ 2 rad(H) - 1` is proved here (`chung_induced_tree_bound`).

The main theorem `conjecture84_proof` has exactly the statement of
`WrittenOnTheWallII.GraphConjecture84.conjecture84` in formal-conjectures
(commit d995ef5d306637c0a2e489c7e579647168d7df2f); see `Challenge.lean`.
-/

namespace WrittenOnTheWallII.GraphConjecture84

open SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α]


/-- The vertices of a geodesic form an induced tree of distance plus one vertices. -/
lemma dist_add_one_le_largestInducedTreeSize {G : SimpleGraph α} {u v : α}
    (h : G.Reachable u v) : G.dist u v + 1 ≤ largestInducedTreeSize G := by
  obtain ⟨p, hp, hlen⟩ := h.exists_path_of_dist
  have hcard : p.support.toFinset.card = G.dist u v + 1 := by
    rw [List.toFinset_card_of_nodup hp.support_nodup, p.length_support, hlen]
  rw [← hcard]
  exact card_le_largestInducedTreeSize (p.induce_support_isTree_of_length_eq_dist hlen)

/-- Radius is attained by a distance in a finite connected graph. -/
lemma radius_add_one_le_largestInducedTreeSize {G : SimpleGraph α}
    [Nonempty α] (h : G.Connected) :
    G.radius.toNat + 1 ≤ largestInducedTreeSize G := by
  obtain ⟨u, v, huv⟩ := G.exists_edist_eq_radius_of_finite
  have hd : G.dist u v = G.radius.toNat := congrArg ENat.toNat huv
  rw [← hd]
  exact dist_add_one_le_largestInducedTreeSize (h u v)

/-- An induced tree cannot use more vertices than the ambient graph. -/
lemma largestInducedTreeSize_le_card (G : SimpleGraph α) :
    largestInducedTreeSize G ≤ Fintype.card α := by
  apply csSup_le'
  rintro n ⟨s, rfl, _⟩
  exact Finset.card_le_univ s

/-- An induced graph embedding transports induced trees without changing their order. -/
lemma largestInducedTreeSize_le_of_embedding {β : Type*} [Fintype β] [DecidableEq β]
    {H : SimpleGraph β} {G : SimpleGraph α} (e : H ↪g G) :
    largestInducedTreeSize H ≤ largestInducedTreeSize G := by
  classical
  apply csSup_le'
  rintro n ⟨s, rfl, hs⟩
  let f : ↥(s : Set β) → ↥(s.map e.toEmbedding : Set α) := fun x =>
    ⟨e x, Finset.mem_map.mpr ⟨x, x.property, rfl⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · intro x y hxy
      apply Subtype.ext
      exact e.injective (congrArg Subtype.val hxy)
    · intro y
      obtain ⟨x, hx, hxy⟩ := Finset.mem_map.mp y.property
      exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  let i : H.induce (s : Set β) ≃g G.induce (s.map e.toEmbedding : Set α) :=
    { Equiv.ofBijective f hf with
      map_rel_iff' := by intro x y; exact e.map_rel_iff }
  have htree := i.isTree_iff.mp hs
  simpa only [Finset.card_map] using card_le_largestInducedTreeSize htree

/-- Passing to an induced subgraph can only decrease the largest induced-tree order. -/
lemma largestInducedTreeSize_induce_le (G : SimpleGraph α) (S : Set α)
    [DecidablePred (· ∈ S)] :
    largestInducedTreeSize (G.induce S) ≤ largestInducedTreeSize G :=
  largestInducedTreeSize_le_of_embedding (SimpleGraph.Embedding.induce S)

/-- In order at least three, the neighbor of a leaf is a vertex cut. -/
lemma exists_cut_vertex_of_minDegree_eq_one {G : SimpleGraph α} [DecidableRel G.Adj]
    [Nonempty α] (hδ : G.minDegree = 1) (hcard : 3 ≤ Fintype.card α) :
    ∃ v, ¬ (G.induce ({v}ᶜ : Set α)).Connected := by
  classical
  obtain ⟨u, hu⟩ := G.exists_minimal_degree_vertex
  have hdu : G.degree u = 1 := hu.symm.trans hδ
  obtain ⟨v, huv, huniq⟩ := degree_eq_one_iff_existsUnique_adj.mp hdu
  have hw : ∃ w : α, w ≠ u ∧ w ≠ v := by
    by_contra! hn
    have hsub : (Finset.univ : Finset α) ⊆ {u, v} := by
      intro w _
      by_cases hwu : w = u
      · simp [hwu]
      · simp [hn w hwu]
    have hle := Finset.card_le_card hsub
    have hpair : ({u, v} : Finset α).card ≤ 2 := Finset.card_le_two
    simp only [Finset.card_univ] at hle
    omega
  obtain ⟨w, hwu, hwv⟩ := hw
  refine ⟨v, ?_⟩
  intro hc
  let u' : ↥({v}ᶜ : Set α) := ⟨u, by simpa using huv.ne⟩
  let w' : ↥({v}ᶜ : Set α) := ⟨w, by simpa using hwv⟩
  obtain ⟨p⟩ := hc u' w'
  have hne : u' ≠ w' := by
    intro heq
    exact hwu (congrArg Subtype.val heq).symm
  have hadj : G.Adj u (p.snd : α) := p.adj_snd (p.not_nil_of_ne hne)
  have heq : (p.snd : α) = v := huniq _ hadj
  have hmem := p.snd.property
  simpa [heq] using hmem

/-- A strict radius decrease on deletion produces a center with a unique farthest vertex. -/
lemma radius_drop_witness {G : SimpleGraph α} (hG : G.Connected) (x : α)
    (hH : (G.induce ({x}ᶜ : Set α)).Connected)
    (hr : 1 ≤ G.radius.toNat)
    (hdrop : (G.induce ({x}ᶜ : Set α)).radius.toNat ≤ G.radius.toNat - 1) :
    ∃ c : α, c ≠ x ∧ G.eccent c = G.radius ∧ G.dist c x = G.radius.toNat ∧
      ∀ z : α, z ≠ x → G.dist c z ≤ G.radius.toNat - 1 := by
  classical
  let H := G.induce ({x}ᶜ : Set α)
  haveI : Nonempty ↥({x}ᶜ : Set α) := hH.nonempty
  haveI : Nonempty α := ⟨x⟩
  obtain ⟨c, hc⟩ := H.exists_eccent_eq_radius
  have hHfin : H.radius ≠ ⊤ := H.radius_ne_top_iff.mpr hH
  have hGfin : G.radius ≠ ⊤ := G.radius_ne_top_iff.mpr hG
  have hother : ∀ z : α, z ≠ x → G.dist c z ≤ G.radius.toNat - 1 := by
    intro z hzx
    let z' : ↥({x}ᶜ : Set α) := ⟨z, by simpa using hzx⟩
    obtain ⟨p, hp⟩ := hH.exists_walk_length_eq_dist c z'
    have hmap : G.dist c z ≤ H.dist c z' := by
      have hm := G.dist_le (p.map (SimpleGraph.Embedding.induce ({x}ᶜ : Set α)).toHom)
      rw [Walk.length_map] at hm
      change G.dist (c : α) z ≤ p.length at hm
      exact hm.trans_eq hp
    have hcenter : H.dist c z' ≤ H.radius.toNat := by
      apply ENat.toNat_le_toNat _ hHfin
      exact hc ▸ (H.edist_le_eccent (u := c) (v := z'))
    exact hmap.trans (hcenter.trans hdrop)
  have hcx : (c : α) ≠ x := by
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using c.property
  obtain ⟨p⟩ := hG x c
  have hp : ¬ p.Nil := p.not_nil_of_ne hcx.symm
  have hxn : G.Adj x p.snd := p.adj_snd hp
  have hnx : p.snd ≠ x := hxn.ne.symm
  have hdistx : G.dist c x ≤ G.radius.toNat := by
    have htri := hG.dist_triangle (u := (c : α)) (v := p.snd) (w := x)
    have hdistn : G.dist p.snd x = 1 := dist_eq_one_iff_adj.mpr hxn.symm
    have hn := hother p.snd hnx
    omega
  have hecc : G.eccent c ≤ (G.radius.toNat : ℕ∞) := by
    rw [G.eccent_le_iff]
    intro z
    rw [← (hG c z).coe_dist_eq_edist]
    apply ENat.natCast_le_natCast.mpr
    exact (show G.dist c z ≤ G.radius.toNat from by
      by_cases hzx : z = x
      · simpa [hzx] using hdistx
      · exact (hother z hzx).trans (Nat.sub_le _ _))
  have heq : G.eccent c = G.radius :=
    le_antisymm (by simpa only [ENat.natCast_toNat hGfin] using hecc) G.radius_le_eccent
  have hdistxeq : G.dist c x = G.radius.toNat := by
    obtain ⟨z, hz⟩ := G.exists_edist_eq_eccent_of_finite (c : α)
    have hdz : G.dist c z = G.radius.toNat := congrArg ENat.toNat (hz.trans heq)
    have hzx : z = x := by
      by_contra hzx
      have := hother z hzx
      omega
    simpa only [hzx] using hdz
  exact ⟨c, hcx, heq, hdistxeq, hother⟩

/-- Distances add at every vertex on a geodesic. -/
lemma dist_add_dist_eq_of_mem_geodesic {G : SimpleGraph α} {u v z : α}
    (p : G.Walk u v) (hp : p.length = G.dist u v) (hz : z ∈ p.support) :
    G.dist u z + G.dist z v = G.dist u v := by
  have htake := length_eq_dist_of_subwalk hp (p.isSubwalk_takeUntil hz)
  have hdrop := length_eq_dist_of_subwalk hp (p.isSubwalk_dropUntil hz)
  have hlen := congrArg Walk.length (p.take_spec hz)
  simpa only [Walk.length_append, htake, hdrop, hp] using hlen

/-- Two disjoint geodesics from a center and its neighbor bound twice the radius by order. -/
lemma two_mul_radius_le_card {G : SimpleGraph α} (hG : G.Connected) :
    2 * G.radius.toNat ≤ Fintype.card α := by
  classical
  haveI : Nonempty α := hG.nonempty
  by_cases hr : G.radius.toNat = 0
  · simp [hr]
  have hfin : G.radius ≠ ⊤ := G.radius_ne_top_iff.mpr hG
  obtain ⟨c, hc⟩ := G.exists_eccent_eq_radius
  have hcenter (z : α) : G.dist c z ≤ G.radius.toNat := by
    exact ENat.toNat_le_toNat (hc ▸ (G.edist_le_eccent (u := c) (v := z))) hfin
  obtain ⟨a, ha⟩ := G.exists_edist_eq_eccent_of_finite c
  have hca : G.dist c a = G.radius.toNat := congrArg ENat.toNat (ha.trans hc)
  obtain ⟨p, hp, hplen⟩ := hG.exists_path_of_dist c a
  cases p with
  | nil => simp only [Walk.length_nil, dist_self] at hplen hca; omega
  | @cons c n a hcn p =>
    have hplen' : p.length = G.dist n a :=
      length_eq_dist_of_subwalk hplen (Walk.isSubwalk_cons p hcn)
    have hpr : p.length + 1 = G.radius.toNat := by
      simpa only [Walk.length_cons, hca] using hplen
    obtain ⟨b, hb⟩ := G.exists_edist_eq_eccent_of_finite n
    have hnb : G.radius.toNat ≤ G.dist n b := by
      apply ENat.toNat_le_toNat (hb ▸ G.radius_le_eccent)
      exact edist_ne_top_iff_reachable.mpr (hG n b)
    obtain ⟨q, hq, hqlen⟩ := hG.exists_path_of_dist c b
    have hdis : Disjoint p.support.toFinset q.support.toFinset := by
      apply Finset.disjoint_left.mpr
      intro z hzp hzq
      have hzp' : z ∈ p.support := by simpa using hzp
      have hzq' : z ∈ q.support := by simpa using hzq
      have hpa := dist_add_dist_eq_of_mem_geodesic p hplen' hzp'
      have hqb := dist_add_dist_eq_of_mem_geodesic q hqlen hzq'
      have htri := hG.dist_triangle (u := c) (v := z) (w := a)
      have hntri := hG.dist_triangle (u := n) (v := z) (w := b)
      have hcb := hcenter b
      omega
    have hp' : p.IsPath := (Walk.cons_isPath_iff hcn p).mp hp |>.1
    have hpcard : p.support.toFinset.card = p.length + 1 := by
      rw [List.toFinset_card_of_nodup hp'.support_nodup, p.length_support]
    have hqcard : q.support.toFinset.card = q.length + 1 := by
      rw [List.toFinset_card_of_nodup hq.support_nodup, q.length_support]
    have htri := hG.dist_triangle (u := n) (v := c) (w := b)
    have hnc : G.dist n c = 1 := dist_eq_one_iff_adj.mpr hcn.symm
    have hcard := Finset.card_le_univ (p.support.toFinset ∪ q.support.toFinset)
    rw [Finset.card_union_of_disjoint hdis, hpcard, hqcard] at hcard
    omega

/-- A tree is itself a largest induced tree. -/
lemma largestInducedTreeSize_eq_card_of_isTree {G : SimpleGraph α} (hG : G.IsTree) :
    largestInducedTreeSize G = Fintype.card α := by
  apply le_antisymm (largestInducedTreeSize_le_card G)
  have ht : (G.induce (↑(Finset.univ : Finset α) : Set α)).IsTree := by
    rw [Finset.coe_univ]
    exact (G.induceUnivIso).isTree_iff.mpr hG
  simpa only [Finset.card_univ] using card_le_largestInducedTreeSize ht

/-- Trees satisfy the required twice-radius bound, including the one-vertex tree. -/
lemma two_mul_radius_le_largestInducedTreeSize_of_isTree {G : SimpleGraph α}
    (hG : G.IsTree) : 2 * G.radius.toNat ≤ largestInducedTreeSize G := by
  rw [largestInducedTreeSize_eq_card_of_isTree hG]
  exact two_mul_radius_le_card hG.connected

/-- A geodesic meeting an induced tree only at its end attaches without creating a cycle
when every edge from the new vertices to the tree ends at that common vertex. -/
lemma induce_union_geodesic_isTree {G : SimpleGraph α} (hG : G.Connected)
    {u v : α} (p : G.Walk u v) (hp : p.length = G.dist u v) (s : Finset α)
    (hs : (G.induce (s : Set α)).IsTree) (hv : v ∈ s)
    (hinter : ∀ z ∈ p.support, z ∈ s → z = v)
    (hcross : ∀ z ∈ p.support, z ≠ v → ∀ w ∈ s, G.Adj z w → w = v) :
    (G.induce ((p.support.toFinset ∪ s : Finset α) : Set α)).IsTree := by
  induction p with
  | @nil u =>
    have hset : (Walk.nil : G.Walk u u).support.toFinset ∪ s = s := by
      ext z
      simp only [Finset.mem_union, List.mem_toFinset, Walk.support_nil, List.mem_singleton]
      exact or_iff_right_of_imp (fun hzu => hzu ▸ hv)
    rw [hset]
    exact hs
  | @cons u n v hun p ih =>
    have hptail : p.length = G.dist n v :=
      length_eq_dist_of_subwalk hp (Walk.isSubwalk_cons p hun)
    have hpPath := (p.cons hun).isPath_of_length_eq_dist hp
    have hu_not : u ∉ p.support.toFinset := by
      simpa using (List.nodup_cons.mp hpPath.support_nodup).1
    have huv : u ≠ v := by
      intro heq
      exact hu_not (by simpa [heq])
    have hu_s : u ∉ s := by
      intro hu
      exact huv (hinter u (by simp) hu)
    have hT := ih hptail hv
      (fun z hz => hinter z (by simp [hz]))
      (fun z hz => hcross z (by simp [hz]))
    have huniq : ∀ b ∈ p.support.toFinset, G.Adj u b → b = n := by
      intro b hb hub
      have hb' : b ∈ p.support := by simpa using hb
      have hsum := dist_add_dist_eq_of_mem_geodesic p hptail hb'
      have htri := hG.dist_triangle (u := u) (v := b) (w := v)
      have hubdist : G.dist u b = 1 := dist_eq_one_iff_adj.mpr hub
      have hlen : G.dist u v = G.dist n v + 1 := by
        simpa only [Walk.length_cons, hptail] using hp.symm
      have hn : G.dist n b = 0 := by omega
      exact (hG.dist_eq_zero_iff.mp hn).symm
    have hT' := hT.induce_insert_of_unique_adj
      (by simp only [Finset.mem_union, not_or]; exact ⟨hu_not, hu_s⟩)
      (Finset.mem_union_left _ (by simp)) hun (by
        intro b hb hub
        rcases Finset.mem_union.mp hb with hb | hb
        · exact huniq b hb hub
        · have hbv := hcross u (by simp) huv b hb hub
          exact huniq b (by simp [hbv]) hub)
    have hset : (p.cons hun).support.toFinset ∪ s = insert u (p.support.toFinset ∪ s) := by
      ext z
      simp
    rw [hset]
    exact hT'

/-- A leaf adds one more vertex to any geodesic starting at its neighbor and avoiding it. -/
lemma radius_add_two_le_largestInducedTreeSize_of_leaf {G : SimpleGraph α}
    [DecidableRel G.Adj] (hG : G.Connected) {u : α} (hu : G.degree u = 1)
    (hr : 2 ≤ G.radius.toNat) : G.radius.toNat + 2 ≤ largestInducedTreeSize G := by
  classical
  haveI : Nonempty α := ⟨u⟩
  obtain ⟨v, huv, huniq⟩ := degree_eq_one_iff_existsUnique_adj.mp hu
  obtain ⟨w, hw⟩ := G.exists_edist_eq_eccent_of_finite v
  have hrw : G.radius.toNat ≤ G.dist v w :=
    ENat.toNat_le_toNat (hw ▸ G.radius_le_eccent)
      (edist_ne_top_iff_reachable.mpr (hG v w))
  have hwu : w ≠ u := by
    intro heq
    have hdist : G.dist v w = 1 := by
      rw [heq]
      exact dist_eq_one_iff_adj.mpr huv.symm
    omega
  have huw : G.dist u w = G.dist v w + 1 := by
    obtain ⟨q, hq⟩ := hG.exists_walk_length_eq_dist u w
    cases q with
    | nil => exact (hwu rfl).elim
    | @cons u b w hub q =>
      have hbv := huniq b hub
      subst b
      have htail := length_eq_dist_of_subwalk hq (Walk.isSubwalk_cons q hub)
      simpa only [Walk.length_cons, htail] using hq.symm
  obtain ⟨p, hp, hplen⟩ := hG.exists_path_of_dist v w
  have hunot : u ∉ p.support.toFinset := by
    intro humem
    have humem' : u ∈ p.support := by simpa using humem
    have hsum := dist_add_dist_eq_of_mem_geodesic p hplen humem'
    have hvu : G.dist v u = 1 := dist_eq_one_iff_adj.mpr huv.symm
    omega
  have hT := p.induce_support_isTree_of_length_eq_dist hplen
  have hi := hT.induce_insert_of_unique_adj hunot (by simp) huv
    (by intro b _ hub; exact huniq b hub)
  have hle := card_le_largestInducedTreeSize hi
  have hcard : (insert u p.support.toFinset).card = p.length + 2 := by
    rw [Finset.card_insert_of_notMem hunot,
      List.toFinset_card_of_nodup hp.support_nodup, p.length_support]
  rw [hcard, hplen] at hle
  omega

/-- Along the tail of a geodesic, distance from its start is one more than distance
from its first neighbor. -/
lemma dist_on_geodesic_tail {G : SimpleGraph α} (hG : G.Connected)
    {u n v z : α} (hun : G.Adj u n) (p : G.Walk n v)
    (hp : (p.cons hun).length = G.dist u v) (hz : z ∈ p.support) :
    G.dist u z = G.dist n z + 1 := by
  have htail := length_eq_dist_of_subwalk hp (Walk.isSubwalk_cons p hun)
  have hsum := dist_add_dist_eq_of_mem_geodesic p htail hz
  have hlen : G.dist u v = G.dist n v + 1 := by
    simpa only [Walk.length_cons, htail] using hp.symm
  have htri := hG.dist_triangle (u := u) (v := z) (w := v)
  have htri' := hG.dist_triangle (u := u) (v := n) (w := z)
  have hdistun : G.dist u n = 1 := dist_eq_one_iff_adj.mpr hun
  omega

set_option maxHeartbeats 800000 in
/-- The two geodesics in Chung's radius-drop argument yield an induced tree on
at least twice the radius minus one vertices. -/
lemma chung_bound_of_unique_farthest {G : SimpleGraph α} (hG : G.Connected)
    {c x : α} (hr : 3 ≤ G.radius.toNat) (hcx : G.dist c x = G.radius.toNat)
    (hother : ∀ z : α, z ≠ x → G.dist c z ≤ G.radius.toNat - 1) :
    2 * G.radius.toNat ≤ largestInducedTreeSize G + 1 := by
  classical
  obtain ⟨q, hq, hqlen⟩ := hG.exists_path_of_dist c x
  cases q with
  | nil => simp only [dist_self] at hcx; omega
  | @cons c a x hca q =>
    cases q with
    | nil => simp only [Walk.length_cons, Walk.length_nil] at hqlen; omega
    | @cons a b x hab q =>
      have hqalen : (q.cons hab).length = G.dist a x :=
        length_eq_dist_of_subwalk hqlen (Walk.isSubwalk_cons (q.cons hab) hca)
      have hqblen : q.length = G.dist b x :=
        length_eq_dist_of_subwalk hqalen (Walk.isSubwalk_cons q hab)
      have hqrad : q.length + 2 = G.radius.toNat := by
        simpa only [Walk.length_cons, hcx] using hqlen
      obtain ⟨w, hw⟩ := G.exists_edist_eq_eccent_of_finite b
      have hbw : G.radius.toNat ≤ G.dist b w :=
        ENat.toNat_le_toNat (hw ▸ G.radius_le_eccent)
          (edist_ne_top_iff_reachable.mpr (hG b w))
      have hwx : w ≠ x := by intro h; subst w; omega
      obtain ⟨p, hp, hplen⟩ := hG.exists_path_of_dist c w
      have hplower : G.radius.toNat - 2 ≤ p.length := by
        have htri := hG.dist_triangle (u := b) (v := c) (w := w)
        have hbc : G.dist b c ≤ 2 := by
          have hwalk := G.dist_le ((Walk.nil.cons hab).cons hca).reverse
          simpa using hwalk
        omega
      have hpupper : p.length ≤ G.radius.toNat - 1 := by
        rw [hplen]
        exact hother w hwx
      have hdistc (z : α) (hz : z ∈ p.support) : G.dist c z + 1 ≤ G.dist b z := by
        have hsum := dist_add_dist_eq_of_mem_geodesic p hplen hz
        have htri := hG.dist_triangle (u := b) (v := z) (w := w)
        omega
      have hqdist (z : α) (hz : z ∈ q.support) : G.dist c z = G.dist b z + 2 := by
        have hza := dist_on_geodesic_tail hG hca (q.cons hab) hqlen (z := z) (by simp [hz])
        have hzb := dist_on_geodesic_tail hG hab q hqalen hz
        omega
      have hinter : ∀ z ∈ p.support, z ∈ ((q.cons hab).cons hca).support → z = c := by
        intro z hzp hzq
        simp only [Walk.support_cons, List.mem_cons] at hzq
        rcases hzq with hzc | hza | hzq
        · exact hzc
        · subst z
          have hd := hdistc a hzp
          have hda : G.dist c a = 1 := dist_eq_one_iff_adj.mpr hca
          have hdb : G.dist b a = 1 := dist_eq_one_iff_adj.mpr hab.symm
          omega
        · have hd := hdistc z hzp
          have heq := hqdist z hzq
          omega
      cases p with
      | nil => simp only [Walk.length_nil] at hplower; omega
      | @cons c d w hcd p =>
        have hptail : p.length = G.dist d w :=
          length_eq_dist_of_subwalk hplen (Walk.isSubwalk_cons p hcd)
        have hcnotp : c ∉ p.support := (List.nodup_cons.mp hp.support_nodup).1
        have hcnotq : c ∉ (q.cons hab).support := (List.nodup_cons.mp hq.support_nodup).1
        have hpPath : p.IsPath := p.isPath_of_length_eq_dist hptail
        have hqPath : (q.cons hab).IsPath := (q.cons hab).isPath_of_length_eq_dist hqalen
        have hpmem {z : α} (hz : z ∈ p.support) : z ∈ (p.cons hcd).support := by
          simp only [Walk.support_cons, List.mem_cons]
          exact Or.inr hz
        have hqmem {z : α} (hz : z ∈ (q.cons hab).support) :
            z ∈ ((q.cons hab).cons hca).support := by
          simp only [Walk.support_cons, List.mem_cons]
          exact Or.inr (by simpa only [Walk.support_cons, List.mem_cons] using hz)
        have hcross : ∀ z ∈ (p.cons hcd).support, z ≠ c →
            ∀ y ∈ ((q.cons hab).cons hca).support, G.Adj z y →
              y = c ∨ (z = d ∧ y = a) := by
          intro z hzp hzc y hy hzy
          simp only [Walk.support_cons, List.mem_cons] at hy
          rcases hy with hyc | hya | hy
          · exact Or.inl hyc
          · subst y
            right
            have hd := hdistc z hzp
            have htri := hG.dist_triangle (u := b) (v := a) (w := z)
            have hba : G.dist b a = 1 := dist_eq_one_iff_adj.mpr hab.symm
            have haz : G.dist a z = 1 := dist_eq_one_iff_adj.mpr hzy.symm
            have hzp' : z ∈ p.support := by
              simpa only [Walk.support_cons, List.mem_cons, or_iff_right hzc] using hzp
            have heq := dist_on_geodesic_tail hG hcd p hplen hzp'
            have hdz : G.dist d z = 0 := by omega
            exact ⟨(hG.dist_eq_zero_iff.mp hdz).symm, rfl⟩
          · have hd := hdistc z hzp
            have heq := hqdist y hy
            have htri := hG.dist_triangle (u := b) (v := y) (w := z)
            have htri' := hG.dist_triangle (u := c) (v := z) (w := y)
            have hzydist : G.dist z y = 1 := dist_eq_one_iff_adj.mpr hzy
            have hyzdist : G.dist y z = 1 := dist_eq_one_iff_adj.mpr hzy.symm
            omega
        by_cases hda : G.Adj d a
        · have hpmax : (p.cons hcd).length = G.radius.toNat - 1 := by
            have htri := hG.dist_triangle (u := b) (v := d) (w := w)
            have hbd : G.dist b d ≤ 2 := by
              have hwalk := G.dist_le ((Walk.nil.cons hda.symm).cons hab.symm)
              simpa using hwalk
            simp only [Walk.length_cons] at hpupper ⊢
            omega
          let s := (q.cons hab).support.toFinset
          have hT : (G.induce (s : Set α)).IsTree :=
            (q.cons hab).induce_support_isTree_of_length_eq_dist hqalen
          have hdnot : d ∉ s := by
            intro hd
            have hdc := hinter d (by simp) (hqmem (by simpa only [s, List.mem_toFinset] using hd))
            exact hcd.ne hdc.symm
          have hTa := hT.induce_insert_of_unique_adj hdnot (by simp [s]) hda (by
            intro y hy hdy
            rcases hcross d (by simp) hcd.ne.symm y
                (hqmem (by simpa only [s, List.mem_toFinset] using hy)) hdy with hyc | ⟨_, hya⟩
            · exact (hcnotq (by simpa [hyc, s] using hy)).elim
            · exact hya)
          have hprev : p.reverse.length = G.dist w d := by
            simpa only [Walk.length_reverse, SimpleGraph.dist_comm] using hptail
          have hTfull := induce_union_geodesic_isTree hG p.reverse hprev (insert d s) hTa
            (by simp) (by
              intro z hz hzs
              rcases Finset.mem_insert.mp hzs with rfl | hzs
              · rfl
              · have hzp : z ∈ p.support := by
                  simpa only [Walk.support_reverse, List.mem_reverse] using hz
                have hzc := hinter z (hpmem hzp)
                  (hqmem (by simpa only [s, List.mem_toFinset] using hzs))
                exact (hcnotp (hzc ▸ hzp)).elim) (by
              intro z hz hzd y hy hzy
              rcases Finset.mem_insert.mp hy with rfl | hy
              · rfl
              · have hzp : z ∈ p.support := by
                  simpa only [Walk.support_reverse, List.mem_reverse] using hz
                rcases hcross z (hpmem hzp)
                  (by intro hzc; exact hcnotp (hzc ▸ hzp)) y
                  (hqmem (by simpa only [s, List.mem_toFinset] using hy)) hzy with hyc | ⟨hzd', _⟩
                · exact (hcnotq (by simpa [hyc, s] using hy)).elim
                · exact (hzd hzd').elim)
          have hset : p.reverse.support.toFinset ∪ insert d s = p.support.toFinset ∪ s := by
            ext z
            simp only [Finset.mem_union, Finset.mem_insert, List.mem_toFinset,
              Walk.support_reverse, List.mem_reverse]
            have hd : d ∈ p.support := by simp
            aesop
          rw [hset] at hTfull
          have hdis : Disjoint p.support.toFinset s := by
            apply Finset.disjoint_left.mpr
            intro z hz hzs
            have hzc := hinter z (hpmem (by simpa only [List.mem_toFinset] using hz))
              (hqmem (by simpa only [s, List.mem_toFinset] using hzs))
            exact hcnotp (by simpa [hzc] using hz)
          have hpcard : p.support.toFinset.card = p.length + 1 := by
            rw [List.toFinset_card_of_nodup hpPath.support_nodup, p.length_support]
          have hqcard : s.card = q.length + 2 := by
            change (q.cons hab).support.toFinset.card = q.length + 2
            rw [List.toFinset_card_of_nodup hqPath.support_nodup, Walk.length_support,
              Walk.length_cons]
          have hbound := card_le_largestInducedTreeSize hTfull
          rw [Finset.card_union_of_disjoint hdis, hpcard, hqcard] at hbound
          simp only [Walk.length_cons] at hpmax
          omega
        · have hprev : (p.cons hcd).reverse.length = G.dist w c := by
            simpa only [Walk.length_reverse, SimpleGraph.dist_comm] using hplen
          let s := ((q.cons hab).cons hca).support.toFinset
          have hT : (G.induce (s : Set α)).IsTree :=
            ((q.cons hab).cons hca).induce_support_isTree_of_length_eq_dist hqlen
          have hTfull := induce_union_geodesic_isTree hG (p.cons hcd).reverse hprev s hT
            (by simp [s]) (by
              intro z hz hzs
              exact hinter z (by simpa only [Walk.support_reverse, List.mem_reverse] using hz)
                (by simpa only [s, List.mem_toFinset] using hzs)) (by
              intro z hz hzc y hy hzy
              rcases hcross z (by simpa only [Walk.support_reverse, List.mem_reverse] using hz)
                  hzc y (by simpa only [s, List.mem_toFinset] using hy) hzy with
                hyc | ⟨hzd, hya⟩
              · exact hyc
              · exact (hda (by simpa [hzd, hya] using hzy)).elim)
          have hset : (p.cons hcd).reverse.support.toFinset ∪ s = p.support.toFinset ∪ s := by
            ext z
            simp only [Finset.mem_union, List.mem_toFinset, Walk.support_reverse,
              List.mem_reverse, Walk.support_cons, List.mem_cons]
            have hc : c ∈ s := by simp [s]
            aesop
          rw [hset] at hTfull
          have hdis : Disjoint p.support.toFinset s := by
            apply Finset.disjoint_left.mpr
            intro z hz hzs
            have hzc := hinter z (hpmem (by simpa only [List.mem_toFinset] using hz))
              (by simpa only [s, List.mem_toFinset] using hzs)
            exact hcnotp (by simpa [hzc] using hz)
          have hpcard : p.support.toFinset.card = p.length + 1 := by
            rw [List.toFinset_card_of_nodup hpPath.support_nodup, p.length_support]
          have hqcard : s.card = q.length + 3 := by
            change ((q.cons hab).cons hca).support.toFinset.card = q.length + 3
            rw [List.toFinset_card_of_nodup hq.support_nodup, Walk.length_support]
            simp only [Walk.length_cons]
          have hbound := card_le_largestInducedTreeSize hTfull
          rw [Finset.card_union_of_disjoint hdis, hpcard, hqcard] at hbound
          simp only [Walk.length_cons] at hplower
          omega

/-- Chung's induction gives an induced tree of order at least twice the radius minus one. -/
lemma chung_induced_tree_bound {G : SimpleGraph α} (hG : G.Connected) :
    2 * G.radius.toNat ≤ largestInducedTreeSize G + 1 := by
  classical
  induction hn : Fintype.card α using Nat.strong_induction_on generalizing α with
  | h n ih =>
    haveI : Nonempty α := hG.nonempty
    have htree := radius_add_one_le_largestInducedTreeSize (G := G) hG
    by_cases hr : G.radius.toNat ≤ 2
    · omega
    have hr : 3 ≤ G.radius.toNat := by omega
    haveI : Nontrivial α := by
      rcases subsingleton_or_nontrivial α with hsub | hnt
      · have hzero : G.radius = 0 := G.radius_eq_zero_iff.mpr ⟨hG.nonempty, hsub⟩
        simp only [hzero, ENat.toNat_zero] at hr
        omega
      · exact hnt
    obtain ⟨x, hx⟩ := hG.exists_connected_induce_compl_singleton_of_finite_nontrivial
    let H := G.induce ({x}ᶜ : Set α)
    have hcard : Fintype.card ↥({x}ᶜ : Set α) < n := by
      rw [← hn]
      exact Fintype.card_subtype_lt (x := x) (by simp)
    by_cases hrad : G.radius.toNat ≤ H.radius.toNat
    · have hsmall := ih _ hcard (G := H) hx rfl
      have htrans : largestInducedTreeSize H ≤ largestInducedTreeSize G :=
        largestInducedTreeSize_induce_le G ({x}ᶜ : Set α)
      omega
    · have hdrop : H.radius.toNat ≤ G.radius.toNat - 1 := by omega
      obtain ⟨c, _, _, hcx, hother⟩ := radius_drop_witness hG x hx (by omega) hdrop
      exact chung_bound_of_unique_farthest hG hr hcx hother

/-- The supports of two geodesics in separate branches induce a tree of their combined order. -/
lemma geodesic_branches_bound {G : SimpleGraph α} (hG : G.Connected)
    {c a b : α} (p : G.Walk c a) (q : G.Walk c b)
    (hp : p.length = G.dist c a) (hq : q.length = G.dist c b)
    (hinter : ∀ z ∈ p.support, z ∈ q.support → z = c)
    (hsep : ∀ z ∈ p.support, z ≠ c → ∀ y ∈ q.support, y ≠ c → ¬ G.Adj z y) :
    p.length + q.length + 1 ≤ largestInducedTreeSize G := by
  classical
  have hprev : p.reverse.length = G.dist a c := by
    simpa only [Walk.length_reverse, SimpleGraph.dist_comm] using hp
  have hT := induce_union_geodesic_isTree hG p.reverse hprev q.support.toFinset
    (q.induce_support_isTree_of_length_eq_dist hq) (by simp) (by
      intro z hz hzs
      exact hinter z (by simpa only [Walk.support_reverse, List.mem_reverse] using hz)
        (by simpa only [List.mem_toFinset] using hzs)) (by
      intro z hz hzc y hy hzy
      by_contra hyc
      exact hsep z (by simpa only [Walk.support_reverse, List.mem_reverse] using hz) hzc y
        (by simpa only [List.mem_toFinset] using hy) hyc hzy)
  have hset : p.reverse.support.toFinset ∪ q.support.toFinset =
      p.support.toFinset ∪ q.support.toFinset := by ext z; simp
  rw [hset] at hT
  have hcardp : p.support.toFinset.card = p.length + 1 := by
    rw [List.toFinset_card_of_nodup (p.isPath_of_length_eq_dist hp).support_nodup,
      p.length_support]
  have hcardq : q.support.toFinset.card = q.length + 1 := by
    rw [List.toFinset_card_of_nodup (q.isPath_of_length_eq_dist hq).support_nodup,
      q.length_support]
  have hinterset : p.support.toFinset ∩ q.support.toFinset = {c} := by
    ext z
    simp only [Finset.mem_inter, List.mem_toFinset, Finset.mem_singleton]
    constructor
    · exact fun ⟨hzp, hzq⟩ => hinter z hzp hzq
    · intro hzc
      subst z
      exact ⟨p.start_mem_support, q.start_mem_support⟩
  have hbound := card_le_largestInducedTreeSize hT
  rw [Finset.card_union, hcardp, hcardq, hinterset, Finset.card_singleton] at hbound
  omega

/-- After removing the initial vertex of a geodesic, its remaining vertices still reach
the endpoint in the deletion graph. -/
lemma reachable_compl_of_mem_geodesic {G : SimpleGraph α} {c a z : α}
    (p : G.Walk c a) (hp : p.length = G.dist c a) (ha : a ≠ c)
    (hz : z ∈ p.support) (hzc : z ≠ c) :
    (G.induce ({c}ᶜ : Set α)).Reachable
      ⟨z, by simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hzc⟩
      ⟨a, by simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using ha⟩ := by
  cases p with
  | nil => exact (ha rfl).elim
  | @cons c n a hcn p =>
    have hpath := (p.cons hcn).isPath_of_length_eq_dist hp
    have hcnot : c ∉ p.support := (List.nodup_cons.mp hpath.support_nodup).1
    have hzp : z ∈ p.support := by
      simpa only [Walk.support_cons, List.mem_cons, or_iff_right hzc] using hz
    let q := p.dropUntil z hzp
    have hsub : ∀ w ∈ q.support, w ∈ ({c}ᶜ : Set α) := by
      intro w hw
      have hwp := p.support_dropUntil_subset hzp hw
      have hwc : w ≠ c := by intro heq; exact hcnot (heq ▸ hwp)
      simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hwc
    exact ⟨q.induce ({c}ᶜ : Set α) hsub⟩

/-- Geodesics from a cut vertex into different components give the two-branch tree bound. -/
lemma geodesic_branches_bound_of_not_reachable {G : SimpleGraph α} (hG : G.Connected)
    {c a b : α} (ha : a ≠ c) (hb : b ≠ c)
    (hsep : ¬ (G.induce ({c}ᶜ : Set α)).Reachable
      ⟨a, by simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using ha⟩
      ⟨b, by simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hb⟩) :
    G.dist c a + G.dist c b + 1 ≤ largestInducedTreeSize G := by
  obtain ⟨p, _, hp⟩ := hG.exists_path_of_dist c a
  obtain ⟨q, _, hq⟩ := hG.exists_path_of_dist c b
  rw [← hp, ← hq]
  apply geodesic_branches_bound hG p q hp hq
  · intro z hzp hzq
    by_contra hzc
    have hza := reachable_compl_of_mem_geodesic p hp ha hzp hzc
    have hzb := reachable_compl_of_mem_geodesic q hq hb hzq hzc
    exact hsep (hza.symm.trans hzb)
  · intro z hzp hzc y hyq hyc hzy
    have hza := reachable_compl_of_mem_geodesic p hp ha hzp hzc
    have hyb := reachable_compl_of_mem_geodesic q hq hb hyq hyc
    have hadj : (G.induce ({c}ᶜ : Set α)).Adj
        ⟨z, by simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hzc⟩
        ⟨y, by simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hyc⟩ := hzy
    exact hsep (hza.symm.trans (hadj.reachable.trans hyb))

/-- Vertices in different deletion components have all shortest paths through the cut vertex. -/
lemma dist_eq_add_of_not_reachable_compl {G : SimpleGraph α} (hG : G.Connected)
    {c a b : α} (ha : a ≠ c) (hb : b ≠ c)
    (hsep : ¬ (G.induce ({c}ᶜ : Set α)).Reachable
      ⟨a, by simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using ha⟩
      ⟨b, by simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hb⟩) :
    G.dist a b = G.dist a c + G.dist c b := by
  obtain ⟨p, _, hp⟩ := hG.exists_path_of_dist a b
  by_cases hc : c ∈ p.support
  · exact (dist_add_dist_eq_of_mem_geodesic p hp hc).symm
  · have hsub : ∀ z ∈ p.support, z ∈ ({c}ᶜ : Set α) := by
      intro z hz
      have hzc : z ≠ c := by intro heq; exact hc (heq ▸ hz)
      simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hzc
    exact (hsep ⟨p.induce ({c}ᶜ : Set α) hsub⟩).elim

/-- A side at a cut vertex consists of that vertex and one deletion component. -/
def cutSide (G : SimpleGraph α) (c : α) (a : ↥({c}ᶜ : Set α)) : Set α :=
  {z | z = c ∨ ∃ hz : z ≠ c, (G.induce ({c}ᶜ : Set α)).Reachable
    a ⟨z, by simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hz⟩}

/-- A geodesic from a cut vertex to a point of one side stays in that side. -/
lemma geodesic_support_subset_cutSide {G : SimpleGraph α} (hG : G.Connected)
    {c v : α} (a : ↥({c}ᶜ : Set α)) (hv : v ∈ cutSide G c a)
    (p : G.Walk c v) (hp : p.length = G.dist c v) :
    ∀ z ∈ p.support, z ∈ cutSide G c a := by
  intro z hz
  by_cases hzc : z = c
  · exact Or.inl hzc
  · refine Or.inr ⟨hzc, ?_⟩
    have hvc : v ≠ c := by
      intro heq
      have hsum := dist_add_dist_eq_of_mem_geodesic p hp hz
      have hdist : G.dist c z = 0 := by simp only [heq, dist_self] at hsum; omega
      exact hzc (hG.dist_eq_zero_iff.mp hdist).symm
    rcases hv with hvc' | ⟨_, hv⟩
    · exact (hvc hvc').elim
    · exact hv.trans (reachable_compl_of_mem_geodesic p hp hvc hz hzc).symm

/-- A side at a cut vertex is connected. -/
lemma connected_induce_cutSide {G : SimpleGraph α} (hG : G.Connected)
    (c : α) (a : ↥({c}ᶜ : Set α)) : (G.induce (cutSide G c a)).Connected := by
  rw [connected_iff_exists_forall_reachable]
  refine ⟨⟨c, Or.inl rfl⟩, ?_⟩
  intro v
  obtain ⟨p, hp⟩ := hG.exists_walk_length_eq_dist c v
  exact ⟨p.induce (cutSide G c a) (geodesic_support_subset_cutSide hG a v.property p hp)⟩

/-- Restricting a walk to a vertex set preserves its length. -/
lemma length_induce_walk {G : SimpleGraph α} {S : Set α} {u v : α}
    (p : G.Walk u v) (hp : ∀ z ∈ p.support, z ∈ S) :
    (p.induce S hp).length = p.length := by
  calc
    (p.induce S hp).length = ((p.induce S hp).map
        (SimpleGraph.Embedding.induce S).toHom).length := (Walk.length_map _ _).symm
    _ = p.length := congrArg Walk.length (Walk.map_induce p hp)

/-- Distances inside one side of a cut vertex equal their ambient distances. -/
lemma dist_induce_cutSide {G : SimpleGraph α} (hG : G.Connected)
    (c : α) (a : ↥({c}ᶜ : Set α)) (u v : cutSide G c a) :
    (G.induce (cutSide G c a)).dist u v = G.dist u v := by
  classical
  let S := cutSide G c a
  have hS := connected_induce_cutSide hG c a
  apply le_antisymm
  · obtain ⟨p, hp⟩ := hG.exists_walk_length_eq_dist (u : α) v
    by_cases hc : c ∈ p.support
    · let pu := (p.takeUntil c hc).reverse
      let pv := p.dropUntil c hc
      have hpu : pu.length = G.dist c u := by
        simpa only [pu, Walk.length_reverse, SimpleGraph.dist_comm] using
          length_eq_dist_of_subwalk hp (p.isSubwalk_takeUntil hc)
      have hpv : pv.length = G.dist c v :=
        length_eq_dist_of_subwalk hp (p.isSubwalk_dropUntil hc)
      have hsu := geodesic_support_subset_cutSide hG a u.property pu hpu
      have hsv := geodesic_support_subset_cutSide hG a v.property pv hpv
      let q := (pu.induce S hsu).reverse.append (pv.induce S hsv)
      have hdist := (G.induce S).dist_le q
      have hlen : q.length = G.dist (u : α) v := by
        have hsum := dist_add_dist_eq_of_mem_geodesic p hp hc
        simp only [q, Walk.length_append, Walk.length_reverse, length_induce_walk, hpu, hpv]
        rw [G.dist_comm (u := c) (v := (u : α))]
        exact hsum
      exact hdist.trans_eq hlen
    · have hsub : ∀ z ∈ p.support, z ∈ ({c}ᶜ : Set α) := by
        intro z hz
        have hzc : z ≠ c := by intro heq; exact hc (heq ▸ hz)
        simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hzc
      have hu : (u : α) ≠ c := by
        intro huc
        exact hc (Eq.subst (motive := fun z : α => z ∈ p.support) huc p.start_mem_support)
      have hur : (G.induce ({c}ᶜ : Set α)).Reachable a
          ⟨(u : α), by simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hu⟩ := by
        rcases u.property with huc | ⟨_, hu'⟩
        · exact (hu huc).elim
        · exact hu'
      have hsubS : ∀ z ∈ p.support, z ∈ S := by
        intro z hz
        have hzc : z ≠ c := by
          simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hsub z hz
        refine Or.inr ⟨hzc, hur.trans ?_⟩
        exact ⟨(p.takeUntil z hz).induce ({c}ᶜ : Set α)
          (fun w hw => hsub w (p.support_takeUntil_subset hz hw))⟩
      have hdist := (G.induce S).dist_le (p.induce S hsubS)
      simpa only [length_induce_walk, hp] using hdist
  · obtain ⟨p, hp⟩ := hS.exists_walk_length_eq_dist u v
    have hdist := G.dist_le (p.map (SimpleGraph.Embedding.induce S).toHom)
    rw [Walk.length_map] at hdist
    change G.dist (u : α) (v : α) ≤ p.length at hdist
    exact hdist.trans_eq hp

/-- If every discarded vertex is no farther than some retained vertex from each retained
vertex, passing to the connected induced graph cannot decrease the radius. -/
lemma radius_le_radius_induce_of_dominated {G : SimpleGraph α} (hG : G.Connected)
    (S : Set α) [DecidablePred (· ∈ S)] (hS : (G.induce S).Connected)
    (hdom : ∀ v ∈ S, ∀ z ∉ S, ∃ w ∈ S, G.dist v z ≤ G.dist v w) :
    G.radius.toNat ≤ (G.induce S).radius.toNat := by
  haveI : Nonempty S := hS.nonempty
  let H := G.induce S
  obtain ⟨v, hv⟩ := H.exists_eccent_eq_radius
  have hfin : H.radius ≠ ⊤ := H.radius_ne_top_iff.mpr hS
  have hdist (w : S) : G.dist v w ≤ H.radius.toNat := by
    obtain ⟨p, hp⟩ := hS.exists_walk_length_eq_dist v w
    have hmap := G.dist_le (p.map (SimpleGraph.Embedding.induce S).toHom)
    rw [Walk.length_map] at hmap
    change G.dist (v : α) (w : α) ≤ p.length at hmap
    have hcenter : H.dist v w ≤ H.radius.toNat :=
      ENat.toNat_le_toNat (hv ▸ (H.edist_le_eccent (u := v) (v := w))) hfin
    exact hmap.trans (hp ▸ hcenter)
  obtain ⟨z, hz⟩ := G.exists_edist_eq_eccent_of_finite (v : α)
  have hrz : G.radius.toNat ≤ G.dist v z :=
    ENat.toNat_le_toNat (hz ▸ G.radius_le_eccent)
      (edist_ne_top_iff_reachable.mpr (hG v z))
  by_cases hzs : z ∈ S
  · exact hrz.trans (hdist ⟨z, hzs⟩)
  · obtain ⟨w, hw, hzw⟩ := hdom v v.property z hzs
    exact hrz.trans (hzw.trans (hdist ⟨w, hw⟩))

/-- A separated pair in the ambient deletion graph certifies a cut in any induced graph
containing that pair and the deleted vertex. -/
lemma not_connected_induce_delete_of_separated_pair {G : SimpleGraph α}
    {S : Set α} {c a b : α} (hcS : c ∈ S) (haS : a ∈ S) (hbS : b ∈ S)
    (hac : a ≠ c) (hbc : b ≠ c)
    (hsep : ¬ (G.induce ({c}ᶜ : Set α)).Reachable
      ⟨a, by simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hac⟩
      ⟨b, by simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hbc⟩) :
    ¬ ((G.induce S).induce ({(⟨c, hcS⟩ : S)}ᶜ : Set S)).Connected := by
  let c' : S := ⟨c, hcS⟩
  let T := ({c'}ᶜ : Set S)
  let a' : T := ⟨⟨a, haS⟩, by
    change (⟨a, haS⟩ : S) ≠ c'
    intro heq
    exact hac (congrArg Subtype.val heq)⟩
  let b' : T := ⟨⟨b, hbS⟩, by
    change (⟨b, hbS⟩ : S) ≠ c'
    intro heq
    exact hbc (congrArg Subtype.val heq)⟩
  let f : (G.induce S).induce T →g G.induce ({c}ᶜ : Set α) :=
    { toFun := fun z => ⟨(z : S), by
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
        intro heq
        have hzc : (z : S) ≠ c' := by
          exact z.property
        exact hzc (Subtype.ext heq)⟩
      map_rel' := by intro u v huv; exact huv }
  intro hconn
  exact hsep ((hconn a' b').map f)

/-- In a minimal counterexample, every cut vertex has one whole side and a shallower
geodesic as its other side. -/
lemma cut_vertex_two_side_reduction {G : SimpleGraph α} (hG : G.Connected)
    (hr : 2 ≤ G.radius.toNat) (hlt : largestInducedTreeSize G < 2 * G.radius.toNat)
    (hsmall : ∀ (S : Set α) [DecidablePred (· ∈ S)], S ≠ Set.univ →
      (G.induce S).Connected →
      (∃ x, ¬ ((G.induce S).induce ({x}ᶜ : Set S)).Connected) →
      2 * (G.induce S).radius.toNat ≤ largestInducedTreeSize (G.induce S))
    (c : α) (hc : ¬ (G.induce ({c}ᶜ : Set α)).Connected) :
    ∃ a b : ↥({c}ᶜ : Set α), ∃ q : G.Walk c (b : α),
      q.length = G.dist c b ∧
      ¬ (G.induce ({c}ᶜ : Set α)).Reachable a b ∧
      G.dist c b + 2 ≤ G.dist c a ∧
      ∀ z : α, z ∈ cutSide G c a ∨ z ∈ q.support := by
  classical
  obtain ⟨a, ha⟩ := G.exists_edist_eq_eccent_of_finite c
  have hra : G.radius.toNat ≤ G.dist c a :=
    ENat.toNat_le_toNat (ha ▸ G.radius_le_eccent)
      (edist_ne_top_iff_reachable.mpr (hG c a))
  have hac : a ≠ c := by intro heq; subst a; simp only [dist_self] at hra; omega
  let H := G.induce ({c}ᶜ : Set α)
  let a' : ↥({c}ᶜ : Set α) := ⟨a, by simpa using hac⟩
  have hbex : ∃ b : ↥({c}ᶜ : Set α), ¬ H.Reachable a' b := by
    by_contra! hall
    exact hc ((H.connected_iff_exists_forall_reachable).mpr ⟨a', hall⟩)
  let B : Set ↥({c}ᶜ : Set α) := {b | ¬ H.Reachable a' b}
  obtain ⟨b, hb, hbmax⟩ := Set.exists_max_image B (fun z => G.dist c (z : α))
    (Set.toFinite B) hbex
  have hbc : (b : α) ≠ c := by
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using b.property
  have hbranches := geodesic_branches_bound_of_not_reachable hG hac hbc hb
  have hgap : G.dist c b + 2 ≤ G.dist c a := by omega
  obtain ⟨q, _, hq⟩ := hG.exists_path_of_dist c (b : α)
  let S := cutSide G c a'
  let U := S ∪ {z : α | z ∈ q.support}
  have hcS : c ∈ S := Or.inl rfl
  have haS : a ∈ S := Or.inr ⟨hac, Reachable.rfl⟩
  have hU : (G.induce U).Connected :=
    induce_union_connected (connected_induce_cutSide hG c a').preconnected
      q.connected_induce_support.preconnected ⟨c, hcS, q.start_mem_support⟩
  have hcU : c ∈ U := Or.inl hcS
  have haU : a ∈ U := Or.inl haS
  have hbU : (b : α) ∈ U := Or.inr q.end_mem_support
  have hcutU := not_connected_induce_delete_of_separated_pair hcU haU hbU hac hbc hb
  have hdepth (z : α) : G.dist c z ≤ G.dist c a := by
    have hle : G.edist c z ≤ G.edist c a := by rw [ha]; exact G.edist_le_eccent
    exact ENat.toNat_le_toNat hle (edist_ne_top_iff_reachable.mpr (hG c a))
  have hdom : ∀ v ∈ U, ∀ z ∉ U, ∃ w ∈ U, G.dist v z ≤ G.dist v w := by
    intro v _ z hz
    have hzS : z ∉ S := fun hzS => hz (Or.inl hzS)
    have hzc : z ≠ c := by intro heq; exact hzS (heq ▸ hcS)
    have hznr : ¬ H.Reachable a'
        ⟨z, by simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hzc⟩ :=
      fun hreach => hzS (Or.inr ⟨hzc, hreach⟩)
    have hzb : G.dist c z ≤ G.dist c b := hbmax _ hznr
    by_cases hvS : v ∈ S
    · refine ⟨b, hbU, ?_⟩
      have hvb : G.dist v b = G.dist v c + G.dist c b := by
        by_cases hvc : v = c
        · simp [hvc]
        · rcases hvS with heq | ⟨_, hvr⟩
          · exact (hvc heq).elim
          · apply dist_eq_add_of_not_reachable_compl hG hvc hbc
            intro hreach
            exact hb (hvr.trans hreach)
      have htri := hG.dist_triangle (u := v) (v := c) (w := z)
      omega
    · refine ⟨a, haU, ?_⟩
      have hvc : v ≠ c := by intro heq; exact hvS (heq ▸ hcS)
      have hva : G.dist v a = G.dist v c + G.dist c a := by
        apply dist_eq_add_of_not_reachable_compl hG hvc hac
        intro hreach
        exact hvS (Or.inr ⟨hvc, hreach.symm⟩)
      have htri := hG.dist_triangle (u := v) (v := c) (w := z)
      have hzdepth := hdepth z
      omega
  have hUeq : U = Set.univ := by
    by_contra hproper
    have hsm := hsmall U hproper hU ⟨⟨c, hcU⟩, hcutU⟩
    have hrad := radius_le_radius_induce_of_dominated hG U hU hdom
    have htrans := largestInducedTreeSize_induce_le G U
    omega
  refine ⟨a', b, q, hq, hb, hgap, ?_⟩
  intro z
  have hz : z ∈ U := hUeq ▸ Set.mem_univ z
  exact hz

/-- A proper prefix of a path does not contain its terminal vertex. -/
lemma end_not_mem_takeUntil {G : SimpleGraph α} {u v z : α} (p : G.Walk u v)
    (hp : p.IsPath) (hz : z ∈ p.support) (hzv : z ≠ v) :
    v ∉ (p.takeUntil z hz).support := by
  intro hv
  have hpath : ((p.takeUntil z hz).append (p.dropUntil z hz)).IsPath := by
    rw [p.take_spec hz]
    exact hp
  exact hpath.ne_of_mem_support_of_append hzv.symm hv (p.dropUntil z hz).end_mem_support rfl

/-- Deleting any vertex from the graph induced by a cycle's support leaves a connected graph. -/
lemma cycle_support_delete_connected {G : SimpleGraph α} {u : α} (p : G.Walk u u)
    (hp : p.IsCycle) (x : ↥(p.support.toFinset : Set α)) :
    ((G.induce (p.support.toFinset : Set α)).induce ({x}ᶜ : Set ↥(p.support.toFinset : Set α))).Connected := by
  classical
  have hx : (x : α) ∈ p.support := List.mem_toFinset.mp x.property
  let r := p.rotate (x : α) hx
  have hr : r.IsCycle := hp.rotate hx
  have hrtail : r.tail.IsPath := by
    rw [Walk.isPath_def, r.support_tail_of_not_nil hr.not_nil]
    exact hr.support_nodup
  have hrot (z : α) (hz : z ∈ r.support) : z ∈ p.support :=
    (p.mem_support_rotate_iff (x : α) hx).mp hz
  have htailmem (z : α) (hz : z ∈ p.support) (hzx : z ≠ (x : α)) :
      z ∈ r.tail.support := by
    rw [r.support_tail_of_not_nil hr.not_nil]
    have hzr := (p.mem_support_rotate_iff (x : α) hx).mpr hz
    have hhead : r.support = (x : α) :: r.support.tail := by cases r <;> rfl
    rw [hhead] at hzr
    exact (List.mem_cons.mp hzr).resolve_left hzx
  let S : Set α := p.support.toFinset
  let T : Set α := {z | z ∈ S ∧ z ≠ (x : α)}
  let f : G.induce T →g (G.induce S).induce ({x}ᶜ : Set S) :=
    { toFun := fun z => ⟨⟨z, z.property.1⟩, by
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
        intro heq
        exact z.property.2 (congrArg Subtype.val heq)⟩
      map_rel' := by intro a b hab; exact hab }
  have hnmem : r.snd ∈ S := by
    apply List.mem_toFinset.mpr
    exact hrot _ (r.getVert_mem_support 1)
  have hnx : r.snd ≠ (x : α) := (r.adj_snd hr.not_nil).ne.symm
  let n : ↥({x}ᶜ : Set S) := ⟨⟨r.snd, hnmem⟩, by
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    intro heq
    exact hnx (congrArg Subtype.val heq)⟩
  rw [connected_iff_exists_forall_reachable]
  refine ⟨n, ?_⟩
  intro z
  have hzmem : ((z : S) : α) ∈ p.support := by
    exact List.mem_toFinset.mp (z : S).property
  have hzx : ((z : S) : α) ≠ (x : α) := by
    intro heq
    have hne : (z : S) ≠ x := z.property
    exact hne (Subtype.ext heq)
  have hztail := htailmem _ hzmem hzx
  let q := r.tail.takeUntil ((z : S) : α) hztail
  have hqx : (x : α) ∉ q.support := end_not_mem_takeUntil r.tail hrtail hztail hzx
  have hsub : ∀ w ∈ q.support, w ∈ T := by
    intro w hw
    have hwrtail : w ∈ r.tail.support := r.tail.support_takeUntil_subset hztail hw
    have hwr : w ∈ r.support := by
      rw [r.support_tail_of_not_nil hr.not_nil] at hwrtail
      exact List.mem_of_mem_tail hwrtail
    refine ⟨List.mem_toFinset.mpr (hrot w hwr), ?_⟩
    intro heq
    exact hqx (heq ▸ hw)
  exact ⟨(q.induce T hsub).map f⟩

/-- A cyclic graph contains an induced vertex-connected core maximal under vertex inclusion. -/
lemma exists_maximal_vertex_core {G : SimpleGraph α} (hcyc : ¬ G.IsAcyclic) :
    ∃ s : Finset α, 3 ≤ s.card ∧ (G.induce (s : Set α)).Connected ∧
      (∀ x : ↥(s : Set α),
        ((G.induce (s : Set α)).induce ({x}ᶜ : Set ↥(s : Set α))).Connected) ∧
      ∀ t : Finset α, s ⊆ t → 3 ≤ t.card → (G.induce (t : Set α)).Connected →
        (∀ x : ↥(t : Set α),
          ((G.induce (t : Set α)).induce ({x}ᶜ : Set ↥(t : Set α))).Connected) → t = s := by
  classical
  obtain ⟨v, p, hp, _⟩ := G.exists_girth_eq_length.mpr hcyc
  have hcardtail : p.support.tail.toFinset.card = p.length := by
    rw [List.toFinset_card_of_nodup hp.support_nodup, List.length_tail, p.length_support]
    omega
  have hcard : 3 ≤ p.support.toFinset.card := by
    have hle : p.support.tail.toFinset.card ≤ p.support.toFinset.card := by
      apply Finset.card_le_card
      intro z hz
      exact List.mem_toFinset.mpr (List.mem_of_mem_tail (List.mem_toFinset.mp hz))
    have hthree := hp.three_le_length
    omega
  let A : Set (Finset α) := {s | 3 ≤ s.card ∧ (G.induce (s : Set α)).Connected ∧
    ∀ x : ↥(s : Set α),
      ((G.induce (s : Set α)).induce ({x}ᶜ : Set ↥(s : Set α))).Connected}
  have hA : A.Nonempty := by
    refine ⟨p.support.toFinset, hcard, ?_, cycle_support_delete_connected p hp⟩
    have hset : (p.support.toFinset : Set α) = {z | z ∈ p.support} := by ext z; simp
    rw [hset]
    exact p.connected_induce_support
  obtain ⟨s, hs, hmax⟩ := Set.exists_max_image A Finset.card (Set.toFinite A) hA
  refine ⟨s, hs.1, hs.2.1, hs.2.2, ?_⟩
  intro t hst htcard htconn htdel
  symm
  apply Finset.eq_of_subset_of_card_le hst
  exact hmax t ⟨htcard, htconn, htdel⟩

/-- A walk supported in an induced graph and avoiding a vertex lifts to its deletion graph. -/
lemma reachable_induce_delete_of_walk {G : SimpleGraph α} {S : Set α} (x : S)
    (u v : ↥({x}ᶜ : Set S)) (p : G.Walk ((u : S) : α) ((v : S) : α))
    (hS : ∀ z ∈ p.support, z ∈ S) (hx : (x : α) ∉ p.support) :
    ((G.induce S).induce ({x}ᶜ : Set S)).Reachable u v := by
  let T : Set α := {z | z ∈ S ∧ z ≠ (x : α)}
  have hT : ∀ z ∈ p.support, z ∈ T := by
    intro z hz
    exact ⟨hS z hz, fun hzx => hx (hzx ▸ hz)⟩
  let f : G.induce T →g (G.induce S).induce ({x}ᶜ : Set S) :=
    { toFun := fun z => ⟨⟨z, z.property.1⟩, by
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
        intro heq
        exact z.property.2 (congrArg Subtype.val heq)⟩
      map_rel' := by intro u v huv; exact huv }
  exact ⟨(p.induce T hT).map f⟩

/-- Paths within a vertex-connected core can avoid any prescribed vertex. -/
lemma exists_walk_in_core_avoiding {G : SimpleGraph α} (K : Finset α)
    (hK : (G.induce (K : Set α)).Connected)
    (hdel : ∀ x : ↥(K : Set α),
      ((G.induce (K : Set α)).induce ({x}ᶜ : Set ↥(K : Set α))).Connected)
    (x : α) {u v : α} (hu : u ∈ K) (hv : v ∈ K) (hux : u ≠ x) (hvx : v ≠ x) :
    ∃ p : G.Walk u v, (∀ z ∈ p.support, z ∈ K) ∧ x ∉ p.support := by
  classical
  by_cases hx : x ∈ K
  · let x' : ↥(K : Set α) := ⟨x, hx⟩
    let u' : ↥({x'}ᶜ : Set ↥(K : Set α)) := ⟨⟨u, hu⟩, by
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      intro heq
      exact hux (congrArg Subtype.val heq)⟩
    let v' : ↥({x'}ᶜ : Set ↥(K : Set α)) := ⟨⟨v, hv⟩, by
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      intro heq
      exact hvx (congrArg Subtype.val heq)⟩
    obtain ⟨p⟩ := hdel x' u' v'
    let f : (G.induce (K : Set α)).induce ({x'}ᶜ : Set ↥(K : Set α)) →g G :=
      { toFun := fun z => ((z : ↥(K : Set α)) : α)
        map_rel' := by intro u v huv; exact huv }
    refine ⟨p.map f, ?_, ?_⟩
    · intro z hz
      rw [Walk.support_map] at hz
      obtain ⟨w, _, rfl⟩ := List.mem_map.mp hz
      exact (w : ↥(K : Set α)).property
    · intro hxmem
      rw [Walk.support_map] at hxmem
      obtain ⟨w, _, hw⟩ := List.mem_map.mp hxmem
      have hwne : (w : ↥(K : Set α)) ≠ x' := w.property
      exact hwne (Subtype.ext hw)
  · obtain ⟨p⟩ := hK (⟨u, hu⟩ : ↥(K : Set α)) ⟨v, hv⟩
    let f : G.induce (K : Set α) →g G := (SimpleGraph.Embedding.induce (K : Set α)).toHom
    have hsub : ∀ z ∈ (p.map f).support, z ∈ K := by
      intro z hz
      rw [Walk.support_map] at hz
      obtain ⟨w, _, rfl⟩ := List.mem_map.mp hz
      exact w.property
    exact ⟨p.map f, hsub, fun hxmem => hx (hsub x hxmem)⟩

set_option maxHeartbeats 800000 in
/-- Adding a path between distinct vertices of a vertex-connected core preserves
connectedness after every vertex deletion. -/
lemma core_union_path_delete_connected {G : SimpleGraph α} (K : Finset α)
    (hcard : 3 ≤ K.card) (hK : (G.induce (K : Set α)).Connected)
    (hdel : ∀ x : ↥(K : Set α),
      ((G.induce (K : Set α)).induce ({x}ᶜ : Set ↥(K : Set α))).Connected)
    {a b : α} (ha : a ∈ K) (hb : b ∈ K) (hab : a ≠ b)
    (p : G.Walk a b) (hp : p.IsPath)
    (x : ↥((K ∪ p.support.toFinset : Finset α) : Set α)) :
    ((G.induce ((K ∪ p.support.toFinset : Finset α) : Set α)).induce
      ({x}ᶜ : Set ↥((K ∪ p.support.toFinset : Finset α) : Set α))).Connected := by
  classical
  let U : Set α := (K ∪ p.support.toFinset : Finset α)
  have hyex : ∃ y ∈ K, y ≠ (x : α) := by
    by_contra! hn
    have hsub : K ⊆ {(x : α)} := by intro y hy; simpa using hn y hy
    have hle := Finset.card_le_card hsub
    simp only [Finset.card_singleton] at hle
    omega
  obtain ⟨y, hy, hyx⟩ := hyex
  let y' : ↥({x}ᶜ : Set U) := ⟨⟨y, Finset.mem_union_left _ hy⟩, by
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    intro heq
    exact hyx (congrArg Subtype.val heq)⟩
  have hcore (z : α) (hz : z ∈ K) (hzx : z ≠ (x : α)) :
      ∃ q : G.Walk y z, (∀ w ∈ q.support, w ∈ U) ∧ (x : α) ∉ q.support := by
    obtain ⟨q, hq, hqx⟩ := exists_walk_in_core_avoiding K hK hdel (x : α) hy hz hyx hzx
    exact ⟨q, fun w hw => Finset.mem_union_left _ (hq w hw), hqx⟩
  rw [connected_iff_exists_forall_reachable]
  refine ⟨y', ?_⟩
  intro z
  have hzx : ((z : U) : α) ≠ (x : α) := by
    intro heq
    have hne : (z : U) ≠ x := z.property
    exact hne (Subtype.ext heq)
  have hzU : ((z : U) : α) ∈ K ∪ p.support.toFinset := (z : U).property
  rcases Finset.mem_union.mp hzU with hzK | hzp
  · obtain ⟨q, hq, hqx⟩ := hcore _ hzK hzx
    exact reachable_induce_delete_of_walk x y' z q hq hqx
  · have hzp' : ((z : U) : α) ∈ p.support := List.mem_toFinset.mp hzp
    let pa := p.takeUntil ((z : U) : α) hzp'
    let pb := p.dropUntil ((z : U) : α) hzp'
    have hpath : (pa.append pb).IsPath := by rw [p.take_spec hzp']; exact hp
    have hprefix : ∀ w ∈ pa.support, w ∈ U := by
      intro w hw
      exact Finset.mem_union_right _ (List.mem_toFinset.mpr (p.support_takeUntil_subset hzp' hw))
    have hsuffix : ∀ w ∈ pb.support, w ∈ U := by
      intro w hw
      exact Finset.mem_union_right _ (List.mem_toFinset.mpr (p.support_dropUntil_subset hzp' hw))
    by_cases hxa : (x : α) ∈ pa.support
    · have hxb : (x : α) ∉ pb.support := by
        intro hxb
        exact hpath.ne_of_mem_support_of_append hzx.symm hxa hxb rfl
      have hbx : b ≠ (x : α) := by intro heq; exact hxb (heq ▸ pb.end_mem_support)
      obtain ⟨q, hq, hqx⟩ := hcore b hb hbx
      let r := q.append pb.reverse
      have hrU : ∀ w ∈ r.support, w ∈ U := by
        intro w hw
        have hsup : w ∈ q.support ∨ w ∈ pb.support := by
          simp only [r, Walk.support_append, List.mem_append] at hw
          rcases hw with hw | hw
          · exact Or.inl hw
          · exact Or.inr (by simpa only [Walk.support_reverse, List.mem_reverse] using
              List.mem_of_mem_tail hw)
        exact hsup.elim (hq w) (hsuffix w)
      have hrx : (x : α) ∉ r.support := by
        intro hxmem
        have hsup : (x : α) ∈ q.support ∨ (x : α) ∈ pb.support := by
          simp only [r, Walk.support_append, List.mem_append] at hxmem
          rcases hxmem with hxmem | hxmem
          · exact Or.inl hxmem
          · exact Or.inr (by simpa only [Walk.support_reverse, List.mem_reverse] using
              List.mem_of_mem_tail hxmem)
        exact hsup.elim hqx hxb
      exact reachable_induce_delete_of_walk x y' z r hrU hrx
    · have hax : a ≠ (x : α) := by intro heq; exact hxa (heq ▸ pa.start_mem_support)
      obtain ⟨q, hq, hqx⟩ := hcore a ha hax
      let r := q.append pa
      have hrU : ∀ w ∈ r.support, w ∈ U := by
        intro w hw
        have hsup : w ∈ q.support ∨ w ∈ pa.support := by
          simp only [r, Walk.support_append, List.mem_append] at hw
          exact hw.elim Or.inl (fun hw => Or.inr (List.mem_of_mem_tail hw))
        exact hsup.elim (hq w) (hprefix w)
      have hrx : (x : α) ∉ r.support := by
        intro hxmem
        have hsup : (x : α) ∈ q.support ∨ (x : α) ∈ pa.support := by
          simp only [r, Walk.support_append, List.mem_append] at hxmem
          exact hxmem.elim Or.inl (fun hw => Or.inr (List.mem_of_mem_tail hw))
        exact hsup.elim hqx hxa
      exact reachable_induce_delete_of_walk x y' z r hrU hrx

/-- Maximality forces every path between two core vertices to remain in the core. -/
lemma path_support_subset_maximal_core {G : SimpleGraph α} (K : Finset α)
    (hcard : 3 ≤ K.card) (hK : (G.induce (K : Set α)).Connected)
    (hdel : ∀ x : ↥(K : Set α),
      ((G.induce (K : Set α)).induce ({x}ᶜ : Set ↥(K : Set α))).Connected)
    (hmax : ∀ t : Finset α, K ⊆ t → 3 ≤ t.card → (G.induce (t : Set α)).Connected →
      (∀ x : ↥(t : Set α),
        ((G.induce (t : Set α)).induce ({x}ᶜ : Set ↥(t : Set α))).Connected) → t = K)
    {a b : α} (ha : a ∈ K) (hb : b ∈ K) (hab : a ≠ b)
    (p : G.Walk a b) (hp : p.IsPath) : ∀ z ∈ p.support, z ∈ K := by
  classical
  let U := K ∪ p.support.toFinset
  have hsubset : K ⊆ U := Finset.subset_union_left
  have hUcard : 3 ≤ U.card := hcard.trans (Finset.card_le_card hsubset)
  have hUconn : (G.induce (U : Set α)).Connected := by
    have hset : (U : Set α) = (K : Set α) ∪ {z | z ∈ p.support} := by
      ext z
      simp [U]
    rw [hset]
    exact induce_union_connected hK.preconnected p.connected_induce_support.preconnected
      ⟨a, ha, p.start_mem_support⟩
  have hUeq := hmax U hsubset hUcard hUconn
    (core_union_path_delete_connected K hcard hK hdel ha hb hab p hp)
  intro z hz
  have hzU : z ∈ U := Finset.mem_union_right _ (List.mem_toFinset.mpr hz)
  exact hUeq ▸ hzU

/-- Every connected outside region has at most one attachment vertex in a maximal core. -/
lemma maximal_core_unique_attachment {G : SimpleGraph α} (K : Finset α)
    (hcard : 3 ≤ K.card) (hK : (G.induce (K : Set α)).Connected)
    (hdel : ∀ x : ↥(K : Set α),
      ((G.induce (K : Set α)).induce ({x}ᶜ : Set ↥(K : Set α))).Connected)
    (hmax : ∀ t : Finset α, K ⊆ t → 3 ≤ t.card → (G.induce (t : Set α)).Connected →
      (∀ x : ↥(t : Set α),
        ((G.induce (t : Set α)).induce ({x}ᶜ : Set ↥(t : Set α))).Connected) → t = K)
    (z w : ↥((K : Set α)ᶜ)) (hr : (G.induce (K : Set α)ᶜ).Reachable z w)
    {a b : α} (ha : a ∈ K) (hb : b ∈ K) (haz : G.Adj a z) (hbw : G.Adj b w) : a = b := by
  classical
  by_contra hab
  obtain ⟨q, hq, _⟩ := hr.exists_path_of_dist
  let e : G.induce (K : Set α)ᶜ ↪g G := SimpleGraph.Embedding.induce _
  let p : G.Walk (z : α) (w : α) := q.map e.toHom
  have hp : p.IsPath := (Walk.isPath_map_iff_of_injective e.injective).mpr hq
  have hout : ∀ v ∈ p.support, v ∉ K := by
    intro v hv
    change v ∈ (q.map e.toHom).support at hv
    rw [Walk.support_map] at hv
    obtain ⟨v', _, rfl⟩ := List.mem_map.mp hv
    exact v'.property
  have hanot : a ∉ p.support := fun ha' => hout a ha' ha
  have hbnot : b ∉ p.support := fun hb' => hout b hb' hb
  let p' := p.cons haz
  have hp' : p'.IsPath := hp.cons hanot
  have hbnot' : b ∉ p'.support := by
    intro hmem
    have hmem' : b = a ∨ b ∈ p.support := by
      simpa only [p', Walk.support_cons, List.mem_cons] using hmem
    exact hmem'.elim (fun heq => hab heq.symm) hbnot
  let p'' := p'.concat hbw.symm
  have hp'' : p''.IsPath := hp'.concat hbnot' hbw.symm
  have hsub := path_support_subset_maximal_core K hcard hK hdel hmax ha hb hab p'' hp''
  have hzmem : (z : α) ∈ p''.support := by
    apply p'.support_subset_support_concat hbw.symm
    change (z : α) ∈ (p.cons haz).support
    simp only [Walk.support_cons, List.mem_cons]
    have hz0 := p.start_mem_support
    change (z : α) ∈ p.support at hz0
    exact Or.inr hz0
  exact z.property (hsub z hzmem)

/-- A set closed under taking neighbors contains every vertex reachable from it. -/
lemma reachable_mem_of_adj_closed {G : SimpleGraph α} {S : Set α}
    (hS : ∀ u ∈ S, ∀ v, G.Adj u v → v ∈ S) {u v : α}
    (hr : G.Reachable u v) (hu : u ∈ S) : v ∈ S := by
  obtain ⟨p⟩ := hr
  revert hu
  induction p with
  | nil => exact fun hu => hu
  | cons huv p ih => exact fun hu => ih (hS _ hu _ huv)

/-- A connected graph of order at least three with connected vertex deletions has
two distinct neighbors at every vertex. -/
lemma exists_two_adj_of_connected_deletions {G : SimpleGraph α}
    (hcard : 3 ≤ Fintype.card α) (hG : G.Connected)
    (hdel : ∀ x, (G.induce ({x}ᶜ : Set α)).Connected) (c : α) :
    ∃ u v : α, G.Adj c u ∧ G.Adj c v ∧ u ≠ v := by
  classical
  have hex (s : Finset α) (hs : s.card ≤ 2) : ∃ d, d ∉ s := by
    by_contra! hall
    have heq := Finset.eq_univ_of_forall hall
    rw [heq, Finset.card_univ] at hs
    omega
  obtain ⟨d, hd⟩ := hex {c} (by simp)
  have hcd : c ≠ d := by simpa [eq_comm] using hd
  obtain ⟨p⟩ := hG c d
  let u := p.snd
  have hcu : G.Adj c u := p.adj_snd (p.not_nil_of_ne hcd)
  obtain ⟨e, he⟩ := hex {c, u} Finset.card_le_two
  have hec : e ≠ c := fun hec => he (by simp [hec])
  have heu : e ≠ u := by
    exact fun heu => he (by simp [heu])
  let c' : ↥({u}ᶜ : Set α) := ⟨c, by simpa using hcu.ne⟩
  let e' : ↥({u}ᶜ : Set α) := ⟨e, by simpa using heu⟩
  obtain ⟨q⟩ := hdel u c' e'
  have hc'e' : c' ≠ e' := fun h => hec (congrArg Subtype.val h).symm
  have hcv : G.Adj c (q.snd : α) := q.adj_snd (q.not_nil_of_ne hc'e')
  refine ⟨u, q.snd, hcu, hcv, ?_⟩
  intro huv
  have hvu : (q.snd : α) ≠ u := q.snd.property
  exact hvu huv.symm

/-- If outside components have unique core contacts, each has a contact which
separates it from every other core vertex. -/
lemma outside_component_attachment {G : SimpleGraph α} (hG : G.Connected)
    (K : Finset α) (hK : K.Nonempty)
    (huniq : ∀ (z w : ↥((K : Set α)ᶜ)),
      (G.induce (K : Set α)ᶜ).Reachable z w →
      ∀ {a b : α}, a ∈ K → b ∈ K → G.Adj a z → G.Adj b w → a = b)
    (z : ↥((K : Set α)ᶜ)) :
    ∃ (c : α) (hc : c ∈ K), ∃ w : ↥((K : Set α)ᶜ),
      (G.induce (K : Set α)ᶜ).Reachable z w ∧ G.Adj c w ∧
      ∀ (v : α) (hv : v ∈ K) (hvc : v ≠ c),
        ¬ (G.induce ({c}ᶜ : Set α)).Reachable
          ⟨z, by simpa using (show (z : α) ≠ c from fun heq => z.property (heq.symm ▸ hc))⟩
          ⟨v, by simpa using hvc⟩ := by
  classical
  let C : Set α := {v | ∃ hv : v ∉ K,
    (G.induce (K : Set α)ᶜ).Reachable z ⟨v, hv⟩}
  have hzC : (z : α) ∈ C := ⟨z.property, Reachable.rfl⟩
  have hCK : ∀ v ∈ C, v ∉ K := fun v hv => hv.choose
  have hCproper : C.toFinset ≠ Finset.univ := by
    obtain ⟨k, hk⟩ := hK
    intro heq
    have hkC : k ∈ C := Set.mem_toFinset.mp (heq ▸ Finset.mem_univ k)
    exact hCK k hkC hk
  obtain ⟨c, hcC, w, hwC, hcw⟩ := hG.exists_adj_finset_compl
    (show C.toFinset.Nonempty from ⟨z, by simpa using hzC⟩) hCproper
  have hwC' : w ∈ C := by simpa using hwC
  obtain ⟨hwK, hzw⟩ := hwC'
  have hcK : c ∈ K := by
    by_contra hcK
    have hwr : (G.induce (K : Set α)ᶜ).Reachable
        (⟨w, hwK⟩ : ↥((K : Set α)ᶜ)) ⟨c, hcK⟩ :=
      (show (G.induce (K : Set α)ᶜ).Adj ⟨w, hwK⟩ ⟨c, hcK⟩ from hcw.symm).reachable
    exact hcC (by simpa using (show c ∈ C from ⟨hcK, hzw.trans hwr⟩))
  refine ⟨c, hcK, ⟨w, hwK⟩, hzw, hcw, ?_⟩
  intro v hv hvc hr
  have hclosed : ∀ u ∈ {y : ↥({c}ᶜ : Set α) | (y : α) ∈ C},
      ∀ t : ↥({c}ᶜ : Set α), (G.induce ({c}ᶜ : Set α)).Adj u t → (t : α) ∈ C := by
    intro u hu t hut
    obtain ⟨huK, hzu⟩ := hu
    by_cases htK : (t : α) ∈ K
    · have hct : c = (t : α) := huniq ⟨w, hwK⟩ ⟨u, huK⟩
        (hzw.symm.trans hzu) hcK htK hcw (show G.Adj t u from hut.symm)
      exact (t.property hct.symm).elim
    · exact ⟨htK, hzu.trans
        (show (G.induce (K : Set α)ᶜ).Adj ⟨u, huK⟩ ⟨t, htK⟩ from hut).reachable⟩
  have hvC := reachable_mem_of_adj_closed hclosed hr hzC
  exact hCK v hvC hv

/-- A shortest path has just one neighbor of its initial vertex on its support. -/
lemma adjacent_start_eq_snd_of_geodesic {G : SimpleGraph α} (hG : G.Connected)
    {c b z : α} (q : G.Walk c b) (hq : q.length = G.dist c b)
    (hz : z ∈ q.support) (hcz : G.Adj c z) : z = q.snd := by
  cases q with
  | nil =>
    have hzc : z = c := by simpa using hz
    exact (hcz.ne hzc.symm).elim
  | @cons c n b hcn q =>
    have hzq : z ∈ q.support := (List.mem_cons.mp hz).resolve_left hcz.ne.symm
    have hqt : q.length = G.dist n b :=
      length_eq_dist_of_subwalk hq (Walk.isSubwalk_cons q hcn)
    have hsum := dist_add_dist_eq_of_mem_geodesic q hqt hzq
    have htri := hG.dist_triangle (u := c) (v := z) (w := b)
    have hczd : G.dist c z = 1 := dist_eq_one_iff_adj.mpr hcz
    have hlen : G.dist c b = G.dist n b + 1 := by
      simpa only [Walk.length_cons, hqt] using hq.symm
    have hnz : G.dist n z = 0 := by omega
    simpa using (hG.dist_eq_zero_iff.mp hnz).symm

/-- Two core vertices different from a prescribed vertex remain reachable in its
ambient deletion graph. -/
lemma core_reachable_compl {G : SimpleGraph α} (K : Finset α)
    (hK : (G.induce (K : Set α)).Connected)
    (hdel : ∀ x : ↥(K : Set α),
      ((G.induce (K : Set α)).induce ({x}ᶜ : Set ↥(K : Set α))).Connected)
    (c : α) {u v : α} (hu : u ∈ K) (hv : v ∈ K) (huc : u ≠ c) (hvc : v ≠ c) :
    (G.induce ({c}ᶜ : Set α)).Reachable ⟨u, by simpa using huc⟩
      ⟨v, by simpa using hvc⟩ := by
  obtain ⟨p, _, hpc⟩ := exists_walk_in_core_avoiding K hK hdel c hu hv huc hvc
  exact ⟨p.induce ({c}ᶜ : Set α) (by
    intro z hz
    exact show z ≠ c from fun heq => hpc (heq ▸ hz))⟩

/-- The shallow geodesic at a core cut vertex meets the core only at its root;
the rest of the core lies on the other side. -/
lemma shallow_geodesic_meets_core {G : SimpleGraph α} (hG : G.Connected)
    (K : Finset α) (hcard : 3 ≤ K.card) (hK : (G.induce (K : Set α)).Connected)
    (hdel : ∀ x : ↥(K : Set α),
      ((G.induce (K : Set α)).induce ({x}ᶜ : Set ↥(K : Set α))).Connected)
    (c : α) (hc : c ∈ K) (a b : ↥({c}ᶜ : Set α))
    (q : G.Walk c (b : α)) (hq : q.length = G.dist c b)
    (hsep : ¬ (G.induce ({c}ᶜ : Set α)).Reachable a b)
    (hcover : ∀ z, z ∈ cutSide G c a ∨ z ∈ q.support) :
    (∀ z ∈ K, z ∈ cutSide G c a) ∧ (∀ z ∈ q.support, z ∈ K → z = c) := by
  classical
  obtain ⟨u, v, hcu, hcv, huv⟩ := exists_two_adj_of_connected_deletions
    (G := G.induce (K : Set α)) (by simpa using hcard) hK hdel ⟨c, hc⟩
  have hside : ∀ z ∈ K, z ∈ cutSide G c a := by
    intro z hz
    by_contra hzside
    have hzc : z ≠ c := fun heq => hzside (Or.inl heq)
    have hneighbor (w : ↥(K : Set α)) (hcw : G.Adj c w) : (w : α) = q.snd := by
      have hwc := hcw.ne.symm
      have hzw := core_reachable_compl K hK hdel c hz w.property hzc hwc
      have hwnot : (w : α) ∉ cutSide G c a := by
        rintro (hwc' | ⟨_, haw⟩)
        · exact hwc hwc'
        · exact hzside (Or.inr ⟨hzc, haw.trans hzw.symm⟩)
      exact adjacent_start_eq_snd_of_geodesic hG q hq
        ((hcover w).resolve_left hwnot) hcw
    have huq := hneighbor u hcu
    have hvq := hneighbor v hcv
    exact huv (Subtype.ext (huq.trans hvq.symm))
  refine ⟨hside, ?_⟩
  intro z hzq hzK
  by_contra hzc
  have hzb := reachable_compl_of_mem_geodesic q hq b.property hzq hzc
  rcases hside z hzK with heq | ⟨_, haz⟩
  · exact hzc heq
  · exact hsep (haz.trans hzb)

/-- Geodesics attached to a core, with no edges leaving their positive tails. -/
structure PendantGeodesics (G : SimpleGraph α) (K : Finset α) where
  endPoint : ↥(K : Set α) → α
  path : ∀ c : ↥(K : Set α), G.Walk c (endPoint c)
  geodesic : ∀ c, (path c).length = G.dist c (endPoint c)
  core_inter : ∀ c z, z ∈ (path c).support → z ∈ K → z = (c : α)
  closed : ∀ c z, z ∈ (path c).support → z ≠ (c : α) →
    ∀ w, G.Adj z w → w ∈ (path c).support
  rest : ∀ (c : ↥(K : Set α)) (z : ↥({(c : α)}ᶜ : Set α)),
    (z : α) ∉ (path c).support → ∀ (v : α) (hv : v ∈ K) (hvc : v ≠ (c : α)),
      (G.induce ({(c : α)}ᶜ : Set α)).Reachable z ⟨v, by simpa using hvc⟩
  depth_gap : ∀ c, 0 < (path c).length → ∃ a, (path c).length + 2 ≤ G.dist c a
  cover : ∀ z : α, ∃ c, z ∈ (path c).support

/-- The two-side reduction and unique attachment property give a covering family
of pendant geodesics rooted in the core, including zero-length paths. -/
lemma exists_pendant_geodesic_family {G : SimpleGraph α} (hG : G.Connected)
    (K : Finset α) (hcard : 3 ≤ K.card) (hK : (G.induce (K : Set α)).Connected)
    (hdel : ∀ x : ↥(K : Set α),
      ((G.induce (K : Set α)).induce ({x}ᶜ : Set ↥(K : Set α))).Connected)
    (huniq : ∀ (z w : ↥((K : Set α)ᶜ)),
      (G.induce (K : Set α)ᶜ).Reachable z w →
      ∀ {a b : α}, a ∈ K → b ∈ K → G.Adj a z → G.Adj b w → a = b)
    (htwo : ∀ c, ¬ (G.induce ({c}ᶜ : Set α)).Connected →
      ∃ a b : ↥({c}ᶜ : Set α), ∃ q : G.Walk c (b : α),
        q.length = G.dist c b ∧
        ¬ (G.induce ({c}ᶜ : Set α)).Reachable a b ∧
        G.dist c b + 2 ≤ G.dist c a ∧
        ∀ z, z ∈ cutSide G c a ∨ z ∈ q.support) :
    Nonempty (PendantGeodesics G K) := by
  classical
  have hpaths (c : ↥(K : Set α)) :
      ∃ (e : α) (p : G.Walk c e),
        p.length = G.dist c e ∧
        (∀ z ∈ p.support, z ∈ K → z = (c : α)) ∧
        (∀ z ∈ p.support, z ≠ (c : α) → ∀ w, G.Adj z w → w ∈ p.support) ∧
        (∀ (z : ↥({(c : α)}ᶜ : Set α)), (z : α) ∉ p.support →
          ∀ (v : α) (hv : v ∈ K) (hvc : v ≠ (c : α)),
            (G.induce ({(c : α)}ᶜ : Set α)).Reachable z ⟨v, by simpa using hvc⟩) ∧
        (0 < p.length → ∃ a, p.length + 2 ≤ G.dist c a) := by
    by_cases hc : (G.induce ({(c : α)}ᶜ : Set α)).Connected
    · refine ⟨c, Walk.nil, by simp, ?_, ?_, ?_, ?_⟩
      · intro z hz _
        simpa using hz
      · intro z hz hzc
        exact (hzc (by simpa using hz)).elim
      · intro z _ v _ hvc
        exact hc z ⟨v, by simpa using hvc⟩
      · simp
    · obtain ⟨a, b, q, hq, hsep, hgap, hcover⟩ := htwo c hc
      obtain ⟨hside, hcore⟩ := shallow_geodesic_meets_core hG K hcard hK hdel
        c c.property a b q hq hsep hcover
      refine ⟨b, q, hq, hcore, ?_, ?_, ?_⟩
      · intro z hz hzc w hzw
        by_contra hwq
        have hwside := (hcover w).resolve_right hwq
        have hwc : w ≠ (c : α) := fun heq => hwq (heq ▸ q.start_mem_support)
        have hzb := reachable_compl_of_mem_geodesic q hq b.property hz hzc
        rcases hwside with heq | ⟨_, haw⟩
        · exact hwc heq
        · have hwz : (G.induce ({(c : α)}ᶜ : Set α)).Adj
              ⟨w, by simpa using hwc⟩ ⟨z, by simpa using hzc⟩ := hzw.symm
          exact hsep (haw.trans (hwz.reachable.trans hzb))
      · intro z hzq v hv hvc
        have hzside := (hcover z).resolve_right hzq
        rcases hzside with hzc | ⟨_, haz⟩
        · exact (z.property hzc).elim
        rcases hside v hv with heq | ⟨_, hav⟩
        · exact (hvc heq).elim
        · exact haz.symm.trans hav
      · intro _
        exact ⟨a, hq ▸ hgap⟩
  choose e P hgeo hcore hclosed hrest hgap using hpaths
  refine ⟨⟨e, P, hgeo, hcore, hclosed, hrest, hgap, ?_⟩⟩
  intro z
  by_cases hzK : z ∈ K
  · exact ⟨⟨z, hzK⟩, (P ⟨z, hzK⟩).start_mem_support⟩
  · obtain ⟨c, hc, w, hzw, hcw, hsep⟩ := outside_component_attachment hG K
      (Finset.card_pos.mp (by omega)) huniq ⟨z, hzK⟩
    obtain ⟨v, _, hcv, _, _⟩ := exists_two_adj_of_connected_deletions
      (G := G.induce (K : Set α)) (by simpa using hcard) hK hdel ⟨c, hc⟩
    have hvc : (v : α) ≠ c := (show G.Adj c v from hcv).ne.symm
    refine ⟨⟨c, hc⟩, ?_⟩
    by_contra hzP
    exact hsep v v.property hvc
      (hrest ⟨c, hc⟩ ⟨z, by simpa using (show z ≠ c from fun heq => hzK (heq.symm ▸ hc))⟩
        hzP v v.property hvc)

namespace PendantGeodesics

variable {G : SimpleGraph α} {K : Finset α} (F : PendantGeodesics G K)

/-- A core of order at least three has a vertex avoiding two prescribed vertices. -/
lemma exists_core_vertex_ne_two (hcard : 3 ≤ K.card) (a b : α) :
    ∃ v : ↥(K : Set α), (v : α) ≠ a ∧ (v : α) ≠ b := by
  classical
  by_contra! hn
  have hsub : K ⊆ {a, b} := by
    intro v hv
    by_cases hva : v = a
    · simp [hva]
    · exact Finset.mem_insert_of_mem (Finset.mem_singleton.mpr (hn ⟨v, hv⟩ hva))
  have hle := Finset.card_le_card hsub
  have htwo : ({a, b} : Finset α).card ≤ 2 := Finset.card_le_two
  omega

/-- Deleting a pendant root separates its positive tail from everything off its path. -/
lemma tail_separated (c : ↥(K : Set α)) {z v : α}
    (hz : z ∈ (F.path c).support) (hzc : z ≠ (c : α))
    (hv : v ∉ (F.path c).support) :
    ¬ (G.induce ({(c : α)}ᶜ : Set α)).Reachable
      ⟨z, by simpa using hzc⟩
      ⟨v, by simpa using (show v ≠ (c : α) from fun heq => hv (heq ▸ (F.path c).start_mem_support))⟩ := by
  intro hr
  have hclosed : ∀ u ∈ {y : ↥({(c : α)}ᶜ : Set α) | (y : α) ∈ (F.path c).support},
      ∀ t, (G.induce ({(c : α)}ᶜ : Set α)).Adj u t → (t : α) ∈ (F.path c).support := by
    intro u hu t hut
    exact F.closed c u hu u.property t hut
  exact hv (reachable_mem_of_adj_closed hclosed hr hz)

/-- Every distance from the core to a pendant path passes through its root. -/
lemma dist_from_core (hG : G.Connected) (c v : ↥(K : Set α)) {z : α}
    (hz : z ∈ (F.path c).support) :
    G.dist v z = G.dist v c + G.dist c z := by
  by_cases hvc : (v : α) = (c : α)
  · simp [hvc]
  by_cases hzc : z = (c : α)
  · simp [hzc]
  have hv : (v : α) ∉ (F.path c).support := fun hv => hvc (F.core_inter c v hv v.property)
  apply dist_eq_add_of_not_reachable_compl hG hvc hzc
  exact fun hr => F.tail_separated c hz hzc hv hr.symm

/-- Distinct core roots have disjoint full pendant supports. -/
lemma support_disjoint (hG : G.Connected) {c d : ↥(K : Set α)} (hcd : c ≠ d) :
    Disjoint (F.path c).support.toFinset (F.path d).support.toFinset := by
  apply Finset.disjoint_left.mpr
  intro z hz hd
  have h₁ := F.dist_from_core hG c d (List.mem_toFinset.mp hz)
  have h₂ := F.dist_from_core hG d c (List.mem_toFinset.mp hd)
  have hcomm : G.dist (d : α) c = G.dist c d := G.dist_comm
  have hzero : G.dist (c : α) d = 0 := by omega
  exact hcd (Subtype.ext (hG.dist_eq_zero_iff.mp hzero))

/-- A pendant path has positive length precisely when its endpoint differs from its root. -/
lemma length_pos_iff (hG : G.Connected) (c : ↥(K : Set α)) :
    0 < (F.path c).length ↔ F.endPoint c ≠ (c : α) := by
  rw [F.geodesic c]
  constructor
  · intro h heq
    simp [heq] at h
  · intro h
    have hne : G.dist (c : α) (F.endPoint c) ≠ 0 :=
      fun hz => h (hG.dist_eq_zero_iff.mp hz).symm
    omega

/-- Endpoints of positive pendant paths are outside the core. -/
lemma endPoint_not_core (hG : G.Connected) (c : ↥(K : Set α))
    (hpos : 0 < (F.path c).length) : F.endPoint c ∉ K := by
  intro heK
  exact (F.length_pos_iff hG c).mp hpos
    (F.core_inter c _ (F.path c).end_mem_support heK)

include F in
/-- Every original-graph center belongs to the core. -/
lemma center_mem_core (hG : G.Connected) {v : α} (hv : G.eccent v = G.radius) : v ∈ K := by
  haveI : Nonempty α := hG.nonempty
  by_contra hvK
  obtain ⟨c, hvc⟩ := F.cover v
  have hvcne : v ≠ (c : α) := fun heq => hvK (heq.symm ▸ c.property)
  have hvdist : 0 < G.dist (c : α) v := by
    have hne : G.dist (c : α) v ≠ 0 := fun heq => hvcne (hG.dist_eq_zero_iff.mp heq).symm
    omega
  have hsum := dist_add_dist_eq_of_mem_geodesic (F.path c) (F.geodesic c) hvc
  have hpos : 0 < (F.path c).length := by rw [F.geodesic c]; omega
  obtain ⟨a, ha⟩ := F.depth_gap c hpos
  obtain ⟨f, hf⟩ := G.exists_edist_eq_eccent_of_finite (c : α)
  have hmax : G.dist (c : α) a ≤ G.dist c f :=
    ENat.toNat_le_toNat (hf ▸ G.edist_le_eccent)
      (edist_ne_top_iff_reachable.mpr (hG c f))
  have hfoff : f ∉ (F.path c).support := by
    intro hfc
    have hf_sum := dist_add_dist_eq_of_mem_geodesic (F.path c) (F.geodesic c) hfc
    rw [← F.geodesic c] at hf_sum
    omega
  have hfc : f ≠ (c : α) := fun heq => hfoff (heq ▸ (F.path c).start_mem_support)
  have hdist := dist_eq_add_of_not_reachable_compl hG hvcne hfc
    (F.tail_separated c hvc hvcne hfoff)
  have hrad : G.radius.toNat ≤ G.dist (c : α) f :=
    ENat.toNat_le_toNat (hf ▸ G.radius_le_eccent)
      (edist_ne_top_iff_reachable.mpr (hG c f))
  have hvf : G.dist v f ≤ G.radius.toNat :=
    ENat.toNat_le_toNat (hv ▸ G.edist_le_eccent)
      (G.radius_ne_top_iff.mpr hG)
  rw [G.dist_comm (u := v) (v := (c : α))] at hdist
  omega

/-- A positive pendant endpoint is a leaf of the whole graph. -/
lemma endPoint_degree_one [DecidableRel G.Adj] (hG : G.Connected) (c : ↥(K : Set α))
    (hpos : 0 < (F.path c).length) : G.degree (F.endPoint c) = 1 := by
  classical
  have hec := (F.length_pos_iff hG c).mp hpos
  let q := (F.path c).reverse
  have hq : q.length = G.dist (F.endPoint c) c := by
    simpa only [q, Walk.length_reverse, SimpleGraph.dist_comm] using F.geodesic c
  have hqn : ¬ q.Nil := q.not_nil_of_ne hec
  apply degree_eq_one_iff_existsUnique_adj.mpr
  refine ⟨q.snd, q.adj_snd hqn, ?_⟩
  intro w hew
  have hw := F.closed c _ (F.path c).end_mem_support hec w hew
  apply adjacent_start_eq_snd_of_geodesic hG q hq _ hew
  simpa only [q, Walk.support_reverse, List.mem_reverse] using hw

/-- Deleting the endpoint of a positive pendant path preserves connectedness. -/
lemma delete_endPoint_connected (hG : G.Connected) (c : ↥(K : Set α))
    (hpos : 0 < (F.path c).length) :
    (G.induce ({F.endPoint c}ᶜ : Set α)).Connected := by
  classical
  exact hG.induce_compl_singleton_of_degree_eq_one (F.endPoint_degree_one hG c hpos)

include F in
/-- Deleting an unused core root preserves connectedness. -/
lemma delete_zero_connected (hG : G.Connected) (hcard : 3 ≤ K.card)
    (hK : (G.induce (K : Set α)).Connected)
    (hdel : ∀ x : ↥(K : Set α),
      ((G.induce (K : Set α)).induce ({x}ᶜ : Set ↥(K : Set α))).Connected)
    (a : ↥(K : Set α)) (ha : (F.path a).length = 0) :
    (G.induce ({(a : α)}ᶜ : Set α)).Connected := by
  classical
  obtain ⟨u, _, hau, _, _⟩ := exists_two_adj_of_connected_deletions
    (G := G.induce (K : Set α)) (by simpa using hcard) hK hdel a
  have hua : (u : α) ≠ (a : α) := (show G.Adj a u from hau).ne.symm
  let u' : ↥({(a : α)}ᶜ : Set α) := ⟨u, by simpa using hua⟩
  rw [connected_iff_exists_forall_reachable]
  refine ⟨u', ?_⟩
  intro z
  obtain ⟨d, hzd⟩ := F.cover z
  have hda : (d : α) ≠ (a : α) := by
    intro hda
    have hdeq : d = a := Subtype.ext hda
    subst d
    have hsum := dist_add_dist_eq_of_mem_geodesic (F.path a) (F.geodesic a) hzd
    rw [← F.geodesic a, ha] at hsum
    have haz : G.dist (a : α) z = 0 := by omega
    exact z.property (hG.dist_eq_zero_iff.mp haz).symm
  obtain ⟨p, _, hpa⟩ := exists_walk_in_core_avoiding K hK hdel a
    u.property d.property hua hda
  let q := (F.path d).takeUntil (z : α) hzd
  have hqa : (a : α) ∉ q.support := by
    intro haq
    have had := F.core_inter d a
      ((F.path d).support_takeUntil_subset hzd haq) a.property
    exact hda had.symm
  let r := p.append q
  have hra : (a : α) ∉ r.support := by
    intro har
    simp only [r, Walk.support_append, List.mem_append] at har
    exact har.elim hpa (fun har => hqa (List.mem_of_mem_tail har))
  exact ⟨r.induce ({(a : α)}ᶜ : Set α) (by
    intro w hw
    exact show w ≠ (a : α) from fun heq => hra (heq ▸ hw))⟩

/-- A surviving positive tail still certifies a cut after another vertex is deleted. -/
lemma cut_after_delete (hG : G.Connected) (x : α) (c v : ↥(K : Set α))
    (hc : 0 < (F.path c).length) (hcx : (c : α) ≠ x)
    (hex : F.endPoint c ≠ x) (hvc : v ≠ c) (hvx : (v : α) ≠ x) :
    ∃ y, ¬ ((G.induce ({x}ᶜ : Set α)).induce
      ({y}ᶜ : Set ↥({x}ᶜ : Set α))).Connected := by
  have hec := (F.length_pos_iff hG c).mp hc
  have hvpath : (v : α) ∉ (F.path c).support := by
    intro hv
    exact hvc (Subtype.ext (F.core_inter c v hv v.property))
  have hsep := F.tail_separated c (F.path c).end_mem_support hec hvpath
  refine ⟨⟨c, by simpa using hcx⟩, ?_⟩
  exact not_connected_induce_delete_of_separated_pair
    (S := ({x}ᶜ : Set α)) hcx hex hvx hec
    (show (v : α) ≠ (c : α) from fun heq => hvc (Subtype.ext heq)) hsep

/-- A graph with a cut has at least one positive pendant length. -/
lemma exists_positive (hG : G.Connected) (hcard : 3 ≤ K.card)
    (hK : (G.induce (K : Set α)).Connected)
    (hdel : ∀ x : ↥(K : Set α),
      ((G.induce (K : Set α)).induce ({x}ᶜ : Set ↥(K : Set α))).Connected)
    (hcut : ∃ x, ¬ (G.induce ({x}ᶜ : Set α)).Connected) :
    ∃ c, 0 < (F.path c).length := by
  by_contra! hn
  have hall : ∀ z : α, z ∈ K := by
    intro z
    obtain ⟨c, hzc⟩ := F.cover z
    have hsum := dist_add_dist_eq_of_mem_geodesic (F.path c) (F.geodesic c) hzc
    have hlen : (F.path c).length = 0 := by have := hn c; omega
    rw [← F.geodesic c, hlen] at hsum
    have hcz : G.dist (c : α) z = 0 := by omega
    exact (hG.dist_eq_zero_iff.mp hcz) ▸ c.property
  obtain ⟨x, hx⟩ := hcut
  obtain ⟨u, hux, _⟩ := exists_core_vertex_ne_two hcard x x
  apply hx
  rw [connected_iff_exists_forall_reachable]
  refine ⟨⟨u, by simpa using hux⟩, ?_⟩
  intro z
  exact core_reachable_compl K hK hdel x u.property (hall z) hux z.property

/-- The minimal-counterexample deletion witness used to compare pendant lengths. -/
def DeletionCenters (G : SimpleGraph α) : Prop :=
  ∀ x, (G.induce ({x}ᶜ : Set α)).Connected →
    (∃ y, ¬ ((G.induce ({x}ᶜ : Set α)).induce
      ({y}ᶜ : Set ↥({x}ᶜ : Set α))).Connected) →
    ∃ c : α, c ≠ x ∧ G.eccent c = G.radius ∧ G.dist c x = G.radius.toNat ∧
      ∀ z : α, z ≠ x → G.dist c z ≤ G.radius.toNat - 1

/-- Adjacent core roots cannot have a zero length next to a positive length. -/
lemma not_zero_adj_positive (hG : G.Connected) (hcard : 3 ≤ K.card)
    (hK : (G.induce (K : Set α)).Connected)
    (hdel : ∀ x : ↥(K : Set α),
      ((G.induce (K : Set α)).induce ({x}ᶜ : Set ↥(K : Set α))).Connected)
    (hdelete : DeletionCenters G) (hr : 1 ≤ G.radius.toNat)
    (a b : ↥(K : Set α)) (hab : G.Adj a b)
    (ha : (F.path a).length = 0) (hb : 0 < (F.path b).length) : False := by
  obtain ⟨v, hva, hvb⟩ := exists_core_vertex_ne_two hcard a b
  have heba : F.endPoint b ≠ (a : α) :=
    fun heq => F.endPoint_not_core hG b hb (heq.symm ▸ a.property)
  have hcut := F.cut_after_delete hG a b v hb hab.ne.symm heba
    (fun heq => hvb (congrArg Subtype.val heq)) hva
  obtain ⟨w, _, hw, hwa, hwb⟩ := hdelete a
    (F.delete_zero_connected hG hcard hK hdel a ha) hcut
  let w' : ↥(K : Set α) := ⟨w, F.center_mem_core hG hw⟩
  have hdist := F.dist_from_core hG b w' (F.path b).end_mem_support
  rw [← F.geodesic b] at hdist
  have hfar := hwb (F.endPoint b) heba
  have htri := hG.dist_triangle (u := w) (v := (b : α)) (w := (a : α))
  have hba : G.dist (b : α) a = 1 := dist_eq_one_iff_adj.mpr hab.symm
  change G.dist w (F.endPoint b) = G.dist w b + (F.path b).length at hdist
  omega

/-- Connectedness propagates positivity from one pendant root to every core vertex. -/
lemma all_positive (hG : G.Connected) (hcard : 3 ≤ K.card)
    (hK : (G.induce (K : Set α)).Connected)
    (hdel : ∀ x : ↥(K : Set α),
      ((G.induce (K : Set α)).induce ({x}ᶜ : Set ↥(K : Set α))).Connected)
    (hdelete : DeletionCenters G) (hr : 1 ≤ G.radius.toNat)
    (hcut : ∃ x, ¬ (G.induce ({x}ᶜ : Set α)).Connected) :
    ∀ c, 0 < (F.path c).length := by
  obtain ⟨a, ha⟩ := F.exists_positive hG hcard hK hdel hcut
  have hclosed : ∀ u ∈ {c : ↥(K : Set α) | 0 < (F.path c).length},
      ∀ v, (G.induce (K : Set α)).Adj u v → 0 < (F.path v).length := by
    intro u hu v huv
    by_contra hv
    have hvzero : (F.path v).length = 0 := by omega
    exact F.not_zero_adj_positive hG hcard hK hdel hdelete hr v u huv.symm hvzero hu
  intro c
  exact reachable_mem_of_adj_closed hclosed (hK a c) ha

/-- Distinct pendant roots have distinct endpoints. -/
lemma endPoint_injective (hG : G.Connected) : Function.Injective F.endPoint := by
  intro c d heq
  by_contra hcd
  exact (Finset.disjoint_left.mp (F.support_disjoint hG hcd))
    (by simpa only [List.mem_toFinset] using (F.path c).end_mem_support)
    (by simpa only [List.mem_toFinset, heq] using (F.path d).end_mem_support)

/-- Deleting a positive endpoint gives a center witnessing that its length is
at least every neighboring pendant length. -/
lemma length_le_of_adj (hG : G.Connected) (hcard : 3 ≤ K.card)
    (hdelete : DeletionCenters G) (hr : 1 ≤ G.radius.toNat)
    (hpos : ∀ c, 0 < (F.path c).length)
    (a b : ↥(K : Set α)) (hab : G.Adj a b) :
    (F.path b).length ≤ (F.path a).length := by
  obtain ⟨d, hda, _⟩ := exists_core_vertex_ne_two hcard a a
  have hda' : d ≠ a := fun heq => hda (congrArg Subtype.val heq)
  have hxK := F.endPoint_not_core hG a (hpos a)
  have hdxa : (d : α) ≠ F.endPoint a := fun heq => hxK (heq ▸ d.property)
  have haxa : (a : α) ≠ F.endPoint a := fun heq => hxK (heq ▸ a.property)
  have hed : F.endPoint d ≠ F.endPoint a := fun heq => hda' (F.endPoint_injective hG heq)
  have hcut := F.cut_after_delete hG (F.endPoint a) d a (hpos d) hdxa hed hda'.symm haxa
  obtain ⟨w, _, hw, hwa, hwb⟩ := hdelete (F.endPoint a)
    (F.delete_endPoint_connected hG a (hpos a)) hcut
  let w' : ↥(K : Set α) := ⟨w, F.center_mem_core hG hw⟩
  have hdistA := F.dist_from_core hG a w' (F.path a).end_mem_support
  have hdistB := F.dist_from_core hG b w' (F.path b).end_mem_support
  rw [← F.geodesic a] at hdistA
  rw [← F.geodesic b] at hdistB
  have heba : F.endPoint b ≠ F.endPoint a := fun heq =>
    hab.ne (congrArg Subtype.val (F.endPoint_injective hG heq)).symm
  have hfar := hwb (F.endPoint b) heba
  have htri := hG.dist_triangle (u := w) (v := (b : α)) (w := (a : α))
  have hba : G.dist (b : α) a = 1 := dist_eq_one_iff_adj.mpr hab.symm
  change G.dist w (F.endPoint a) = G.dist w a + (F.path a).length at hdistA
  change G.dist w (F.endPoint b) = G.dist w b + (F.path b).length at hdistB
  omega

/-- All positive pendant paths in the minimal counterexample have one common length. -/
lemma common_length (hG : G.Connected) (hcard : 3 ≤ K.card)
    (hK : (G.induce (K : Set α)).Connected)
    (hdelete : DeletionCenters G) (hr : 1 ≤ G.radius.toNat)
    (hpos : ∀ c, 0 < (F.path c).length) :
    ∃ L, 0 < L ∧ ∀ c, (F.path c).length = L := by
  haveI : Nonempty ↥(K : Set α) := hK.nonempty
  let a : ↥(K : Set α) := Classical.choice inferInstance
  refine ⟨(F.path a).length, hpos a, ?_⟩
  have hedge (u v : ↥(K : Set α)) (huv : (G.induce (K : Set α)).Adj u v) :
      (F.path u).length = (F.path v).length :=
    Nat.le_antisymm (F.length_le_of_adj hG hcard hdelete hr hpos v u huv.symm)
      (F.length_le_of_adj hG hcard hdelete hr hpos u v huv)
  have hclosed : ∀ u ∈ {c : ↥(K : Set α) | (F.path c).length = (F.path a).length},
      ∀ v, (G.induce (K : Set α)).Adj u v → (F.path v).length = (F.path a).length := by
    intro u hu v huv
    exact (hedge u v huv).symm.trans hu
  intro c
  exact reachable_mem_of_adj_closed hclosed (hK a c) rfl

/-- Equal pendant lengths give the radius comparison needed for the final count. -/
lemma radius_le_core_radius_add (hG : G.Connected)
    (hK : (G.induce (K : Set α)).Connected) (L : ℕ)
    (hLen : ∀ c, (F.path c).length = L) :
    G.radius.toNat ≤ (G.induce (K : Set α)).radius.toNat + L := by
  classical
  haveI : Nonempty α := hG.nonempty
  haveI : Nonempty ↥(K : Set α) := hK.nonempty
  let H := G.induce (K : Set α)
  obtain ⟨v, hv⟩ := H.exists_eccent_eq_radius
  obtain ⟨z, hz⟩ := G.exists_edist_eq_eccent_of_finite (v : α)
  obtain ⟨c, hzc⟩ := F.cover z
  have hdist := F.dist_from_core hG c v hzc
  have hsum := dist_add_dist_eq_of_mem_geodesic (F.path c) (F.geodesic c) hzc
  rw [← F.geodesic c, hLen c] at hsum
  obtain ⟨p, hp⟩ := hK.exists_walk_length_eq_dist v c
  have hmap := G.dist_le (p.map (SimpleGraph.Embedding.induce (K : Set α)).toHom)
  rw [Walk.length_map, hp] at hmap
  change G.dist (v : α) c ≤ H.dist v c at hmap
  have hvc : H.dist v c ≤ H.radius.toNat :=
    ENat.toNat_le_toNat (hv ▸ H.edist_le_eccent) (H.radius_ne_top_iff.mpr hK)
  have hrad : G.radius.toNat ≤ G.dist (v : α) z :=
    ENat.toNat_le_toNat (hz ▸ G.radius_le_eccent)
      (edist_ne_top_iff_reachable.mpr (hG v z))
  dsimp only [H] at hmap hvc
  omega

set_option maxHeartbeats 800000 in
/-- Adjoining the pendant paths at the vertices of an induced core tree gives
an induced tree whose order is multiplied by the common path order. -/
lemma lift_induced_tree (hG : G.Connected) (L : ℕ)
    (hLen : ∀ c, (F.path c).length = L)
    (s : Finset ↥(K : Set α))
    (hs : ((G.induce (K : Set α)).induce (s : Set ↥(K : Set α))).IsTree) :
    s.card * (L + 1) ≤ largestInducedTreeSize G := by
  classical
  let B : Finset α := s.image Subtype.val
  let f : ↥(s : Set ↥(K : Set α)) → ↥(B : Set α) := fun x =>
    ⟨((x : ↥(K : Set α)) : α), Finset.mem_image.mpr ⟨x, x.property, rfl⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · intro x y hxy
      have hval : ((x : ↥(K : Set α)) : α) = ((y : ↥(K : Set α)) : α) :=
        congrArg (fun z : ↥(B : Set α) => (z : α)) hxy
      exact Subtype.ext (Subtype.ext hval)
    · intro y
      obtain ⟨c, hc, hcy⟩ := Finset.mem_image.mp y.property
      exact ⟨⟨c, hc⟩, Subtype.ext hcy⟩
  let i : ((G.induce (K : Set α)).induce (s : Set ↥(K : Set α))) ≃g
      G.induce (B : Set α) :=
    { Equiv.ofBijective f hf with map_rel_iff' := by intro x y; rfl }
  have hB : (G.induce (B : Set α)).IsTree := i.isTree_iff.mp hs
  let U (t : Finset ↥(K : Set α)) : Finset α :=
    B ∪ t.biUnion (fun c => (F.path c).support.toFinset)
  have hUt : ∀ t : Finset ↥(K : Set α), t ⊆ s → (G.induce (U t : Set α)).IsTree := by
    intro t
    induction t using Finset.induction_on with
    | empty =>
      intro _
      have hUB : U ∅ = B := by simp [U]
      rw [hUB]
      exact hB
    | @insert c t hct ih =>
      intro hts
      have hcs : c ∈ s := hts (Finset.mem_insert_self _ _)
      have hts' : t ⊆ s := fun d hd => hts (Finset.mem_insert_of_mem hd)
      have hroot : (c : α) ∈ U t := Finset.mem_union_left _
        (Finset.mem_image.mpr ⟨c, hcs, rfl⟩)
      have hinter : ∀ z ∈ (F.path c).support, z ∈ U t → z = (c : α) := by
        intro z hz hzU
        rcases Finset.mem_union.mp hzU with hzB | hzt
        · obtain ⟨d, _, hdz⟩ := Finset.mem_image.mp hzB
          exact F.core_inter c z hz (hdz ▸ d.property)
        · obtain ⟨d, hd, hzd⟩ := Finset.mem_biUnion.mp hzt
          have hcd : c ≠ d := fun heq => hct (heq.symm ▸ hd)
          exact ((Finset.disjoint_left.mp (F.support_disjoint hG hcd))
            (List.mem_toFinset.mpr hz) hzd).elim
      have hrev : (F.path c).reverse.length = G.dist (F.endPoint c) c := by
        simpa only [Walk.length_reverse, SimpleGraph.dist_comm] using F.geodesic c
      have hnew := induce_union_geodesic_isTree hG (F.path c).reverse hrev (U t)
        (ih hts') hroot
        (by intro z hz hzu; exact hinter z (by simpa using hz) hzu)
        (by
          intro z hz hzc w hw hzw
          exact hinter w (F.closed c z (by simpa using hz) hzc w hzw) hw)
      have hset : U (insert c t) = (F.path c).reverse.support.toFinset ∪ U t := by
        ext z
        simp [U, or_assoc, or_comm, or_left_comm]
      rw [hset]
      exact hnew
  let T := s.biUnion (fun c => (F.path c).support.toFinset)
  have hUT : U s = T := by
    apply Finset.union_eq_right.mpr
    intro z hz
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hz
    exact Finset.mem_biUnion.mpr ⟨c, hc, List.mem_toFinset.mpr (F.path c).start_mem_support⟩
  have hT : (G.induce (T : Set α)).IsTree := hUT ▸ hUt s Finset.Subset.rfl
  have hcardpath (c : ↥(K : Set α)) : (F.path c).support.toFinset.card = L + 1 := by
    rw [List.toFinset_card_of_nodup ((F.path c).isPath_of_length_eq_dist
      (F.geodesic c)).support_nodup, Walk.length_support, hLen c]
  have hcard : T.card = s.card * (L + 1) := by
    rw [Finset.card_biUnion]
    · simp only [hcardpath, Finset.sum_const, smul_eq_mul]
    · intro c hc d hd hcd
      exact F.support_disjoint hG hcd
  rw [← hcard]
  exact card_le_largestInducedTreeSize hT

end PendantGeodesics

/-- The cut-vertex bound, by induction on graph order. -/
lemma two_mul_radius_le_largestInducedTreeSize_of_cut_vertex {G : SimpleGraph α}
    (hG : G.Connected) (hcut : ∃ x, ¬ (G.induce ({x}ᶜ : Set α)).Connected) :
    2 * G.radius.toNat ≤ largestInducedTreeSize G := by
  classical
  induction hn : Fintype.card α using Nat.strong_induction_on generalizing α with
  | h n ih =>
    haveI : Nonempty α := hG.nonempty
    have htree := radius_add_one_le_largestInducedTreeSize hG
    by_cases hr : G.radius.toNat ≤ 1
    · omega
    have hr : 2 ≤ G.radius.toNat := by omega
    by_cases hT : G.IsTree
    · exact two_mul_radius_le_largestInducedTreeSize_of_isTree hT
    by_contra hbound
    have hlt : largestInducedTreeSize G < 2 * G.radius.toNat := by omega
    have hsmall (S : Set α) (hproper : S ≠ Set.univ) (hS : (G.induce S).Connected)
        (hcutS : ∃ x, ¬ ((G.induce S).induce ({x}ᶜ : Set S)).Connected) :
        2 * (G.induce S).radius.toNat ≤ largestInducedTreeSize (G.induce S) := by
      have hmiss : ∃ x : α, x ∉ S := by
        by_contra! hall
        exact hproper (Set.eq_univ_of_forall hall)
      obtain ⟨x, hx⟩ := hmiss
      have hcard : Fintype.card S < n := by
        rw [← hn]
        exact Fintype.card_subtype_lt hx
      exact ih _ hcard hS hcutS rfl
    have hdelete (x : α) (hx : (G.induce ({x}ᶜ : Set α)).Connected)
        (hcutx : ∃ y, ¬ ((G.induce ({x}ᶜ : Set α)).induce ({y}ᶜ : Set ↥({x}ᶜ : Set α))).Connected) :
        ∃ c : α, c ≠ x ∧ G.eccent c = G.radius ∧ G.dist c x = G.radius.toNat ∧
          ∀ z : α, z ≠ x → G.dist c z ≤ G.radius.toNat - 1 := by
      have hproper : ({x}ᶜ : Set α) ≠ Set.univ := by
        intro heq
        have hxmem : x ∈ ({x}ᶜ : Set α) := heq ▸ Set.mem_univ x
        simpa using hxmem
      have hboundH := hsmall ({x}ᶜ : Set α) hproper hx hcutx
      have htrans := largestInducedTreeSize_induce_le G ({x}ᶜ : Set α)
      have hdrop : (G.induce ({x}ᶜ : Set α)).radius.toNat ≤ G.radius.toNat - 1 := by omega
      exact radius_drop_witness hG x hx (by omega) hdrop
    have htwosides (c : α) (hc : ¬ (G.induce ({c}ᶜ : Set α)).Connected) :=
      cut_vertex_two_side_reduction hG hr hlt (fun S _ => hsmall S) c hc
    obtain ⟨c, hc⟩ := hcut
    obtain ⟨a, b, q, hq, hsep, hgap, hcover⟩ := htwosides c hc
    have hcyc : ¬ G.IsAcyclic := fun hacyc => hT ⟨hG, hacyc⟩
    obtain ⟨K, hKcard, hKconn, hKdel, hKmax⟩ := exists_maximal_vertex_core hcyc
    have hKne : K.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨F⟩ := exists_pendant_geodesic_family hG K hKcard hKconn hKdel
      (fun z w hzw _ _ ha hb haz hbw =>
        maximal_core_unique_attachment K hKcard hKconn hKdel hKmax z w hzw ha hb haz hbw)
      htwosides
    have hpos := F.all_positive hG hKcard hKconn hKdel hdelete (by omega) ⟨c, hc⟩
    obtain ⟨L, hL, hLen⟩ := F.common_length hG hKcard hKconn hdelete (by omega) hpos
    let H := G.induce (K : Set α)
    haveI : Nonempty ↥(K : Set α) := hKconn.nonempty
    let v : ↥(K : Set α) := Classical.choice inferInstance
    obtain ⟨t, _, _, ht⟩ := hKconn.exists_induced_tree_containing_pair v v
    obtain ⟨S, _, hS, hSmax⟩ := H.exists_maximum_induced_tree_containing ∅
      ⟨t, Finset.empty_subset _, ht⟩
    have hcard : largestInducedTreeSize H = S.card := by
      apply le_antisymm
      · apply csSup_le'
        rintro m ⟨T, rfl, hT⟩
        exact hSmax T (Finset.empty_subset _) hT
      · exact card_le_largestInducedTreeSize hS
    have hlift := F.lift_induced_tree hG L hLen S hS
    rw [← hcard] at hlift
    have hrad := F.radius_le_core_radius_add hG hKconn L hLen
    change G.radius.toNat ≤ H.radius.toNat + L at hrad
    have hchung := chung_induced_tree_bound (G := H) hKconn
    obtain ⟨u, w, hvu, _, _⟩ := exists_two_adj_of_connected_deletions
      (G := H) (by simpa using hKcard) hKconn hKdel v
    have htwo : 2 ≤ largestInducedTreeSize H := by
      have hedge := dist_add_one_le_largestInducedTreeSize (hKconn v u)
      rw [dist_eq_one_iff_adj.mpr hvu] at hedge
      exact hedge
    by_cases hs : H.radius.toNat ≤ 1
    · have hmul := Nat.mul_le_mul_right (L + 1) htwo
      omega
    · have hthree : 3 ≤ largestInducedTreeSize H := by omega
      have hmul := Nat.mul_le_mul_right L hthree
      have hcount : 2 * G.radius.toNat ≤ largestInducedTreeSize H * (L + 1) := by
        rw [Nat.mul_add, Nat.mul_one]
        omega
      omega

/-- **WOWII Conjecture 84.** For a finite simple connected graph `G` with positive minimum
degree, `tree(G) ≥ 2 · rad(G) / δ(G)`. -/
theorem conjecture84_proof {β : Type*} [Fintype β] [DecidableEq β] [Nontrivial β]
    (G : SimpleGraph β) [DecidableRel G.Adj]
    (h : G.Connected) (hδ : 0 < G.minDegree) :
    2 * (G.radius.toNat : ℝ) / (G.minDegree : ℝ) ≤ (largestInducedTreeSize G : ℝ) := by
  have htree := radius_add_one_le_largestInducedTreeSize h
  have htreeR : (G.radius.toNat : ℝ) + 1 ≤ (largestInducedTreeSize G : ℝ) := by
    exact_mod_cast htree
  have hδR : (0 : ℝ) < G.minDegree := by exact_mod_cast hδ
  apply (div_le_iff₀ hδR).2
  by_cases htwo : 2 ≤ G.minDegree
  · have htwoR : (2 : ℝ) ≤ G.minDegree := by exact_mod_cast htwo
    nlinarith [show (0 : ℝ) ≤ (G.radius.toNat : ℝ) from Nat.cast_nonneg _,
      show (0 : ℝ) ≤ (largestInducedTreeSize G : ℝ) from Nat.cast_nonneg _]
  have hδone : G.minDegree = 1 := by omega
  rw [hδone, Nat.cast_one, mul_one]
  by_cases hr : G.radius.toNat ≤ 1
  · have hrR : (G.radius.toNat : ℝ) ≤ 1 := by exact_mod_cast hr
    linarith
  have hr : 2 ≤ G.radius.toNat := by omega
  obtain ⟨u, hu⟩ := G.exists_minimal_degree_vertex
  have hleaf : G.degree u = 1 := hu.symm.trans hδone
  have hmore := radius_add_two_le_largestInducedTreeSize_of_leaf h hleaf hr
  by_cases hr2 : G.radius.toNat ≤ 2
  · have hfinal : 2 * G.radius.toNat ≤ largestInducedTreeSize G := by omega
    exact_mod_cast hfinal
  have hcard : 3 ≤ Fintype.card β := by
    have hle := largestInducedTreeSize_le_card G
    omega
  obtain ⟨v, hv⟩ := exists_cut_vertex_of_minDegree_eq_one hδone hcard
  by_cases hT : G.IsTree
  · have hbound := two_mul_radius_le_largestInducedTreeSize_of_isTree hT
    exact_mod_cast hbound
  have hbound := two_mul_radius_le_largestInducedTreeSize_of_cut_vertex h ⟨v, hv⟩
  exact_mod_cast hbound

end WrittenOnTheWallII.GraphConjecture84

theorem OMA.solution : type_of% @WrittenOnTheWallII.GraphConjecture84.conjecture84 :=
  @WrittenOnTheWallII.GraphConjecture84.conjecture84_proof
