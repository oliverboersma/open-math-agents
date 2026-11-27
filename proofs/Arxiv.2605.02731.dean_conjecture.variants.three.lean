import FormalConjectures.Arxiv.«2605.02731».DeanCycles

/-!
# Cycles of length divisible by 3 in graphs of minimum degree at least 3

We prove the `k = 3` case of Dean's conjecture (Chen and Saito, 1994): every finite simple graph
`G` with `3 ≤ G.minDegree` contains a cycle whose length is divisible by `3`.

## Proof outline
1. **Two-terminal modulo-3 paths (`two_paths_mod3_z`)**: If `4 ≤ Fintype.card W`, `x ≠ y`,
   `addEdge G x y` is `2`-connected, and every vertex `v ∉ {x, y, z}` has `3 ≤ G.degree v`,
   then `G` contains two simple `(x, y)`-paths whose lengths are incongruent modulo `3`.
2. **Chen-Saito one-deficient theorem (`one_deficient`)**: Every connected graph `G` on at least
   `3` vertices with at most one vertex `r` of degree `< 3` contains a cycle of length `0 mod 3`.
   A minimal counterexample is `2`-connected, has no essential `2`-vertex cut (by `two_paths_mod3_z`),
   contains no `3`-cycle or `4`-cycle (by maximal `K_{2, t}` contraction and `two_paths_mod3_z`),
   and therefore contains a non-separating induced cycle `C` in `G - r` of length `m ≥ 5` (`3 ∤ m`).
   Taking a spanning tree `T` of `G - C`, the `4`-point tree condition (for `m ≡ 1 mod 3`) and
   tree Helly property on five diagonal paths (for `m ≡ 2 mod 3`) force a `0 mod 3` cycle.
3. **Main theorem (`prove_dean_three`)**: Restricting `G` (`3 ≤ G.minDegree`) to a connected
   component preserves `∀ v, 3 ≤ degree v` and `4 ≤ card`, yielding a `0 mod 3` cycle.
-/

namespace DeanThreeProof

open SimpleGraph

/- ### Section 1: Graph operations, walk lifting, and cycle helpers -/

def HasMod3Cycle {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ (v : V) (w : G.Walk v v), w.IsCycle ∧ 3 ∣ w.length

lemma hasMod3Cycle_iff_cycleLengths {V : Type*} (G : SimpleGraph V) :
    (∃ m ∈ G.cycleLengths, 3 ∣ m) ↔ HasMod3Cycle G := by
  constructor
  · rintro ⟨m, ⟨v, w, hw, rfl⟩, hm⟩
    exact ⟨v, w, hw, hm⟩
  · rintro ⟨v, w, hw, hm⟩
    exact ⟨w.length, ⟨v, w, hw, rfl⟩, hm⟩

lemma HasMod3Cycle.mono {V : Type*} {G H : SimpleGraph V} (hle : G ≤ H) (h : HasMod3Cycle G) :
    HasMod3Cycle H := by
  rcases h with ⟨v, w, hw, hm⟩
  refine ⟨v, w.mapLe hle, ?_, by simpa using hm⟩
  exact Walk.IsCycle.map Function.injective_id hw

lemma HasMod3Cycle.of_embedding {U V : Type*} {G : SimpleGraph U} {H : SimpleGraph V}
    (f : G ↪g H) (h : HasMod3Cycle G) : HasMod3Cycle H := by
  rcases h with ⟨v, w, hw, hm⟩
  refine ⟨f v, w.map f.toHom, hw.map f.injective, by simpa using hm⟩

def addEdge {W : Type*} (G : SimpleGraph W) (x y : W) : SimpleGraph W where
  Adj a b := G.Adj a b ∨ (x ≠ y ∧ ((a = x ∧ b = y) ∨ (a = y ∧ b = x)))
  symm := ⟨fun _ _ h ↦ by
    rcases h with h | ⟨hne, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
    · exact Or.inl h.symm
    · exact Or.inr ⟨hne, Or.inr ⟨rfl, rfl⟩⟩
    · exact Or.inr ⟨hne, Or.inl ⟨rfl, rfl⟩⟩⟩
  loopless := ⟨fun a h ↦ by
    rcases h with h | ⟨hne, ⟨rfl, h2⟩ | ⟨rfl, h2⟩⟩
    · exact G.ne_of_adj h rfl
    · exact hne h2
    · exact hne h2.symm⟩

instance instDecidableRelAddEdge {W : Type*} [DecidableEq W] (G : SimpleGraph W)
    [DecidableRel G.Adj] (x y : W) : DecidableRel (addEdge G x y).Adj :=
  fun a b ↦ inferInstanceAs (Decidable (G.Adj a b ∨ _))

lemma le_addEdge {W : Type*} (G : SimpleGraph W) (x y : W) : G ≤ addEdge G x y :=
  fun _ _ h ↦ Or.inl h

lemma addEdge_adj_self {W : Type*} (G : SimpleGraph W) {x y : W} (hxy : x ≠ y) :
    (addEdge G x y).Adj x y :=
  Or.inr ⟨hxy, Or.inl ⟨rfl, rfl⟩⟩

def delEdge {W : Type*} (G : SimpleGraph W) (x y : W) : SimpleGraph W where
  Adj a b := G.Adj a b ∧ ¬((a = x ∧ b = y) ∨ (a = y ∧ b = x))
  symm := ⟨fun _ _ h ↦ ⟨h.1.symm, by tauto⟩⟩
  loopless := ⟨fun a h ↦ G.ne_of_adj h.1 rfl⟩

instance instDecidableRelDelEdge {W : Type*} [DecidableEq W] (G : SimpleGraph W)
    [DecidableRel G.Adj] (x y : W) : DecidableRel (delEdge G x y).Adj :=
  fun a b ↦ inferInstanceAs (Decidable (G.Adj a b ∧ _))

lemma delEdge_le {W : Type*} (G : SimpleGraph W) (x y : W) : delEdge G x y ≤ G :=
  fun _ _ h ↦ h.1

lemma addEdge_delEdge_eq {W : Type*} (G : SimpleGraph W) {x y : W} (hxy : x ≠ y) :
    addEdge (delEdge G x y) x y = addEdge G x y := by
  ext a b
  simp only [addEdge, delEdge]
  by_cases h : (a = x ∧ b = y) ∨ (a = y ∧ b = x)
  · simp [h, hxy]
  · simp [h]

lemma degree_delEdge_eq {W : Type*} [Fintype W] [DecidableEq W] (G : SimpleGraph W)
    [DecidableRel G.Adj] {x y v : W} (hvx : v ≠ x) (hvy : v ≠ y) :
    (delEdge G x y).degree v = G.degree v := by
  simp only [← card_neighborFinset_eq_degree]
  congr 1
  ext w
  rw [SimpleGraph.mem_neighborFinset, SimpleGraph.mem_neighborFinset]
  change (G.Adj v w ∧ ¬((v = x ∧ w = y) ∨ (v = y ∧ w = x))) ↔ G.Adj v w
  tauto

lemma edgeFinset_delEdge_lt {W : Type*} [Fintype W] [DecidableEq W] (G : SimpleGraph W)
    [DecidableRel G.Adj] {x y : W} (hadj : G.Adj x y) :
    (delEdge G x y).edgeFinset.card < G.edgeFinset.card := by
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · refine ⟨s(x, y), ?_, ?_⟩
    · rw [SimpleGraph.mem_edgeFinset]
      exact hadj
    · rw [SimpleGraph.mem_edgeFinset]
      change ¬(G.Adj x y ∧ ¬((x = x ∧ y = y) ∨ (x = y ∧ y = x)))
      tauto
  · intro e he
    rcases Sym2.mk_surjective e with ⟨a, b, rfl⟩
    rw [SimpleGraph.mem_edgeFinset] at he ⊢
    exact he.1

def IsTwoConn {W : Type*} (G : SimpleGraph W) : Prop :=
  G.Connected ∧ ∀ c : W, (G.induce {v : W | v ≠ c}).Connected

lemma IsTwoConn.mono {W : Type*} {G H : SimpleGraph W} (hle : G ≤ H) (h : IsTwoConn G) :
    IsTwoConn H := by
  refine ⟨h.1.mono hle, fun c ↦ ?_⟩
  exact (h.2 c).mono (fun a b hab ↦ hle hab)

lemma support_eq_cons_tail {W : Type*} {G : SimpleGraph W} {u v : W} (p : G.Walk u v) :
    p.support = u :: p.support.tail := by
  cases p <;> rfl

lemma one_le_length_of_ne {W : Type*} {G : SimpleGraph W} {u v : W} (huv : u ≠ v)
    (p : G.Walk u v) : 1 ≤ p.length := by
  cases p with
  | nil => exact (huv rfl).elim
  | cons _ _ => simp

lemma induce_adj_val {W : Type*} {G : SimpleGraph W} {U : Set W}
    {u v : {w : W // w ∈ U}} (h : (G.induce U).Adj u v) : G.Adj u.1 v.1 := h

def liftWalk {W : Type*} {G : SimpleGraph W} {U : Set W} :
    ∀ {a b : {v : W // v ∈ U}}, (G.induce U).Walk a b → G.Walk a.1 b.1
  | _, _, .nil => .nil
  | _, _, .cons hadj rest => .cons (induce_adj_val hadj) (liftWalk rest)

@[simp]
lemma length_liftWalk {W : Type*} {G : SimpleGraph W} {U : Set W} {a b : {v : W // v ∈ U}}
    (p : (G.induce U).Walk a b) : (liftWalk p).length = p.length := by
  induction p with
  | nil => rfl
  | cons _ _ ih =>
    dsimp only [liftWalk]
    rw [Walk.length_cons, Walk.length_cons, ih]

lemma support_liftWalk_subset {W : Type*} {G : SimpleGraph W} {U : Set W}
    {a b : {v : W // v ∈ U}} (p : (G.induce U).Walk a b) :
    ∀ w ∈ (liftWalk p).support, w ∈ U := by
  induction p with
  | @nil u =>
    intro w hw
    dsimp only [liftWalk] at hw
    simp only [Walk.support_nil, List.mem_singleton] at hw
    subst hw
    exact u.2
  | @cons u _ _ _ rest ih =>
    intro w hw
    dsimp only [liftWalk] at hw
    simp only [Walk.support_cons, List.mem_cons] at hw
    rcases hw with rfl | hw
    · exact u.2
    · exact ih w hw

lemma support_liftWalk_mem {W : Type*} {G : SimpleGraph W} {U : Set W}
    {a b : {v : W // v ∈ U}} (p : (G.induce U).Walk a b) :
    ∀ w ∈ (liftWalk p).support, ∃ hw : w ∈ U, (⟨w, hw⟩ : {v : W // v ∈ U}) ∈ p.support := by
  induction p with
  | @nil u =>
    intro w hw
    dsimp only [liftWalk] at hw
    simp only [Walk.support_nil, List.mem_singleton] at hw
    subst hw
    exact ⟨u.2, Walk.start_mem_support _⟩
  | @cons u _ _ _ rest ih =>
    intro w hw
    dsimp only [liftWalk] at hw
    simp only [Walk.support_cons, List.mem_cons] at hw
    rcases hw with rfl | hw
    · exact ⟨u.2, Walk.start_mem_support _⟩
    · obtain ⟨hwU, hwm⟩ := ih w hw
      exact ⟨hwU, List.mem_cons_of_mem _ hwm⟩

lemma isPath_liftWalk {W : Type*} {G : SimpleGraph W} {U : Set W} {a b : {v : W // v ∈ U}}
    {p : (G.induce U).Walk a b} (hp : p.IsPath) : (liftWalk p).IsPath := by
  induction p with
  | nil => exact Walk.IsPath.nil
  | @cons u _ _ hadj rest ih =>
    have hnd := hp.support_nodup
    simp only [Walk.support_cons, List.nodup_cons] at hnd
    apply Walk.IsPath.cons (ih hp.of_cons)
    intro hum
    obtain ⟨huU, hm⟩ := support_liftWalk_mem rest u.1 hum
    have heq : (⟨u.1, huU⟩ : {v : W // v ∈ U}) = u := Subtype.ext rfl
    exact hnd.1 (heq ▸ hm)

def pushWalk {W : Type*} {G : SimpleGraph W} {U : Set W} :
    ∀ {a b : W} (ha : a ∈ U) (hb : b ∈ U) (p : G.Walk a b),
      (∀ w ∈ p.support, w ∈ U) → (G.induce U).Walk ⟨a, ha⟩ ⟨b, hb⟩
  | _, _, _, _, .nil, _ => .nil
  | _, _, ha, hb, .cons (v := c) hadj rest, hmem =>
    let hc : c ∈ U := hmem c (by simp)
    let hadj' : (G.induce U).Adj ⟨_, ha⟩ ⟨c, hc⟩ := hadj
    .cons hadj' (pushWalk hc hb rest (fun w hw ↦ hmem w (by simp [hw])))

@[simp]
lemma liftWalk_pushWalk {W : Type*} {G : SimpleGraph W} {U : Set W} {a b : W}
    (ha : a ∈ U) (hb : b ∈ U) (p : G.Walk a b) (hp : ∀ w ∈ p.support, w ∈ U) :
    liftWalk (pushWalk ha hb p hp) = p := by
  induction p with
  | nil => rfl
  | cons _ _ ih =>
    dsimp only [pushWalk, liftWalk]
    congr 1
    exact ih _ _ _

@[simp]
lemma length_pushWalk {W : Type*} {G : SimpleGraph W} {U : Set W} {a b : W}
    (ha : a ∈ U) (hb : b ∈ U) (p : G.Walk a b) (hp : ∀ w ∈ p.support, w ∈ U) :
    (pushWalk ha hb p hp).length = p.length := by
  rw [← length_liftWalk (pushWalk ha hb p hp), liftWalk_pushWalk]

lemma reachable_induce_iff {W : Type*} {G : SimpleGraph W} {U : Set W} {a b : W}
    (ha : a ∈ U) (hb : b ∈ U) :
    (G.induce U).Reachable ⟨a, ha⟩ ⟨b, hb⟩ ↔
      ∃ p : G.Walk a b, ∀ w ∈ p.support, w ∈ U := by
  constructor
  · rintro ⟨p⟩
    exact ⟨liftWalk p, support_liftWalk_subset p⟩
  · rintro ⟨p, hp⟩
    exact ⟨pushWalk ha hb p hp⟩

lemma connected_induce_of_base {W : Type*} {G : SimpleGraph W} {U : Set W} (b : W) (hb : b ∈ U)
    (hreach : ∀ a (ha : a ∈ U), (G.induce U).Reachable ⟨b, hb⟩ ⟨a, ha⟩) :
    (G.induce U).Connected :=
  @Connected.mk _ (G.induce U)
    (fun ⟨x, hx⟩ ⟨y, hy⟩ ↦ (hreach x hx).symm.trans (hreach y hy)) ⟨⟨b, hb⟩⟩

lemma IsTwoConn.two_le_degree {W : Type*} [Fintype W] [DecidableEq W] {G : SimpleGraph W}
    [DecidableRel G.Adj] (hcard : 3 ≤ Fintype.card W) (h2 : IsTwoConn G) (v : W) :
    2 ≤ G.degree v := by
  by_contra hlt
  have hle1 : (G.neighborFinset v).card ≤ 1 := by
    rw [card_neighborFinset_eq_degree]
    omega
  rcases Nat.eq_zero_or_pos (G.neighborFinset v).card with h0 | hpos
  · have hex : ∃ w : W, w ≠ v := by
      by_contra hall
      push Not at hall
      have hsub : Fintype.card W ≤ 1 :=
        Fintype.card_le_one_iff.mpr (fun a b ↦ by rw [hall a, hall b])
      omega
    rcases hex with ⟨w, hwv⟩
    obtain ⟨p⟩ := h2.1 v w
    cases p with
    | nil => exact hwv rfl
    | cons hadj _ =>
      have hm : _ ∈ G.neighborFinset v := (G.mem_neighborFinset _ _).mpr hadj
      rw [Finset.card_eq_zero.mp h0] at hm
      simp at hm
  · have hc1 : (G.neighborFinset v).card = 1 := by omega
    rcases Finset.card_eq_one.mp hc1 with ⟨u, hu⟩
    have hex : ∃ w : W, w ≠ v ∧ w ≠ u := by
      have hsub : ({v, u} : Finset W).card ≤ 2 := Finset.card_le_two
      obtain ⟨w, _, hw⟩ := Finset.exists_mem_notMem_of_card_lt_card
        (s := {v, u}) (t := Finset.univ) (by simp; omega)
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hw
      exact ⟨w, hw⟩
    rcases hex with ⟨w, hwv, hwu⟩
    have hv_ne_u : v ≠ u := by
      rintro rfl
      have hm : v ∈ G.neighborFinset v := by simp [hu]
      exact G.loopless.irrefl v ((G.mem_neighborFinset _ _).mp hm)
    obtain ⟨p, hp⟩ := (reachable_induce_iff (U := {t : W | t ≠ u}) hv_ne_u hwu).mp
      ((h2.2 u) ⟨v, hv_ne_u⟩ ⟨w, hwu⟩)
    cases p with
    | nil => exact hwv rfl
    | @cons _ nxt _ hadj _ =>
      have hm : nxt ∈ G.neighborFinset v := (G.mem_neighborFinset _ _).mpr hadj
      rw [hu, Finset.mem_singleton] at hm
      exact hp nxt (by simp) hm

lemma append_isPath {W : Type*} {G : SimpleGraph W} {u v w : W}
    {p : G.Walk u v} {q : G.Walk v w} (hp : p.IsPath) (hq : q.IsPath)
    (hinter : ∀ t ∈ p.support, t ∈ q.support → t = v) :
    (p.append q).IsPath := by
  rw [Walk.isPath_def, Walk.support_append, List.nodup_append']
  refine ⟨hp.support_nodup, hq.support_nodup.tail, ?_⟩
  rw [List.disjoint_left]
  intro t htp htq
  have hnodup_q := hq.support_nodup
  rw [support_eq_cons_tail q, List.nodup_cons] at hnodup_q
  have htv : t = v := hinter t htp (List.mem_of_mem_tail htq)
  exact hnodup_q.1 (htv ▸ htq)

lemma cycle_of_two_paths_mod3 {W : Type*} {G : SimpleGraph W} {u v : W} (huv : u ≠ v)
    {p q : G.Walk u v} (hp : p.IsPath) (hq : q.IsPath)
    (hdisj : ∀ t ∈ p.support, t ∈ q.support → t = u ∨ t = v)
    (hmod : (p.length + q.length) % 3 = 0) :
    HasMod3Cycle G := by
  have hp_pos : 1 ≤ p.length := one_le_length_of_ne huv p
  have hq_pos : 1 ≤ q.length := one_le_length_of_ne huv q
  have hgt1 : 1 < p.length ∨ 1 < q.reverse.length := by
    rw [Walk.length_reverse]
    omega
  have htail_disj : p.support.tail.Disjoint q.reverse.support.tail := by
    rw [List.disjoint_left]
    intro t htp htq
    have hnodup_p := hp.support_nodup
    rw [support_eq_cons_tail p, List.nodup_cons] at hnodup_p
    have hnodup_q := hq.reverse.support_nodup
    rw [support_eq_cons_tail q.reverse, List.nodup_cons] at hnodup_q
    have htu : t ≠ u := fun h ↦ hnodup_p.1 (h ▸ htp)
    have htv : t ≠ v := fun h ↦ hnodup_q.1 (h ▸ htq)
    have htp' : t ∈ p.support := List.mem_of_mem_tail htp
    have htq' : t ∈ q.support := by
      have hm : t ∈ q.reverse.support := List.mem_of_mem_tail htq
      simpa [Walk.support_reverse] using hm
    rcases hdisj t htp' htq' with rfl | rfl
    · exact htu rfl
    · exact htv rfl
  refine ⟨u, p.append q.reverse, hp.isCycle_append hq.reverse htail_disj hgt1, ?_⟩
  rw [Walk.length_append, Walk.length_reverse]
  exact Nat.dvd_of_mod_eq_zero hmod

lemma first_exit {W : Type*} [DecidableEq W] {G : SimpleGraph W}
    (Q : Finset W) {q z : W} (hq : q ∈ Q) (hz : z ∉ Q) (p : G.Walk q z) :
    ∃ q' ∈ Q, ∃ w ∉ Q, G.Adj q' w ∧ w ∈ p.support ∧
      ∃ r : G.Walk q q', ∀ t ∈ r.support, t ∈ Q ∧ t ∈ p.support := by
  induction p with
  | nil => exact (hz hq).elim
  | @cons a b c hadj rest ih =>
    by_cases hb : b ∈ Q
    · obtain ⟨q', hq'Q, w, hwQ, hadj', hwp, r, hr⟩ := ih hb hz
      refine ⟨q', hq'Q, w, hwQ, hadj', by simp [hwp], .cons hadj r, ?_⟩
      intro t ht
      simp only [Walk.support_cons, List.mem_cons] at ht
      rcases ht with rfl | ht
      · exact ⟨hq, by simp⟩
      · exact ⟨(hr t ht).1, by simp [(hr t ht).2]⟩
    · refine ⟨a, hq, b, hb, hadj, by simp, .nil, ?_⟩
      intro t ht
      simp only [Walk.support_nil, List.mem_singleton] at ht
      subst ht
      exact ⟨hq, by simp⟩

lemma last_mem_suffix {W : Type*} [DecidableEq W] {G : SimpleGraph W}
    (S : Finset W) {a b : W} (ha : a ∈ S) (p : G.Walk a b) (hp : p.IsPath) :
    ∃ s ∈ S, ∃ q : G.Walk s b, q.IsPath ∧
      (∀ t ∈ q.support, t ∈ p.support) ∧
      (∀ t ∈ q.support.tail, t ∉ S) := by
  induction hlen : p.length using Nat.strongRecOn generalizing a with
  | ind n ih =>
    cases p with
    | nil =>
      exact ⟨b, ha, Walk.nil, Walk.IsPath.nil, fun t ht ↦ ht, by simp⟩
    | @cons _ nxt _ hadj rest =>
      have hrest_path : rest.IsPath := hp.of_cons
      by_cases hex : ∃ t ∈ rest.support, t ∈ S
      · rcases hex with ⟨t, ht_supp, htS⟩
        let p' := rest.dropUntil t ht_supp
        have hp'_path : p'.IsPath := hrest_path.dropUntil ht_supp
        have hp'_len : (rest.dropUntil t ht_supp).length < n := by
          have hle : (rest.dropUntil t ht_supp).length ≤ rest.length := by
            have hspec := Walk.take_spec rest ht_supp
            have hlen_eq := congrArg Walk.length hspec
            rw [Walk.length_append] at hlen_eq
            omega
          simp only [Walk.length_cons] at hlen
          omega
        obtain ⟨s, hsS, q, hq_path, hq_sub, hq_tail⟩ :=
          ih p'.length hp'_len htS p' hp'_path rfl
        refine ⟨s, hsS, q, hq_path, fun u hu ↦ ?_, hq_tail⟩
        have hu_rest : u ∈ rest.support :=
          Walk.support_dropUntil_subset_support rest ht_supp (hq_sub u hu)
        simp [hu_rest]
      · push Not at hex
        refine ⟨a, ha, .cons hadj rest, hp, fun u hu ↦ hu, ?_⟩
        intro u hu
        simp only [Walk.support_cons, List.tail_cons] at hu
        exact hex u hu

/- Connected component of `s` inside `U : Finset W`. -/
noncomputable def compIn {W : Type*} [Fintype W] [DecidableEq W] (G : SimpleGraph W)
    (U : Finset W) (s : W) : Finset W := by
  classical
  exact U.filter (fun v ↦ ∃ p : G.Walk s v, ∀ w ∈ p.support, w ∈ U)

lemma mem_compIn_iff {W : Type*} [Fintype W] [DecidableEq W] {G : SimpleGraph W}
    {U : Finset W} {s v : W} :
    v ∈ compIn G U s ↔ v ∈ U ∧ ∃ p : G.Walk s v, ∀ w ∈ p.support, w ∈ U := by
  classical
  simp [compIn]

lemma self_mem_compIn {W : Type*} [Fintype W] [DecidableEq W] {G : SimpleGraph W}
    {U : Finset W} {s : W} (hs : s ∈ U) : s ∈ compIn G U s := by
  rw [mem_compIn_iff]
  exact ⟨hs, .nil, by simp [hs]⟩

lemma compIn_subset {W : Type*} [Fintype W] [DecidableEq W] {G : SimpleGraph W}
    {U : Finset W} {s : W} : compIn G U s ⊆ U := by
  intro v hv
  exact (mem_compIn_iff.mp hv).1

lemma compIn_no_edge_out {W : Type*} [Fintype W] [DecidableEq W] {G : SimpleGraph W}
    {U : Finset W} {s a b : W} (ha : a ∈ compIn G U s) (hbU : b ∈ U) (hbC : b ∉ compIn G U s) :
    ¬ G.Adj a b := by
  intro hadj
  rcases mem_compIn_iff.mp ha with ⟨_, p, hp⟩
  apply hbC
  rw [mem_compIn_iff]
  refine ⟨hbU, p.append (.cons hadj .nil), ?_⟩
  intro w hw
  rw [Walk.support_append] at hw
  simp only [Walk.support_cons, Walk.support_nil, List.tail_cons, List.mem_append,
    List.mem_singleton] at hw
  rcases hw with hw | rfl
  · exact hp w hw
  · exact hbU

lemma walk_in_U_stays_in_compIn {W : Type*} [Fintype W] [DecidableEq W] {G : SimpleGraph W}
    {U : Finset W} {s a b : W} (ha : a ∈ compIn G U s) (p : G.Walk a b)
    (hpU : ∀ w ∈ p.support, w ∈ U) :
    ∀ w ∈ p.support, w ∈ compIn G U s := by
  induction p with
  | nil =>
    intro w hw
    simp only [Walk.support_nil, List.mem_singleton] at hw
    rwa [hw]
  | @cons x y z hadj rest ih =>
    have hyU : y ∈ U := hpU y (by simp)
    have hyC : y ∈ compIn G U s := by
      by_contra hyC
      exact compIn_no_edge_out ha hyU hyC hadj
    intro w hw
    simp only [Walk.support_cons, List.mem_cons] at hw
    rcases hw with rfl | hw
    · exact ha
    · exact ih hyC (fun t ht ↦ hpU t (by simp [ht])) w hw

lemma connected_induce_compIn {W : Type*} [Fintype W] [DecidableEq W] {G : SimpleGraph W}
    {U : Finset W} {s : W} (hs : s ∈ U) :
    (G.induce (compIn G U s : Set W)).Connected := by
  apply connected_induce_of_base s (self_mem_compIn hs)
  intro a ha
  rcases mem_compIn_iff.mp ha with ⟨_, p, hp⟩
  rw [reachable_induce_iff]
  exact ⟨p, walk_in_U_stays_in_compIn (self_mem_compIn hs) p hp⟩

lemma not_connected_induce_exists_disjoint_compIn {W : Type*} [Fintype W] [DecidableEq W]
    {G : SimpleGraph W} {U : Finset W} (hU : U.Nonempty)
    (hnc : ¬ (G.induce (U : Set W)).Connected) :
    ∃ u ∈ U, ∃ v ∈ U, Disjoint (compIn G U u) (compIn G U v) := by
  rcases hU with ⟨u, hu⟩
  by_contra hall
  push Not at hall
  apply hnc
  apply connected_induce_of_base u hu
  intro v hv
  obtain ⟨w, hw⟩ := Finset.not_disjoint_iff.mp (hall u hu v hv)
  rcases mem_compIn_iff.mp hw.1 with ⟨_, p1, hp1⟩
  rcases mem_compIn_iff.mp hw.2 with ⟨_, p2, hp2⟩
  rw [reachable_induce_iff]
  refine ⟨p1.append p2.reverse, ?_⟩
  intro t ht
  rw [Walk.support_append] at ht
  rcases List.mem_append.mp ht with ht1 | ht2
  · exact hp1 t ht1
  · have ht2' : t ∈ p2.reverse.support := List.mem_of_mem_tail ht2
    rw [Walk.support_reverse, List.mem_reverse] at ht2'
    exact hp2 t ht2'

lemma degree_induce_compIn_union {W : Type*} [Fintype W] [DecidableEq W] {G : SimpleGraph W}
    [DecidableRel G.Adj] {U X : Finset W} {s a : W} (ha : a ∈ compIn G U s)
    (hX : Finset.univ \ U ⊆ X) :
    (G.induce (((compIn G U s ∪ X) : Finset W) : Set W)).degree
      ⟨a, Finset.mem_coe.mpr (Finset.mem_union_left X ha)⟩ = G.degree a := by
  classical
  set S := compIn G U s ∪ X
  have haS : a ∈ (S : Set W) := Finset.mem_coe.mpr (Finset.mem_union_left X ha)
  rw [← card_neighborFinset_eq_degree, ← card_neighborFinset_eq_degree]
  apply Finset.card_bij (fun (w : {v : W // v ∈ (S : Set W)}) _ ↦ w.1)
  · intro w hw
    rw [SimpleGraph.mem_neighborFinset] at hw
    rw [SimpleGraph.mem_neighborFinset]
    exact hw
  · intro w1 _ w2 _ heq
    exact Subtype.ext heq
  · intro w hw
    rw [SimpleGraph.mem_neighborFinset] at hw
    have hwS : w ∈ S := by
      by_cases hwU : w ∈ U
      · apply Finset.mem_union_left
        by_contra hwC
        exact compIn_no_edge_out ha hwU hwC hw
      · exact Finset.mem_union_right _ (hX (Finset.mem_sdiff.mpr ⟨Finset.mem_univ w, hwU⟩))
    exact ⟨⟨w, Finset.mem_coe.mpr hwS⟩, (SimpleGraph.mem_neighborFinset _ _ _).mpr hw, rfl⟩

/- Contraction of an external set `X` to `none` on `Option {v // v ∈ A}`. -/
def contractOne {W : Type*} (G : SimpleGraph W) (A X : Finset W) :
    SimpleGraph (Option {v : W // v ∈ A}) where
  Adj o1 o2 :=
    match o1, o2 with
    | none, none => False
    | none, some a => ∃ u ∈ X, G.Adj u a.1
    | some a, none => ∃ u ∈ X, G.Adj u a.1
    | some a, some b => G.Adj a.1 b.1
  symm := ⟨fun o1 o2 h ↦ by
    cases o1 <;> cases o2
    · exact h
    · exact h
    · exact h
    · exact h.symm⟩
  loopless := ⟨fun o h ↦ by
    cases o
    · exact h
    · exact G.ne_of_adj h rfl⟩

noncomputable instance instDecidableRelContractOne {W : Type*} (G : SimpleGraph W)
    (A X : Finset W) : DecidableRel (contractOne G A X).Adj := by
  classical
  infer_instance

lemma isTwoConn_contractOne {W : Type*} [Fintype W] [DecidableEq W] {G : SimpleGraph W}
    (h2G : IsTwoConn G) {U X : Finset W} {s z_out : W} (hs : s ∈ U)
    (hA_card : 2 ≤ (compIn G U s).card)
    (hz_out : z_out ∉ compIn G U s)
    (hbdy : ∀ a ∈ compIn G U s, ∀ w ∉ compIn G U s, G.Adj a w → w ∈ X) :
    IsTwoConn (contractOne G (compIn G U s) X) := by
  set A := compIn G U s
  set H := contractOne G A X
  have hreach_none : ∀ (c : Option {v : W // v ∈ A}) (hc_none : c ≠ none)
      (a : W) (ha : a ∈ A) (hac : some ⟨a, ha⟩ ≠ c),
        (H.induce {t | t ≠ c}).Reachable ⟨none, Ne.symm hc_none⟩ ⟨some ⟨a, ha⟩, hac⟩ := by
    intro c hc_none a ha hac
    have hwalk : ∃ p : G.Walk a z_out, ∀ x : {v : W // v ∈ A}, c = some x → x.1 ∉ p.support := by
      cases c with
      | none => exact (hc_none rfl).elim
      | some x =>
        have hax : a ≠ x.1 := fun heq ↦ hac (congrArg some (Subtype.ext heq))
        have hzx : z_out ≠ x.1 := fun h ↦ hz_out (h ▸ x.2)
        obtain ⟨p, hp⟩ := (reachable_induce_iff (U := {v : W | v ≠ x.1}) hax hzx).mp
          ((h2G.2 x.1) ⟨a, hax⟩ ⟨z_out, hzx⟩)
        refine ⟨p, fun x' hx' hmem ↦ ?_⟩
        cases hx'
        exact hp x.1 hmem rfl
    rcases hwalk with ⟨p, hp⟩
    obtain ⟨q', hq'A, w, hwA, hadj_qw, _, r, hr⟩ := first_exit A ha hz_out p
    have hwX : w ∈ X := hbdy q' hq'A w hwA hadj_qw
    have hq'_ne_c : (some ⟨q', hq'A⟩ : Option {v : W // v ∈ A}) ≠ c := by
      intro heq
      exact hp ⟨q', hq'A⟩ heq.symm (hr q' (Walk.end_mem_support r)).2
    have hadj_H : (H.induce {t | t ≠ c}).Adj ⟨none, Ne.symm hc_none⟩ ⟨some ⟨q', hq'A⟩, hq'_ne_c⟩ :=
      ⟨w, hwX, hadj_qw.symm⟩
    suffices hsub : (H.induce {t | t ≠ c}).Reachable ⟨some ⟨a, ha⟩, hac⟩ ⟨some ⟨q', hq'A⟩, hq'_ne_c⟩ by
      exact hadj_H.reachable.trans hsub.symm
    have liftToH : ∀ {u v : W} (hu : u ∈ A) (hv : v ∈ A)
        (huc : (some ⟨u, hu⟩ : Option {v : W // v ∈ A}) ≠ c) (hvc : (some ⟨v, hv⟩ : Option {v : W // v ∈ A}) ≠ c)
        (wlk : G.Walk u v),
        (∀ t ∈ wlk.support, ∃ ht : t ∈ A, (some ⟨t, ht⟩ : Option {v : W // v ∈ A}) ≠ c) →
        (H.induce {t | t ≠ c}).Reachable ⟨some ⟨u, hu⟩, huc⟩ ⟨some ⟨v, hv⟩, hvc⟩ := by
      intro u v hu hv huc hvc wlk
      induction wlk with
      | nil => intro _; exact Reachable.refl _
      | @cons x y z hadj_xy tl ihtl =>
        intro hmem
        obtain ⟨hyA, hyc⟩ := hmem y (by simp)
        have hadj_step : (H.induce {t | t ≠ c}).Adj ⟨some ⟨x, hu⟩, huc⟩ ⟨some ⟨y, hyA⟩, hyc⟩ :=
          hadj_xy
        exact hadj_step.reachable.trans (ihtl hyA hv hyc hvc (fun t ht ↦ hmem t (by simp [ht])))
    exact liftToH ha hq'A hac hq'_ne_c r (fun t ht ↦ ⟨(hr t ht).1, fun heq ↦
      hp ⟨t, (hr t ht).1⟩ heq.symm (hr t ht).2⟩)
  refine ⟨?_, fun c ↦ ?_⟩
  · obtain ⟨a, ha⟩ : A.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨b, hb, hab⟩ : ∃ b ∈ A, b ≠ a := by
      obtain ⟨b, hb, hab⟩ := Finset.exists_mem_ne hA_card a
      exact ⟨b, hb, hab⟩
    have hc_b : (some ⟨b, hb⟩ : Option {v : W // v ∈ A}) ≠ none := Option.some_ne_none _
    have hconn_sub : (H.induce {t | t ≠ some ⟨b, hb⟩}).Connected := by
      apply connected_induce_of_base none (Ne.symm hc_b)
      intro o ho
      cases o with
      | none => exact Reachable.refl _
      | some x => exact hreach_none (some ⟨b, hb⟩) hc_b x.1 x.2 ho
    have hreach_all : ∀ o : Option {v : W // v ∈ A}, H.Reachable none o := by
      intro o
      by_cases hob : o = some ⟨b, hb⟩
      · subst hob
        have ha_ne_b : (some ⟨a, ha⟩ : Option {v : W // v ∈ A}) ≠ some ⟨b, hb⟩ :=
          fun heq ↦ hab (Subtype.mk.inj (Option.some.inj heq)).symm
        have hc_a : (some ⟨a, ha⟩ : Option {v : W // v ∈ A}) ≠ none := Option.some_ne_none _
        obtain ⟨p⟩ := hreach_none (some ⟨a, ha⟩) hc_a b hb ha_ne_b.symm
        exact ⟨liftWalk p⟩
      · obtain ⟨p⟩ := hconn_sub ⟨none, Ne.symm hc_b⟩ ⟨o, hob⟩
        exact ⟨liftWalk p⟩
    exact @Connected.mk _ H (fun o1 o2 ↦ (hreach_all o1).symm.trans (hreach_all o2)) ⟨none⟩
  · cases c with
    | none =>
      have hA_conn := connected_induce_compIn (G := G) hs
      obtain ⟨a0, ha0⟩ : A.Nonempty := Finset.card_pos.mp (by omega)
      set Sno : Set (Option {v : W // v ∈ A}) := {t | t ≠ none}
      refine @Connected.mk _ _ (fun ⟨o1, ho1⟩ ⟨o2, ho2⟩ ↦ ?_)
        ⟨⟨some ⟨a0, ha0⟩, Option.some_ne_none _⟩⟩
      cases o1 with
      | none => exact (ho1 rfl).elim
      | some x1 =>
        cases o2 with
        | none => exact (ho2 rfl).elim
        | some x2 =>
          obtain ⟨p⟩ := hA_conn.preconnected ⟨x1.1, x1.2⟩ ⟨x2.1, x2.2⟩
          let mapSome : ∀ {u v : {w : W // w ∈ (A : Set W)}} (wlk : (G.induce (A : Set W)).Walk u v),
              (H.induce Sno).Walk
                ⟨some ⟨u.1, Finset.mem_coe.mp u.2⟩, Option.some_ne_none _⟩
                ⟨some ⟨v.1, Finset.mem_coe.mp v.2⟩, Option.some_ne_none _⟩ := by
            intro u v wlk
            induction wlk with
            | nil => exact .nil
            | @cons u1 u2 _ hadj tl ihtl =>
              have hadj_H : (H.induce Sno).Adj
                  ⟨some ⟨u1.1, Finset.mem_coe.mp u1.2⟩, Option.some_ne_none _⟩
                  ⟨some ⟨u2.1, Finset.mem_coe.mp u2.2⟩, Option.some_ne_none _⟩ :=
                induce_adj_val hadj
              exact .cons hadj_H ihtl
          exact ⟨mapSome p⟩
    | some x =>
      apply connected_induce_of_base none (Option.some_ne_none x).symm
      intro o ho
      cases o with
      | none => exact Reachable.refl _
      | some y => exact hreach_none (some x) (Option.some_ne_none x) y.1 y.2 ho

lemma degree_le_contractOne {W : Type*} [Fintype W] [DecidableEq W] {G : SimpleGraph W}
    [DecidableRel G.Adj] {A X : Finset W} (a : {v : W // v ∈ A})
    (hbdy : ∀ w ∉ A, G.Adj a.1 w → w ∈ X)
    (hX1 : (G.neighborFinset a.1 ∩ X).card ≤ 1) :
    G.degree a.1 ≤ (contractOne G A X).degree (some a) := by
  classical
  set H := contractOne G A X
  rw [← card_neighborFinset_eq_degree, ← card_neighborFinset_eq_degree]
  let f : W → Option {v : W // v ∈ A} := fun w ↦
    if hw : w ∈ A then some ⟨w, hw⟩ else none
  apply Finset.card_le_card_of_injOn f
  · intro w hw
    rw [Finset.mem_coe, SimpleGraph.mem_neighborFinset] at hw
    rw [Finset.mem_coe, SimpleGraph.mem_neighborFinset]
    dsimp only [f]
    split_ifs with hwA
    · exact hw
    · exact ⟨w, hbdy w hwA hw, hw.symm⟩
  · intro w1 hw1 w2 hw2 heq
    rw [Finset.mem_coe, SimpleGraph.mem_neighborFinset] at hw1 hw2
    dsimp only [f] at heq
    by_cases h1 : w1 ∈ A <;> by_cases h2 : w2 ∈ A
    · simp only [h1, h2, ↓reduceDIte, Option.some.injEq, Subtype.mk.injEq] at heq
      exact heq
    · simp [h1, h2] at heq
    · simp [h1, h2] at heq
    · have hm1 : w1 ∈ G.neighborFinset a.1 ∩ X :=
        Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hw1, hbdy w1 h1 hw1⟩
      have hm2 : w2 ∈ G.neighborFinset a.1 ∩ X :=
        Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hw2, hbdy w2 h2 hw2⟩
      exact Finset.card_le_one.mp hX1 w1 hm1 w2 hm2

lemma lift_some_walk_contractOne {W : Type*} {G : SimpleGraph W} {A X : Finset W}
    {b c : {v : W // v ∈ A}} (wlk : (contractOne G A X).Walk (some b) (some c))
    (hno : none ∉ wlk.support) (hpath : wlk.IsPath) :
    ∃ r : G.Walk b.1 c.1, r.IsPath ∧ r.length = wlk.length ∧
      ∀ t ∈ r.support, ∃ ht : t ∈ A, (some ⟨t, ht⟩ : Option {v : W // v ∈ A}) ∈ wlk.support := by
  suffices hgen : ∀ {o1 o2 : Option {v : W // v ∈ A}} (w : (contractOne G A X).Walk o1 o2),
      none ∉ w.support → w.IsPath → ∀ (b c : {v : W // v ∈ A}), o1 = some b → o2 = some c →
      ∃ r : G.Walk b.1 c.1, r.IsPath ∧ r.length = w.length ∧
        ∀ t ∈ r.support, ∃ ht : t ∈ A, (some ⟨t, ht⟩ : Option {v : W // v ∈ A}) ∈ w.support from
    hgen wlk hno hpath b c rfl rfl
  intro o1 o2 w
  induction w with
  | nil =>
    intro _ _ b c ho1 ho2
    have hbc : b = c := Option.some.inj (ho1.symm.trans ho2)
    subst hbc; subst ho1
    refine ⟨.nil, Walk.IsPath.nil, rfl, fun t ht ↦ ?_⟩
    simp only [Walk.support_nil, List.mem_singleton] at ht
    subst ht
    exact ⟨b.2, Walk.start_mem_support _⟩
  | @cons u1 u2 u3 hadj_step tl ihtl =>
    intro hno_w hpath_w b c ho1 ho2
    subst ho1
    cases u2 with
    | none => exact (hno_w (by simp)).elim
    | some b' =>
      have hno_tl : none ∉ tl.support := fun hm ↦ hno_w (by simp [hm])
      have hnd := hpath_w.support_nodup
      simp only [Walk.support_cons, List.nodup_cons] at hnd
      obtain ⟨r, hr_path, hr_len, hr_supp⟩ := ihtl hno_tl hpath_w.of_cons b' c rfl ho2
      have hb_not_r : b.1 ∉ r.support := by
        intro hbr
        obtain ⟨hbA, hbm⟩ := hr_supp b.1 hbr
        have heq : (⟨b.1, hbA⟩ : {v : W // v ∈ A}) = b := Subtype.ext rfl
        exact hnd.1 (heq ▸ hbm)
      let hadj_G : G.Adj b.1 b'.1 := hadj_step
      refine ⟨.cons hadj_G r, Walk.IsPath.cons hr_path hb_not_r, ?_, fun t ht ↦ ?_⟩
      · rw [Walk.length_cons, Walk.length_cons, hr_len]
      · simp only [Walk.support_cons, List.mem_cons] at ht
        rcases ht with rfl | ht
        · exact ⟨b.2, Walk.start_mem_support _⟩
        · obtain ⟨htA, htm⟩ := hr_supp t ht
          exact ⟨htA, List.mem_cons_of_mem _ htm⟩

lemma lift_walk_contractOne {W : Type*} {G : SimpleGraph W} {A X : Finset W}
    (hdisj : Disjoint A X) {y : {v : W // v ∈ A}}
    (p : (contractOne G A X).Walk none (some y)) (hp : p.IsPath) :
    ∃ u ∈ X, ∃ q : G.Walk u y.1, q.IsPath ∧ q.length = p.length ∧
      ∀ t ∈ q.support.tail, t ∈ A := by
  cases p with
  | @cons _ mid _ hadj rest =>
    cases mid with
    | none => exact hadj.elim
    | some a =>
      have hnd := hp.support_nodup
      simp only [Walk.support_cons, List.nodup_cons] at hnd
      have hp_tl : rest.IsPath := hp.of_cons
      clear hp
      rw [Walk.length_cons]
      rcases hadj with ⟨u, huX, hadj_ua⟩
      obtain ⟨r, hr_path, hr_len, hr_supp⟩ := lift_some_walk_contractOne rest hnd.1 hp_tl
      have hu_not_r : u ∉ r.support := by
        intro hur
        obtain ⟨huA, _⟩ := hr_supp u hur
        exact Finset.disjoint_left.mp hdisj huA huX
      refine ⟨u, huX, .cons hadj_ua r, Walk.IsPath.cons hr_path hu_not_r, by rw [Walk.length_cons, hr_len], ?_⟩
      intro t ht
      simp only [Walk.support_cons, List.tail_cons] at ht
      exact (hr_supp t ht).1

/- Contraction of two disjoint external sets `X0, X1` onto `{v // v ∈ Q} ⊕ Fin 2`. -/
def contractTwo {W : Type*} (G : SimpleGraph W) (Q X0 X1 : Finset W) :
    SimpleGraph ({v : W // v ∈ Q} ⊕ Fin 2) where
  Adj s1 s2 :=
    match s1, s2 with
    | .inl a, .inl b => G.Adj a.1 b.1
    | .inl a, .inr i => if i = 0 then ∃ u ∈ X0, G.Adj a.1 u else ∃ u ∈ X1, G.Adj a.1 u
    | .inr i, .inl a => if i = 0 then ∃ u ∈ X0, G.Adj a.1 u else ∃ u ∈ X1, G.Adj a.1 u
    | .inr _, .inr _ => False
  symm := ⟨fun s1 s2 h ↦ by
    cases s1 <;> cases s2
    · exact h.symm
    · exact h
    · exact h
    · exact h⟩
  loopless := ⟨fun s h ↦ by
    cases s
    · exact G.ne_of_adj h rfl
    · exact h⟩

noncomputable instance instDecidableRelContractTwo {W : Type*} (G : SimpleGraph W)
    (Q X0 X1 : Finset W) : DecidableRel (contractTwo G Q X0 X1).Adj := by
  classical
  infer_instance

lemma isTwoConn_addEdge_contractTwo {W : Type*} [Fintype W] [DecidableEq W] {G : SimpleGraph W}
    (h2G : IsTwoConn G) {U X0 X1 : Finset W} {s : W} (hs : s ∈ U)
    (hdisj0 : Disjoint (compIn G U s) X0)
    (hbdy : ∀ q ∈ compIn G U s, ∀ w ∉ compIn G U s, G.Adj q w → w ∈ X0 ∪ X1)
    (hex0 : ∃ q0 ∈ compIn G U s, ∃ u0 ∈ X0, G.Adj q0 u0)
    (hex1 : ∃ q1 ∈ compIn G U s, ∃ u1 ∈ X1, G.Adj q1 u1) :
    IsTwoConn (addEdge (contractTwo G (compIn G U s) X0 X1) (.inr 0) (.inr 1)) := by
  set Q := compIn G U s
  set H := contractTwo G Q X0 X1
  set K := addEdge H (.inr 0) (.inr 1)
  have h01_ne : (Sum.inr 0 : {v : W // v ∈ Q} ⊕ Fin 2) ≠ Sum.inr 1 := by intro h; simp at h
  have hadj_01 : K.Adj (.inr 0) (.inr 1) := addEdge_adj_self H h01_ne
  rcases hex0 with ⟨q0, hq0Q, u0, hu0X0, hadj_q0⟩
  rcases hex1 with ⟨q1, hq1Q, u1, hu1X1, hadj_q1⟩
  have hu0_not_Q : u0 ∉ Q := Finset.disjoint_right.mp hdisj0 hu0X0
  set S0 : Set ({v : W // v ∈ Q} ⊕ Fin 2) := {t | t ≠ .inr 0}
  set S1 : Set ({v : W // v ∈ Q} ⊕ Fin 2) := {t | t ≠ .inr 1}
  have hcut_inr0 : (K.induce S0).Connected := by
    have h1_ne : (Sum.inr 1 : {v : W // v ∈ Q} ⊕ Fin 2) ∈ S0 := by intro h; simp at h
    apply connected_induce_of_base (.inr 1) h1_ne
    intro t ht
    cases t with
    | inr j =>
      fin_cases j
      · exact (ht rfl).elim
      · exact Reachable.refl _
    | inl a =>
      have hQ_conn := connected_induce_compIn (G := G) hs
      obtain ⟨p⟩ := hQ_conn.preconnected ⟨q1, hq1Q⟩ ⟨a.1, a.2⟩
      let mapInl : ∀ {x y : {v : W // v ∈ (Q : Set W)}} (wlk : (G.induce (Q : Set W)).Walk x y),
          (K.induce S0).Walk
            ⟨.inl ⟨x.1, Finset.mem_coe.mp x.2⟩, Sum.inl_ne_inr⟩
            ⟨.inl ⟨y.1, Finset.mem_coe.mp y.2⟩, Sum.inl_ne_inr⟩ := by
        intro x y wlk
        induction wlk with
        | nil => exact .nil
        | @cons u1 u2 _ hadj tl ihtl =>
          have hadj_K : (K.induce S0).Adj
              ⟨.inl ⟨u1.1, Finset.mem_coe.mp u1.2⟩, Sum.inl_ne_inr⟩
              ⟨.inl ⟨u2.1, Finset.mem_coe.mp u2.2⟩, Sum.inl_ne_inr⟩ :=
            Or.inl (induce_adj_val hadj)
          exact .cons hadj_K ihtl
      have hadj_1_q1 : (K.induce S0).Adj ⟨.inr 1, h1_ne⟩
          ⟨.inl ⟨q1, hq1Q⟩, Sum.inl_ne_inr⟩ := Or.inl (by simp [H, contractTwo]; exact ⟨u1, hu1X1, hadj_q1⟩)
      exact hadj_1_q1.reachable.trans ⟨mapInl p⟩
  have hcut_inr1 : (K.induce S1).Connected := by
    have h0_mem : (Sum.inr 0 : {v : W // v ∈ Q} ⊕ Fin 2) ∈ S1 := h01_ne
    apply connected_induce_of_base (.inr 0) h0_mem
    intro t ht
    cases t with
    | inr j =>
      fin_cases j
      · exact Reachable.refl _
      · exact (ht rfl).elim
    | inl a =>
      have hQ_conn := connected_induce_compIn (G := G) hs
      obtain ⟨p⟩ := hQ_conn.preconnected ⟨q0, hq0Q⟩ ⟨a.1, a.2⟩
      let mapInl : ∀ {x y : {v : W // v ∈ (Q : Set W)}} (wlk : (G.induce (Q : Set W)).Walk x y),
          (K.induce S1).Walk
            ⟨.inl ⟨x.1, Finset.mem_coe.mp x.2⟩, Sum.inl_ne_inr⟩
            ⟨.inl ⟨y.1, Finset.mem_coe.mp y.2⟩, Sum.inl_ne_inr⟩ := by
        intro x y wlk
        induction wlk with
        | nil => exact .nil
        | @cons u1 u2 _ hadj tl ihtl =>
          have hadj_K : (K.induce S1).Adj
              ⟨.inl ⟨u1.1, Finset.mem_coe.mp u1.2⟩, Sum.inl_ne_inr⟩
              ⟨.inl ⟨u2.1, Finset.mem_coe.mp u2.2⟩, Sum.inl_ne_inr⟩ :=
            Or.inl (induce_adj_val hadj)
          exact .cons hadj_K ihtl
      have hadj_0_q0 : (K.induce S1).Adj ⟨.inr 0, h0_mem⟩
          ⟨.inl ⟨q0, hq0Q⟩, Sum.inl_ne_inr⟩ := Or.inl (by simp [H, contractTwo]; exact ⟨u0, hu0X0, hadj_q0⟩)
      exact hadj_0_q0.reachable.trans ⟨mapInl p⟩
  refine ⟨?_, fun c ↦ ?_⟩
  · have hreach0 : ∀ t : {v : W // v ∈ Q} ⊕ Fin 2, K.Reachable (.inr 0) t := by
      intro t
      by_cases ht1 : t = .inr 1
      · subst ht1
        exact hadj_01.reachable
      · obtain ⟨p⟩ := hcut_inr1 ⟨.inr 0, h01_ne⟩ ⟨t, ht1⟩
        exact ⟨liftWalk p⟩
    exact @Connected.mk _ K (fun t1 t2 ↦ (hreach0 t1).symm.trans (hreach0 t2)) ⟨.inr 0⟩
  · cases c with
    | inr j =>
      fin_cases j
      · exact hcut_inr0
      · exact hcut_inr1
    | inl x =>
      set Sx : Set ({v : W // v ∈ Q} ⊕ Fin 2) := {t | t ≠ .inl x}
      have h0_ne : (Sum.inr 0 : {v : W // v ∈ Q} ⊕ Fin 2) ∈ Sx := Sum.inr_ne_inl
      have h1_ne : (Sum.inr 1 : {v : W // v ∈ Q} ⊕ Fin 2) ∈ Sx := Sum.inr_ne_inl
      have hadj_01_sub : (K.induce Sx).Adj ⟨.inr 0, h0_ne⟩ ⟨.inr 1, h1_ne⟩ := hadj_01
      apply connected_induce_of_base (.inr 0) h0_ne
      intro t ht
      cases t with
      | inr j =>
        fin_cases j
        · exact Reachable.refl _
        · exact hadj_01_sub.reachable
      | inl a =>
        have hax : a.1 ≠ x.1 := fun heq ↦ ht (congrArg Sum.inl (Subtype.ext heq))
        have hu0x : u0 ≠ x.1 := fun h ↦ hu0_not_Q (h ▸ x.2)
        obtain ⟨p, hp⟩ := (reachable_induce_iff (U := {v : W | v ≠ x.1}) hax hu0x).mp
          ((h2G.2 x.1) ⟨a.1, hax⟩ ⟨u0, hu0x⟩)
        obtain ⟨q', hq'Q, w, hwQ, hadj_qw, _, r, hr⟩ := first_exit Q a.2 hu0_not_Q p
        have hq'_ne : (Sum.inl ⟨q', hq'Q⟩ : {v : W // v ∈ Q} ⊕ Fin 2) ∈ Sx := by
          intro heq
          have hqx : q' = x.1 := Subtype.mk.inj (Sum.inl.inj heq)
          exact hp q' (hr q' (Walk.end_mem_support r)).2 hqx
        have liftToK : ∀ {u v : W} (hu : u ∈ Q) (hv : v ∈ Q)
            (hux : (Sum.inl ⟨u, hu⟩ : {v : W // v ∈ Q} ⊕ Fin 2) ∈ Sx)
            (hvx : (Sum.inl ⟨v, hv⟩ : {v : W // v ∈ Q} ⊕ Fin 2) ∈ Sx)
            (wlk : G.Walk u v),
            (∀ z ∈ wlk.support, ∃ hz : z ∈ Q, (Sum.inl ⟨z, hz⟩ : {v : W // v ∈ Q} ⊕ Fin 2) ∈ Sx) →
            (K.induce Sx).Reachable ⟨.inl ⟨u, hu⟩, hux⟩ ⟨.inl ⟨v, hv⟩, hvx⟩ := by
          intro u v hu hv hux hvx wlk
          induction wlk with
          | nil => intro _; exact Reachable.refl _
          | @cons z1 z2 z3 hadj_step tl ihtl =>
            intro hmem
            obtain ⟨hz2Q, hz2x⟩ := hmem z2 (by simp)
            have hadj_K : (K.induce Sx).Adj
                ⟨.inl ⟨z1, hu⟩, hux⟩ ⟨.inl ⟨z2, hz2Q⟩, hz2x⟩ := Or.inl hadj_step
            exact hadj_K.reachable.trans
              (ihtl hz2Q hv hz2x hvx (fun z hz ↦ hmem z (by simp [hz])))
        have hreach_aq' : (K.induce Sx).Reachable ⟨.inl a, ht⟩ ⟨.inl ⟨q', hq'Q⟩, hq'_ne⟩ := by
          refine liftToK a.2 hq'Q ht hq'_ne r (fun z hz ↦ ⟨(hr z hz).1, fun heq ↦ ?_⟩)
          have hzx : z = x.1 := Subtype.mk.inj (Sum.inl.inj heq)
          exact hp z (hr z hz).2 hzx
        rcases Finset.mem_union.mp (hbdy q' hq'Q w hwQ hadj_qw) with hw0 | hw1
        · have hadj_0 : (K.induce Sx).Adj ⟨.inr 0, h0_ne⟩ ⟨.inl ⟨q', hq'Q⟩, hq'_ne⟩ :=
            Or.inl (by simp [H, contractTwo]; exact ⟨w, hw0, hadj_qw⟩)
          exact hadj_0.reachable.trans hreach_aq'.symm
        · have hadj_1 : (K.induce Sx).Adj ⟨.inr 1, h1_ne⟩ ⟨.inl ⟨q', hq'Q⟩, hq'_ne⟩ :=
            Or.inl (by simp [H, contractTwo]; exact ⟨w, hw1, hadj_qw⟩)
          exact hadj_01_sub.reachable.trans (hadj_1.reachable.trans hreach_aq'.symm)

lemma degree_le_contractTwo {W : Type*} [Fintype W] [DecidableEq W] {G : SimpleGraph W}
    [DecidableRel G.Adj] {Q X0 X1 : Finset W} (a : {v : W // v ∈ Q})
    (hbdy : ∀ w ∉ Q, G.Adj a.1 w → w ∈ X0 ∪ X1)
    (hX0 : (G.neighborFinset a.1 ∩ X0).card ≤ 1)
    (hX1 : (G.neighborFinset a.1 ∩ X1).card ≤ 1) :
    G.degree a.1 ≤ (contractTwo G Q X0 X1).degree (.inl a) := by
  classical
  set H := contractTwo G Q X0 X1
  rw [← card_neighborFinset_eq_degree, ← card_neighborFinset_eq_degree]
  let f : W → {v : W // v ∈ Q} ⊕ Fin 2 := fun w ↦
    if hw : w ∈ Q then .inl ⟨w, hw⟩ else if w ∈ X0 then .inr 0 else .inr 1
  apply Finset.card_le_card_of_injOn f
  · intro w hw
    rw [Finset.mem_coe, SimpleGraph.mem_neighborFinset] at hw
    rw [Finset.mem_coe, SimpleGraph.mem_neighborFinset]
    dsimp only [f]
    split_ifs with hwQ hw0
    · exact hw
    · simp [contractTwo]
      exact ⟨w, hw0, hw⟩
    · simp [contractTwo]
      rcases Finset.mem_union.mp (hbdy w hwQ hw) with h0 | h1
      · exact (hw0 h0).elim
      · exact ⟨w, h1, hw⟩
  · intro w1 hw1 w2 hw2 heq
    rw [Finset.mem_coe, SimpleGraph.mem_neighborFinset] at hw1 hw2
    dsimp only [f] at heq
    by_cases h1Q : w1 ∈ Q <;> by_cases h2Q : w2 ∈ Q
    · simp only [h1Q, h2Q, ↓reduceDIte, Sum.inl.injEq, Subtype.mk.injEq] at heq
      exact heq
    · simp only [h1Q, h2Q, ↓reduceDIte] at heq
      split_ifs at heq
    · simp only [h1Q, h2Q, ↓reduceDIte] at heq
      split_ifs at heq
    · simp only [h1Q, h2Q, ↓reduceDIte] at heq
      by_cases h10 : w1 ∈ X0 <;> by_cases h20 : w2 ∈ X0
      · have hm1 : w1 ∈ G.neighborFinset a.1 ∩ X0 :=
          Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hw1, h10⟩
        have hm2 : w2 ∈ G.neighborFinset a.1 ∩ X0 :=
          Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hw2, h20⟩
        exact Finset.card_le_one.mp hX0 w1 hm1 w2 hm2
      · simp [h10, h20] at heq
      · simp [h10, h20] at heq
      · have hw1_X1 : w1 ∈ X1 := by
          rcases Finset.mem_union.mp (hbdy w1 h1Q hw1) with h0 | h1
          · exact (h10 h0).elim
          · exact h1
        have hw2_X1 : w2 ∈ X1 := by
          rcases Finset.mem_union.mp (hbdy w2 h2Q hw2) with h0 | h1
          · exact (h20 h0).elim
          · exact h1
        have hm1 : w1 ∈ G.neighborFinset a.1 ∩ X1 :=
          Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hw1, hw1_X1⟩
        have hm2 : w2 ∈ G.neighborFinset a.1 ∩ X1 :=
          Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hw2, hw2_X1⟩
        exact Finset.card_le_one.mp hX1 w1 hm1 w2 hm2

lemma lift_inl_walk_contractTwo {W : Type*} {G : SimpleGraph W} {Q X0 X1 : Finset W}
    (hdisj1 : Disjoint Q X1)
    {a : {v : W // v ∈ Q}} (wlk : (contractTwo G Q X0 X1).Walk (.inl a) (.inr 1))
    (hno0 : .inr 0 ∉ wlk.support) (hpath : wlk.IsPath) :
    ∃ u1 ∈ X1, ∃ q1 ∈ Q, G.Adj q1 u1 ∧
      ∃ r : G.Walk a.1 q1, r.IsPath ∧ r.length + 1 = wlk.length ∧
        ∀ t ∈ r.support, ∃ ht : t ∈ Q, (Sum.inl ⟨t, ht⟩ : _ ⊕ Fin 2) ∈ wlk.support := by
  induction hlen : wlk.length using Nat.strongRecOn generalizing a with
  | ind k ih =>
    cases wlk with
    | @cons _ nxt _ hadj_step tl =>
      have hnd := hpath.support_nodup
      simp only [Walk.support_cons, List.nodup_cons] at hnd
      cases nxt with
      | inr j =>
        fin_cases j
        · exact (hno0 (by simp)).elim
        · cases tl with
          | nil =>
            obtain ⟨u1, hu1X1, hadj_au1⟩ : ∃ u ∈ X1, G.Adj a.1 u := by
              simpa [contractTwo] using hadj_step
            refine ⟨u1, hu1X1, a.1, a.2, hadj_au1, .nil, Walk.IsPath.nil, hlen, fun t ht ↦ ?_⟩
            simp only [Walk.support_nil, List.mem_singleton] at ht
            subst ht
            exact ⟨a.2, by simp⟩
          | cons _ _ =>
            exfalso
            have hnd_tl := hpath.of_cons.support_nodup
            simp only [Walk.support_cons, List.nodup_cons] at hnd_tl
            exact hnd_tl.1 (Walk.end_mem_support _)
      | inl a' =>
        have hno0_tl : .inr 0 ∉ tl.support := fun hm ↦ hno0 (by simp [hm])
        have hlt_tl : tl.length < k := by simp only [Walk.length_cons] at hlen; omega
        obtain ⟨u1, hu1X1, q1, hq1Q, hadj_q1, r, hr_path, hr_len, hr_supp⟩ :=
          ih tl.length hlt_tl tl hno0_tl hpath.of_cons rfl
        have ha_not_r : a.1 ∉ r.support := by
          intro har
          obtain ⟨haQ, ham⟩ := hr_supp a.1 har
          have heq : (⟨a.1, haQ⟩ : {v : W // v ∈ Q}) = a := Subtype.ext rfl
          exact hnd.1 (heq ▸ ham)
        have _ := hdisj1
        have hadj_G : G.Adj a.1 a'.1 := hadj_step
        refine ⟨u1, hu1X1, q1, hq1Q, hadj_q1, .cons hadj_G r,
          Walk.IsPath.cons hr_path ha_not_r, by simp only [Walk.length_cons] at hlen ⊢; omega, fun t ht ↦ ?_⟩
        simp only [Walk.support_cons, List.mem_cons] at ht
        rcases ht with rfl | ht
        · exact ⟨a.2, by simp⟩
        · obtain ⟨htQ, htm⟩ := hr_supp t ht
          exact ⟨htQ, by simp [htm]⟩

lemma lift_walk_contractTwo {W : Type*} {G : SimpleGraph W} {Q X0 X1 : Finset W}
    (hdisj0 : Disjoint Q X0) (hdisj1 : Disjoint Q X1) (hdisj01 : Disjoint X0 X1)
    (p : (contractTwo G Q X0 X1).Walk (.inr 0) (.inr 1)) (hp : p.IsPath) :
    ∃ u0 ∈ X0, ∃ u1 ∈ X1, ∃ q : G.Walk u0 u1, q.IsPath ∧ q.length = p.length ∧
      ∀ t ∈ q.support, t ∈ Q ∨ t = u0 ∨ t = u1 := by
  cases p with
  | @cons _ mid _ hadj0 rest =>
    cases mid with
    | inr _ => exact hadj0.elim
    | inl a =>
      obtain ⟨u0, hu0X0, hadj_au0⟩ : ∃ u ∈ X0, G.Adj a.1 u := by
        simpa [contractTwo] using hadj0
      have hnd := hp.support_nodup
      simp only [Walk.support_cons, List.nodup_cons] at hnd
      obtain ⟨u1, hu1X1, q1, _, hadj_q1u1, r, hr_path, hr_len, hr_supp⟩ :=
        lift_inl_walk_contractTwo hdisj1 rest hnd.1 hp.of_cons
      have hu1_not_r : u1 ∉ r.support := by
        intro hm
        obtain ⟨hu1Q, _⟩ := hr_supp u1 hm
        exact Finset.disjoint_left.mp hdisj1 hu1Q hu1X1
      have hr1_path : (r.append (.cons hadj_q1u1 .nil)).IsPath := by
        apply append_isPath hr_path (Walk.IsPath.cons Walk.IsPath.nil (by simp [G.ne_of_adj hadj_q1u1]))
        intro t htr ht_end
        simp only [Walk.support_cons, Walk.support_nil, List.mem_cons,
          List.not_mem_nil, or_false] at ht_end
        rcases ht_end with rfl | rfl
        · rfl
        · exact (hu1_not_r htr).elim
      have hu0_not_r1 : u0 ∉ (r.append (.cons hadj_q1u1 .nil)).support := by
        intro hm
        rw [Walk.support_append] at hm
        simp only [Walk.support_cons, Walk.support_nil, List.tail_cons, List.mem_append,
          List.mem_singleton] at hm
        rcases hm with hmr | rfl
        · obtain ⟨hu0Q, _⟩ := hr_supp u0 hmr
          exact Finset.disjoint_left.mp hdisj0 hu0Q hu0X0
        · exact Finset.disjoint_left.mp hdisj01 hu0X0 hu1X1
      set q := Walk.cons hadj_au0.symm (r.append (.cons hadj_q1u1 .nil))
      refine ⟨u0, hu0X0, u1, hu1X1, q, Walk.IsPath.cons hr1_path hu0_not_r1, ?_, ?_⟩
      · simp [q, Walk.length_append, hr_len]
      · intro t ht
        simp only [q, Walk.support_cons, Walk.support_append, Walk.support_nil, List.tail_cons,
          List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at ht
        rcases ht with rfl | htr | rfl
        · exact Or.inr (Or.inl rfl)
        · exact Or.inl (hr_supp t htr).1
        · exact Or.inr (Or.inr rfl)

/- ### Section 2: Chiba-Ota-Yamashita two-terminal modulo-3 paths (`k = 2`) -/

lemma card_cube_add_edges_le_pred {W W' : Type*} [Fintype W] [Fintype W'] [DecidableEq W']
    (G' : SimpleGraph W') [DecidableRel G'.Adj]
    (hlt : Fintype.card W' < Fintype.card W) :
    Fintype.card W' ^ 3 + G'.edgeFinset.card ≤ Fintype.card W ^ 3 - 1 := by
  have hsum := G'.sum_degrees_eq_twice_card_edges
  have hle_sum : ∑ v : W', G'.degree v ≤ ∑ _v : W', Fintype.card W' :=
    Finset.sum_le_sum (fun v _ ↦ le_of_lt (G'.degree_lt_card_verts v))
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul] at hle_sum
  have hpow : (Fintype.card W' + 1) ^ 3 ≤ Fintype.card W ^ 3 :=
    Nat.pow_le_pow_left hlt 3
  have hstrict : Fintype.card W' ^ 3 + G'.edgeFinset.card < Fintype.card W ^ 3 := by
    nlinarith
  omega

theorem two_paths_mod3_z :
    ∀ (M : ℕ) {W : Type*} [Fintype W] [DecidableEq W] (G : SimpleGraph W) [DecidableRel G.Adj]
      (x y z : W),
      Fintype.card W ^ 3 + G.edgeFinset.card ≤ M →
      4 ≤ Fintype.card W →
      x ≠ y →
      IsTwoConn (addEdge G x y) →
      (∀ v : W, v ≠ x → v ≠ y → v ≠ z → 3 ≤ G.degree v) →
      ∃ (p1 p2 : G.Walk x y), p1.IsPath ∧ p2.IsPath ∧ p1.length % 3 ≠ p2.length % 3 := by
  intro M
  induction M using Nat.strongRecOn with
  | ind M ih =>
    intro W _ _ G _ x y z hM hcard hxy h2conn hdeg
    have hM_pos : Fintype.card W ^ 3 - 1 < M := by
      have : 1 ≤ Fintype.card W ^ 3 := Nat.one_le_pow 3 _ (by omega)
      omega
    -- Step 1: Reduce to `IsTwoConn G` (cut-vertex reduction).
    by_cases h2G : IsTwoConn G
    · -- Step 2: Reduce to `¬ G.Adj x y` (edge deletion).
      by_cases hadj_xy : G.Adj x y
      · set G' := delEdge G x y
        have hlt_e := edgeFinset_delEdge_lt G hadj_xy
        have hM_lt : M - 1 < M := by omega
        have hle_G' : Fintype.card W ^ 3 + G'.edgeFinset.card ≤ M - 1 := by
          dsimp only [G']
          omega
        have h2' : IsTwoConn (addEdge G' x y) := by
          rwa [addEdge_delEdge_eq G hxy]
        have hdeg' : ∀ v : W, v ≠ x → v ≠ y → v ≠ z → 3 ≤ G'.degree v := by
          intro v hvx hvy hvz
          rw [degree_delEdge_eq G hvx hvy]
          exact hdeg v hvx hvy hvz
        obtain ⟨p1, p2, hp1, hp2, hmod⟩ :=
          ih (M - 1) hM_lt G' x y z hle_G' hcard hxy h2' hdeg'
        exact ⟨p1.mapLe (delEdge_le G x y), p2.mapLe (delEdge_le G x y),
          hp1.mapLe _, hp2.mapLe _, by simpa using hmod⟩
      · -- Step 3: Symmetrize so `G.degree x ≤ G.degree y` without loss of generality.
        suffices hsym : ∀ (x' y' : W), x' ≠ y' → ¬ G.Adj x' y' →
            G.degree x' ≤ G.degree y' →
            (∀ v : W, v ≠ x' → v ≠ y' → v ≠ z → 3 ≤ G.degree v) →
            ∃ (p1 p2 : G.Walk x' y'), p1.IsPath ∧ p2.IsPath ∧ p1.length % 3 ≠ p2.length % 3 by
          by_cases hle_deg : G.degree x ≤ G.degree y
          · exact hsym x y hxy hadj_xy hle_deg hdeg
          · obtain ⟨p1, p2, hp1, hp2, hmod⟩ := hsym y x hxy.symm (fun h ↦ hadj_xy h.symm)
              (by omega) (fun v hvy hvx hvz ↦ hdeg v hvx hvy hvz)
            exact ⟨p1.reverse, p2.reverse, hp1.reverse, hp2.reverse, by simpa using hmod⟩
        clear hadj_xy hxy hdeg h2conn
        intro x y hxy hadj_xy hdeg_le hdeg
        -- Step 4: Rule out triangles containing `x` in `G - y`.
        by_cases htri : ∃ u v : W, u ≠ y ∧ v ≠ y ∧ G.Adj x u ∧ G.Adj x v ∧ G.Adj u v
        · rcases htri with ⟨u, v, huy, hvy, hxu, hxv, huv⟩
          have hux : u ≠ x := (G.ne_of_adj hxu).symm
          have hvx : v ≠ x := (G.ne_of_adj hxv).symm
          obtain ⟨p_raw, hp_raw⟩ := (reachable_induce_iff (U := {t : W | t ≠ x}) hux hxy.symm).mp
            ((h2G.2 x) ⟨u, hux⟩ ⟨y, hxy.symm⟩)
          set p0 := p_raw.toPath
          have hp0_sub : ∀ t ∈ p0.1.support, t ≠ x :=
            fun t ht ↦ hp_raw t (Walk.support_toPath_subset_support p_raw ht)
          obtain ⟨s, hsS, q, hq_path, hq_sub, hq_tail⟩ :=
            last_mem_suffix ({u, v} : Finset W) (by simp) p0.1 p0.2
          have hq_no_x : x ∉ q.support := fun hx ↦ hp0_sub x (hq_sub x hx) rfl
          simp only [Finset.mem_insert, Finset.mem_singleton] at hsS
          rcases hsS with rfl | rfl
          · have hv_not_q : v ∉ q.support := by
              intro hvq
              rw [support_eq_cons_tail q, List.mem_cons] at hvq
              rcases hvq with rfl | hv_tl
              · exact G.ne_of_adj huv rfl
              · exact hq_tail v hv_tl (by simp)
            set w1 : G.Walk x y := .cons hxu q
            set w2 : G.Walk x y := .cons hxv (.cons huv.symm q)
            have hw1 : w1.IsPath := Walk.IsPath.cons hq_path hq_no_x
            have hw2 : w2.IsPath := by
              apply Walk.IsPath.cons (Walk.IsPath.cons hq_path hv_not_q)
              simp only [Walk.support_cons, List.mem_cons, not_or]
              exact ⟨hvx.symm, hq_no_x⟩
            exact ⟨w1, w2, hw1, hw2, by simp [w1, w2]; omega⟩
          · have hu_not_q : u ∉ q.support := by
              intro huq
              rw [support_eq_cons_tail q, List.mem_cons] at huq
              rcases huq with rfl | hu_tl
              · exact G.ne_of_adj huv rfl
              · exact hq_tail u hu_tl (by simp)
            set w1 : G.Walk x y := .cons hxv q
            set w2 : G.Walk x y := .cons hxu (.cons huv q)
            have hw1 : w1.IsPath := Walk.IsPath.cons hq_path hq_no_x
            have hw2 : w2.IsPath := by
              apply Walk.IsPath.cons (Walk.IsPath.cons hq_path hu_not_q)
              simp only [Walk.support_cons, List.mem_cons, not_or]
              exact ⟨hux.symm, hq_no_x⟩
            exact ⟨w1, w2, hw1, hw2, by simp [w1, w2]; omega⟩
        · -- `N_G(x)` is an independent set (since `y ∉ N_G(x)` and no triangle on `x` in `G - y`).
          set Nx := G.neighborFinset x
          have hNx_card : 2 ≤ Nx.card := by
            rw [card_neighborFinset_eq_degree]
            exact h2G.two_le_degree (by omega) x
          have hy_not_Nx : y ∉ Nx := by simp [Nx, hadj_xy]
          have hx_not_Nx : x ∉ Nx := by simp [Nx]
          have hNx_indep : ∀ u1 ∈ Nx, ∀ u2 ∈ Nx, ¬ G.Adj u1 u2 := by
            intro u1 hu1 u2 hu2 hadj12
            apply htri
            exact ⟨u1, u2, fun h ↦ hy_not_Nx (h ▸ hu1), fun h ↦ hy_not_Nx (h ▸ hu2),
              (G.mem_neighborFinset _ _).mp hu1, (G.mem_neighborFinset _ _).mp hu2, hadj12⟩
          -- Step 5: Check whether `x` lies in a `4`-cycle `x - x1 - a - x2 - x` in `G - y`.
          by_cases hc4 : ∃ x1 x2 a : W, x1 ≠ x2 ∧ a ≠ x ∧ a ≠ y ∧
              x1 ∈ Nx ∧ x2 ∈ Nx ∧ G.Adj x1 a ∧ G.Adj x2 a
          · -- Step 6: `4`-cycle `x - x1 - a - x2 - x` in `G - y`!
            rcases hc4 with ⟨x1, x2, a, hx12, hax, hay, hx1Nx, hx2Nx, hx1a, hx2a⟩
            have hxx1 : G.Adj x x1 := (G.mem_neighborFinset _ _).mp hx1Nx
            have hxx2 : G.Adj x x2 := (G.mem_neighborFinset _ _).mp hx2Nx
            have ha_not_Nx : a ∉ Nx := fun haNx ↦ hNx_indep x1 hx1Nx a haNx hx1a
            have hx1_ne_y : x1 ≠ y := fun h ↦ hy_not_Nx (h ▸ hx1Nx)
            have hx2_ne_y : x2 ≠ y := fun h ↦ hy_not_Nx (h ▸ hx2Nx)
            have hx1_ne_x : x1 ≠ x := fun h ↦ hx_not_Nx (h ▸ hx1Nx)
            have hx2_ne_x : x2 ≠ x := fun h ↦ hx_not_Nx (h ▸ hx2Nx)
            have hx1_ne_a : x1 ≠ a := G.ne_of_adj hx1a
            have hx2_ne_a : x2 ≠ a := G.ne_of_adj hx2a
            set U := Finset.univ.filter (fun v ↦ v ≠ x ∧ v ≠ a)
            have hx1U : x1 ∈ U := by simp [U, hx1_ne_x, hx1_ne_a]
            have hx2U : x2 ∈ U := by simp [U, hx2_ne_x, hx2_ne_a]
            have hyU : y ∈ U := by simp [U, hxy.symm, hay.symm]
            by_cases hreach_y : ∃ s0 ∈ ({x1, x2} : Finset W),
                ∃ p : G.Walk s0 y, ∀ w ∈ p.support, w ∈ U
            · -- Case 6a: `{x1, x2}` reaches `y` in `G - {x, a}`!
              rcases hreach_y with ⟨s0, hs0, p_raw, hp_raw⟩
              set p0 := p_raw.toPath
              have hp0U : ∀ w ∈ p0.1.support, w ∈ U :=
                fun w hw ↦ hp_raw w (Walk.support_toPath_subset_support p_raw hw)
              obtain ⟨s, hsS, q, hq_path, hq_sub, hq_tail⟩ :=
                last_mem_suffix ({x1, x2} : Finset W) hs0 p0.1 p0.2
              have hqU : ∀ w ∈ q.support, w ≠ x ∧ w ≠ a := by
                intro w hw
                have hm := hp0U w (hq_sub w hw)
                simp only [U, Finset.mem_filter, Finset.mem_univ, true_and] at hm
                exact hm
              simp only [Finset.mem_insert, Finset.mem_singleton] at hsS
              rcases hsS with rfl | rfl
              · have hx2_not_q : x2 ∉ q.support := by
                  intro hm
                  rw [support_eq_cons_tail q, List.mem_cons] at hm
                  rcases hm with h_eq | htl
                  · exact hx12 h_eq.symm
                  · exact hq_tail x2 htl (by simp)
                set w1 : G.Walk x y := .cons hxx1 q
                set w2 : G.Walk x y := .cons hxx2 (.cons hx2a (.cons hx1a.symm q))
                have hw1 : w1.IsPath := Walk.IsPath.cons hq_path (fun hm ↦ (hqU x hm).1 rfl)
                have hw2 : w2.IsPath := by
                  have h1 : (Walk.cons hx1a.symm q).IsPath :=
                    Walk.IsPath.cons hq_path (fun hm ↦ (hqU a hm).2 rfl)
                  have h2 : (Walk.cons hx2a (.cons hx1a.symm q)).IsPath := by
                    apply Walk.IsPath.cons h1
                    simp only [Walk.support_cons, List.mem_cons, not_or]
                    exact ⟨hx2_ne_a, hx2_not_q⟩
                  apply Walk.IsPath.cons h2
                  simp only [Walk.support_cons, List.mem_cons, not_or]
                  exact ⟨hx2_ne_x.symm, hax.symm, fun hm ↦ (hqU x hm).1 rfl⟩
                exact ⟨w1, w2, hw1, hw2, by simp [w1, w2]; omega⟩
              · have hx1_not_q : x1 ∉ q.support := by
                  intro hm
                  rw [support_eq_cons_tail q, List.mem_cons] at hm
                  rcases hm with h_eq | htl
                  · exact hx12 h_eq
                  · exact hq_tail x1 htl (by simp)
                set w1 : G.Walk x y := .cons hxx2 q
                set w2 : G.Walk x y := .cons hxx1 (.cons hx1a (.cons hx2a.symm q))
                have hw1 : w1.IsPath := Walk.IsPath.cons hq_path (fun hm ↦ (hqU x hm).1 rfl)
                have hw2 : w2.IsPath := by
                  have h1 : (Walk.cons hx2a.symm q).IsPath :=
                    Walk.IsPath.cons hq_path (fun hm ↦ (hqU a hm).2 rfl)
                  have h2 : (Walk.cons hx1a (.cons hx2a.symm q)).IsPath := by
                    apply Walk.IsPath.cons h1
                    simp only [Walk.support_cons, List.mem_cons, not_or]
                    exact ⟨hx1_ne_a, hx1_not_q⟩
                  apply Walk.IsPath.cons h2
                  simp only [Walk.support_cons, List.mem_cons, not_or]
                  exact ⟨hx1_ne_x.symm, hax.symm, fun hm ↦ (hqU x hm).1 rfl⟩
                exact ⟨w1, w2, hw1, hw2, by simp [w1, w2]; omega⟩
            · -- Case 6b: `{x, a}` separates `{x1, x2}` from `y`!
              have hpick : ∃ xi ∈ ({x1, x2} : Finset W), xi ≠ z := by
                by_cases h1 : x1 ≠ z
                · exact ⟨x1, by simp, h1⟩
                · push Not at h1
                  exact ⟨x2, by simp, fun h2 ↦ hx12 (h1.trans h2.symm)⟩
              rcases hpick with ⟨xi, hxi_pair, hxi_ne_z⟩
              have hxiU : xi ∈ U := by
                simp only [Finset.mem_insert, Finset.mem_singleton] at hxi_pair
                rcases hxi_pair with rfl | rfl <;> assumption
              have hxxi : G.Adj x xi ∧ G.Adj xi a := by
                simp only [Finset.mem_insert, Finset.mem_singleton] at hxi_pair
                rcases hxi_pair with rfl | rfl
                · exact ⟨hxx1, hx1a⟩
                · exact ⟨hxx2, hx2a⟩
              set D := compIn G U xi
              have hxiD : xi ∈ D := self_mem_compIn hxiU
              have hy_not_D : y ∉ D := by
                intro hyD
                rcases mem_compIn_iff.mp hyD with ⟨_, p, hp⟩
                exact hreach_y ⟨xi, hxi_pair, p, hp⟩
              have hx_not_D : x ∉ D := fun hm ↦ by
                have h := compIn_subset hm; simp [U] at h
              have ha_not_D : a ∉ D := fun hm ↦ by
                have h := compIn_subset hm; simp [U] at h
              set SD := D ∪ ({x, a} : Finset W)
              have hxi_deg : 3 ≤ (G.induce (SD : Set W)).degree
                  ⟨xi, Finset.mem_coe.mpr (Finset.mem_union_left _ hxiD)⟩ := by
                rw [degree_induce_compIn_union hxiD]
                · exact hdeg xi (by rintro rfl; exact hx_not_D hxiD)
                    (by rintro rfl; exact hy_not_D hxiD) hxi_ne_z
                · intro w hw
                  simp only [U, Finset.mem_sdiff, Finset.mem_univ, Finset.mem_filter,
                    true_and, not_and_or, not_not] at hw
                  simp [ hw]
              have hSD_card : 4 ≤ SD.card := by
                have hlt := (G.induce (SD : Set W)).degree_lt_card_verts
                  ⟨xi, Finset.mem_coe.mpr (Finset.mem_union_left _ hxiD)⟩
                have hc_eq : Fintype.card (SD : Set W) = SD.card := by
                  convert Fintype.card_coe SD; exact Finset.mem_coe
                omega
              have hSD_lt : SD.card < Fintype.card W := by
                apply Finset.card_lt_card
                rw [Finset.ssubset_iff_of_subset (Finset.subset_univ _)]
                refine ⟨y, Finset.mem_univ y, ?_⟩
                simp [SD, hy_not_D, hxy.symm, hay.symm]
              set GD := G.induce (SD : Set W)
              set xD : {v : W // v ∈ (SD : Set W)} := ⟨x, by simp [SD]⟩
              set aD : {v : W // v ∈ (SD : Set W)} := ⟨a, by simp [SD]⟩
              set zD : {v : W // v ∈ (SD : Set W)} :=
                if hzSD : z ∈ (SD : Set W) then ⟨z, hzSD⟩ else xD
              have hxa_ne : xD ≠ aD := fun heq ↦ hax (Subtype.mk.inj heq).symm
              have h2GD : IsTwoConn (addEdge GD xD aD) := by
                set KD := addEdge GD xD aD
                have hadj_xa : KD.Adj xD aD := addEdge_adj_self GD hxa_ne
                have hD_conn := connected_induce_compIn (G := G) hxiU
                have hcut_xD : (KD.induce {t | t ≠ xD}).Connected := by
                  apply connected_induce_of_base aD hxa_ne.symm
                  intro t ht
                  by_cases hta : t = aD
                  · subst hta; exact Reachable.refl _
                  · have htD : t.1 ∈ D := by
                      have hm : t.1 ∈ SD := t.2
                      simp only [SD, Finset.mem_union, Finset.mem_insert,
                        Finset.mem_singleton] at hm
                      rcases hm with hm | h_eq | h_eq
                      · exact hm
                      · exact (ht (Subtype.ext h_eq)).elim
                      · exact (hta (Subtype.ext h_eq)).elim
                    obtain ⟨p⟩ := hD_conn ⟨xi, hxiD⟩ ⟨t.1, htD⟩
                    let mapD : ∀ {u v : {w : W // w ∈ (D : Set W)}}
                        (wlk : (G.induce (D : Set W)).Walk u v),
                        (KD.induce {z | z ≠ xD}).Walk
                          ⟨⟨u.1, Finset.mem_coe.mpr (Finset.mem_union_left _ u.2)⟩,
                            fun heq ↦ hx_not_D (Subtype.mk.inj heq ▸ u.2)⟩
                          ⟨⟨v.1, Finset.mem_coe.mpr (Finset.mem_union_left _ v.2)⟩,
                            fun heq ↦ hx_not_D (Subtype.mk.inj heq ▸ v.2)⟩ := by
                      intro u v wlk
                      induction wlk with
                      | nil => exact .nil
                      | @cons u1 u2 _ hadj tl ihtl =>
                        have hadj' : (KD.induce {z | z ≠ xD}).Adj
                            ⟨⟨u1.1, Finset.mem_coe.mpr (Finset.mem_union_left _ u1.2)⟩,
                              fun heq ↦ hx_not_D (Subtype.mk.inj heq ▸ u1.2)⟩
                            ⟨⟨u2.1, Finset.mem_coe.mpr (Finset.mem_union_left _ u2.2)⟩,
                              fun heq ↦ hx_not_D (Subtype.mk.inj heq ▸ u2.2)⟩ :=
                          Or.inl (induce_adj_val hadj)
                        exact .cons hadj' ihtl
                    have hxi_sub : (⟨xi, Finset.mem_coe.mpr (Finset.mem_union_left _ hxiD)⟩ :
                        {v : W // v ∈ (SD : Set W)}) ≠ xD :=
                      fun heq ↦ hx_not_D (Subtype.mk.inj heq ▸ hxiD)
                    have hadj_a_xi : (KD.induce {z | z ≠ xD}).Adj ⟨aD, hxa_ne.symm⟩ ⟨_, hxi_sub⟩ :=
                      Or.inl hxxi.2.symm
                    exact hadj_a_xi.reachable.trans ⟨mapD p⟩
                have hcut_aD : (KD.induce {t | t ≠ aD}).Connected := by
                  apply connected_induce_of_base xD hxa_ne
                  intro t ht
                  by_cases htx : t = xD
                  · subst htx; exact Reachable.refl _
                  · have htD : t.1 ∈ D := by
                      have hm : t.1 ∈ SD := t.2
                      simp only [SD, Finset.mem_union, Finset.mem_insert,
                        Finset.mem_singleton] at hm
                      rcases hm with hm | h_eq | h_eq
                      · exact hm
                      · exact (htx (Subtype.ext h_eq)).elim
                      · exact (ht (Subtype.ext h_eq)).elim
                    obtain ⟨p⟩ := hD_conn ⟨xi, hxiD⟩ ⟨t.1, htD⟩
                    let mapD : ∀ {u v : {w : W // w ∈ (D : Set W)}}
                        (wlk : (G.induce (D : Set W)).Walk u v),
                        (KD.induce {z | z ≠ aD}).Walk
                          ⟨⟨u.1, Finset.mem_coe.mpr (Finset.mem_union_left _ u.2)⟩,
                            fun heq ↦ ha_not_D (Subtype.mk.inj heq ▸ u.2)⟩
                          ⟨⟨v.1, Finset.mem_coe.mpr (Finset.mem_union_left _ v.2)⟩,
                            fun heq ↦ ha_not_D (Subtype.mk.inj heq ▸ v.2)⟩ := by
                      intro u v wlk
                      induction wlk with
                      | nil => exact .nil
                      | @cons u1 u2 _ hadj tl ihtl =>
                        have hadj' : (KD.induce {z | z ≠ aD}).Adj
                            ⟨⟨u1.1, Finset.mem_coe.mpr (Finset.mem_union_left _ u1.2)⟩,
                              fun heq ↦ ha_not_D (Subtype.mk.inj heq ▸ u1.2)⟩
                            ⟨⟨u2.1, Finset.mem_coe.mpr (Finset.mem_union_left _ u2.2)⟩,
                              fun heq ↦ ha_not_D (Subtype.mk.inj heq ▸ u2.2)⟩ :=
                          Or.inl (induce_adj_val hadj)
                        exact .cons hadj' ihtl
                    have hxi_sub : (⟨xi, Finset.mem_coe.mpr (Finset.mem_union_left _ hxiD)⟩ :
                        {v : W // v ∈ (SD : Set W)}) ≠ aD :=
                      fun heq ↦ ha_not_D (Subtype.mk.inj heq ▸ hxiD)
                    have hadj_x_xi : (KD.induce {z | z ≠ aD}).Adj ⟨xD, hxa_ne⟩ ⟨_, hxi_sub⟩ :=
                      Or.inl hxxi.1
                    exact hadj_x_xi.reachable.trans ⟨mapD p⟩
                refine ⟨?_, fun c ↦ ?_⟩
                · have hr0 : ∀ t, KD.Reachable xD t := by
                    intro t
                    by_cases hta : t = aD
                    · subst hta; exact hadj_xa.reachable
                    · obtain ⟨p⟩ := hcut_aD ⟨xD, hxa_ne⟩ ⟨t, hta⟩
                      exact ⟨liftWalk p⟩
                  exact @Connected.mk _ KD (fun t1 t2 ↦ (hr0 t1).symm.trans (hr0 t2)) ⟨xD⟩
                · by_cases hcx : c = xD
                  · subst hcx; exact hcut_xD
                  · by_cases hca : c = aD
                    · subst hca; exact hcut_aD
                    · have hcD : c.1 ∈ D := by
                        have hm : c.1 ∈ SD := c.2
                        simp only [SD, Finset.mem_union, Finset.mem_insert,
                          Finset.mem_singleton] at hm
                        rcases hm with hm | h_eq | h_eq
                        · exact hm
                        · exact (hcx (Subtype.ext h_eq)).elim
                        · exact (hca (Subtype.ext h_eq)).elim
                      have hx_ne_c : xD ≠ c := Ne.symm hcx
                      have ha_ne_c : aD ≠ c := Ne.symm hca
                      have hadj_xa_sub : (KD.induce {t | t ≠ c}).Adj ⟨xD, hx_ne_c⟩ ⟨aD, ha_ne_c⟩ :=
                        hadj_xa
                      apply connected_induce_of_base xD hx_ne_c
                      intro t ht
                      by_cases htx : t = xD
                      · subst htx; exact Reachable.refl _
                      · by_cases hta : t = aD
                        · subst hta; exact hadj_xa_sub.reachable
                        · have htD : t.1 ∈ D := by
                            have hm : t.1 ∈ SD := t.2
                            simp only [SD, Finset.mem_union, Finset.mem_insert,
                              Finset.mem_singleton] at hm
                            rcases hm with hm | h_eq | h_eq
                            · exact hm
                            · exact (htx (Subtype.ext h_eq)).elim
                            · exact (hta (Subtype.ext h_eq)).elim
                          have htc1 : t.1 ≠ c.1 := fun heq ↦ ht (Subtype.ext heq)
                          have hyc1 : y ≠ c.1 := fun h ↦ hy_not_D (h ▸ hcD)
                          obtain ⟨p, hp⟩ := (reachable_induce_iff (U := {v : W | v ≠ c.1})
                            htc1 hyc1).mp ((h2G.2 c.1) ⟨t.1, htc1⟩ ⟨y, hyc1⟩)
                          obtain ⟨q', hq'D, w, hwD, hadj_qw, _, r, hr⟩ :=
                            first_exit D htD hy_not_D p
                          have hw_xa : w = x ∨ w = a := by
                            by_contra hnot
                            push Not at hnot
                            have hwU : w ∈ U := by simp [U, hnot.1, hnot.2]
                            exact compIn_no_edge_out hq'D hwU hwD hadj_qw
                          have hq'_sub : (⟨q', Finset.mem_coe.mpr (Finset.mem_union_left _ hq'D)⟩ :
                              {v : W // v ∈ (SD : Set W)}) ≠ c := by
                            intro heq
                            have hqc : q' = c.1 := Subtype.mk.inj heq
                            exact hp q' (hr q' (Walk.end_mem_support r)).2 hqc
                          have liftToKD : ∀ {u v : W} (hu : u ∈ D) (hv : v ∈ D)
                              (huc : (⟨u, Finset.mem_coe.mpr (Finset.mem_union_left _ hu)⟩ :
                                {w : W // w ∈ (SD : Set W)}) ≠ c)
                              (hvc : (⟨v, Finset.mem_coe.mpr (Finset.mem_union_left _ hv)⟩ :
                                {w : W // w ∈ (SD : Set W)}) ≠ c)
                              (wlk : G.Walk u v),
                              (∀ s ∈ wlk.support, ∃ hs : s ∈ D,
                                (⟨s, Finset.mem_coe.mpr (Finset.mem_union_left _ hs)⟩ :
                                  {w : W // w ∈ (SD : Set W)}) ≠ c) →
                              (KD.induce {z | z ≠ c}).Reachable ⟨_, huc⟩ ⟨_, hvc⟩ := by
                            intro u v hu hv huc hv_c wlk
                            induction wlk with
                            | nil => intro _; exact Reachable.refl _
                            | @cons s1 s2 s3 hadj_s tl ihtl =>
                              intro hmem
                              obtain ⟨hs2D, hs2c⟩ := hmem s2 (by simp)
                              have hadj_KD : (KD.induce {z | z ≠ c}).Adj ⟨_, huc⟩ ⟨_, hs2c⟩ :=
                                Or.inl hadj_s
                              exact hadj_KD.reachable.trans
                                (ihtl hs2D hv hs2c hv_c (fun s hs ↦ hmem s (by simp [hs])))
                          have hr_KD : (KD.induce {z | z ≠ c}).Reachable ⟨t, ht⟩ ⟨_, hq'_sub⟩ := by
                            have ht_eq : (⟨t.1, Finset.mem_coe.mpr (Finset.mem_union_left _ htD)⟩ :
                                {w : W // w ∈ (SD : Set W)}) = t := Subtype.ext rfl
                            have hr0_KD := liftToKD htD hq'D (ht_eq.symm ▸ ht) hq'_sub r
                              (fun s hs ↦ ⟨(hr s hs).1, fun heq ↦ hp s (hr s hs).2 (Subtype.mk.inj heq)⟩)
                            convert hr0_KD
                          rcases hw_xa with hwx | hwa
                          · rw [hwx] at hadj_qw
                            have hadj_xq : (KD.induce {z | z ≠ c}).Adj ⟨xD, hx_ne_c⟩ ⟨_, hq'_sub⟩ :=
                              Or.inl hadj_qw.symm
                            exact hadj_xq.reachable.trans hr_KD.symm
                          · rw [hwa] at hadj_qw
                            have hadj_aq : (KD.induce {z | z ≠ c}).Adj ⟨aD, ha_ne_c⟩ ⟨_, hq'_sub⟩ :=
                              Or.inl hadj_qw.symm
                            exact hadj_xa_sub.reachable.trans (hadj_aq.reachable.trans hr_KD.symm)
              have hdegGD : ∀ v : {w : W // w ∈ (SD : Set W)},
                  v ≠ xD → v ≠ aD → v ≠ zD → 3 ≤ GD.degree v := by
                intro v hvx hva hvz
                have hvD : v.1 ∈ D := by
                  have hm : v.1 ∈ SD := v.2
                  simp only [SD, Finset.mem_union, Finset.mem_insert,
                    Finset.mem_singleton] at hm
                  rcases hm with hm | h_eq | h_eq
                  · exact hm
                  · exact (hvx (Subtype.ext h_eq)).elim
                  · exact (hva (Subtype.ext h_eq)).elim
                have hv_eq : (⟨v.1, Finset.mem_coe.mpr (Finset.mem_union_left _ hvD)⟩ :
                    {w : W // w ∈ (SD : Set W)}) = v := Subtype.ext rfl
                rw [← hv_eq, degree_induce_compIn_union hvD]
                · apply hdeg v.1 (fun h ↦ hvx (Subtype.ext h)) (fun h ↦ hy_not_D (h ▸ hvD))
                  intro hzv
                  apply hvz
                  dsimp only [zD]
                  rw [dif_pos (hzv ▸ v.2)]
                  exact Subtype.ext hzv
                · intro w hw
                  simp only [U, Finset.mem_sdiff, Finset.mem_univ, Finset.mem_filter,
                    true_and, not_and_or, not_not] at hw
                  simp [hw]
              have hc_GD : Fintype.card (SD : Set W) = SD.card := by
                convert Fintype.card_coe SD; exact Finset.mem_coe
              have hcardGD : 4 ≤ Fintype.card (SD : Set W) := by omega
              have hltGD : Fintype.card (SD : Set W) < Fintype.card W := by omega
              obtain ⟨q1, q2, hq1_path, hq2_path, hq_mod⟩ :=
                ih (Fintype.card W ^ 3 - 1) hM_pos GD xD aD zD
                  (card_cube_add_edges_le_pred GD hltGD) hcardGD hxa_ne h2GD hdegGD
              -- Connect `a` to `y` in `G - x` via a simple path `r_ay`; it cannot enter `D`!
              obtain ⟨r_raw, hr_raw⟩ := (reachable_induce_iff (U := {v : W | v ≠ x})
                hax hxy.symm).mp ((h2G.2 x) ⟨a, hax⟩ ⟨y, hxy.symm⟩)
              set r_ay := r_raw.toPath
              have hray_no_x : ∀ w ∈ r_ay.1.support, w ≠ x :=
                fun w hw ↦ hr_raw w (Walk.support_toPath_subset_support r_raw hw)
              have hray_no_D : ∀ w ∈ r_ay.1.support, w ∉ D := by
                intro w hw hwD
                have hw_ne_a : w ≠ a := fun h ↦ ha_not_D (h ▸ hwD)
                set sub := r_ay.1.dropUntil w hw
                obtain ⟨q', hq'D, w_out, hw_outD, hadj_out, hw_out_supp, _⟩ :=
                  first_exit D hwD hy_not_D sub
                have hw_out_ne_x : w_out ≠ x :=
                  hray_no_x w_out (Walk.support_dropUntil_subset_support r_ay.1 hw hw_out_supp)
                have hw_out_eq_a : w_out = a := by
                  by_contra hnea
                  have hwU : w_out ∈ U := by simp [U, hw_out_ne_x, hnea]
                  exact compIn_no_edge_out hq'D hwU hw_outD hadj_out
                subst w_out
                -- `a` is the start of `r_ay.1`, AND `a ∈ sub.support` where `sub` starts at `w ≠ a`!
                have hspec := Walk.take_spec r_ay.1 hw
                have hnd := r_ay.2.support_nodup
                rw [← hspec, Walk.support_append, List.nodup_append'] at hnd
                have ha_pref : a ∈ (r_ay.1.takeUntil w hw).support := Walk.start_mem_support _
                have ha_sub_tl : a ∈ sub.support.tail := by
                  rw [support_eq_cons_tail sub, List.mem_cons] at hw_out_supp
                  rcases hw_out_supp with h_eq | htl
                  · exact (hw_ne_a h_eq.symm).elim
                  · exact htl
                exact List.disjoint_left.mp hnd.2.2 ha_pref ha_sub_tl
              set lq1 : G.Walk x a := liftWalk q1
              set lq2 : G.Walk x a := liftWalk q2
              have hlq1_inter : ∀ t ∈ lq1.support, t ∈ r_ay.1.support → t = a := by
                intro t ht1 ht2
                have htSD : t ∈ SD := Finset.mem_coe.mp (support_liftWalk_subset q1 t ht1)
                simp only [SD, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at htSD
                rcases htSD with htD | htx | hta
                · exact (hray_no_D t ht2 htD).elim
                · exact (hray_no_x t ht2 htx).elim
                · exact hta
              have hlq2_inter : ∀ t ∈ lq2.support, t ∈ r_ay.1.support → t = a := by
                intro t ht1 ht2
                have htSD : t ∈ SD := Finset.mem_coe.mp (support_liftWalk_subset q2 t ht1)
                simp only [SD, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at htSD
                rcases htSD with htD | htx | hta
                · exact (hray_no_D t ht2 htD).elim
                · exact (hray_no_x t ht2 htx).elim
                · exact hta
              refine ⟨lq1.append r_ay.1, lq2.append r_ay.1,
                append_isPath (isPath_liftWalk hq1_path) r_ay.2 hlq1_inter,
                append_isPath (isPath_liftWalk hq2_path) r_ay.2 hlq2_inter, ?_⟩
              simp only [Walk.length_append, lq1, lq2, length_liftWalk]
              omega
          · -- Step 5 (No `4`-cycle on `x` in `G - y`): `|N_G(v) ∩ Nx| ≤ 1` for all `v ∉ {x, y}`!
            have hle1_Nx : ∀ v : W, v ≠ x → v ≠ y → (G.neighborFinset v ∩ Nx).card ≤ 1 := by
              intro v hvx hvy
              rw [Finset.card_le_one]
              intro u1 hu1 u2 hu2
              by_contra hne12
              rw [Finset.mem_inter, SimpleGraph.mem_neighborFinset] at hu1 hu2
              exact hc4 ⟨u1, u2, v, hne12, hvx, hvy, hu1.2, hu2.2, hu1.1.symm, hu2.1.symm⟩
            set U := Finset.univ \ insert x Nx
            have hyU : y ∈ U := by simp [U, hxy.symm, hy_not_Nx]
            set A := compIn G U y
            have hyA : y ∈ A := self_mem_compIn hyU
            have hx_not_A : x ∉ A := fun hm ↦ by
              have h := compIn_subset hm; simp [U] at h
            have hdisj_A_Nx : Disjoint A Nx := by
              rw [Finset.disjoint_left]
              intro w hwA hwNx
              have h := compIn_subset hwA
              simp [U, hwNx] at h
            have hbdy_A : ∀ a ∈ A, ∀ w ∉ A, G.Adj a w → w ∈ Nx := by
              intro a haA w hwA hadj
              by_cases hwU : w ∈ U
              · exact (compIn_no_edge_out haA hwU hwA hadj).elim
              · simp only [U, Finset.mem_sdiff, Finset.mem_univ, true_and, not_not,
                  Finset.mem_insert] at hwU
                rcases hwU with rfl | hwNx
                · exfalso
                  have haNx : a ∈ Nx := (G.mem_neighborFinset _ _).mpr hadj.symm
                  exact Finset.disjoint_left.mp hdisj_A_Nx haA haNx
                · exact hwNx
            -- Split on `A.card`: `3 ≤ A.card`, `A.card = 2`, or `A.card = 1` (`A = {y}`).
            by_cases hA3 : 3 ≤ A.card
            · -- Subcase 5a1: `3 ≤ A.card`, apply IH to `contractOne G A Nx`.
              set B1 := contractOne G A Nx
              have hA_ge2 : 2 ≤ (compIn G U y).card := by change 2 ≤ A.card; omega
              have h2B1 : IsTwoConn B1 :=
                isTwoConn_contractOne h2G hyU hA_ge2 hx_not_A hbdy_A
              set yB : Option {v : W // v ∈ A} := some ⟨y, hyA⟩
              set zB : Option {v : W // v ∈ A} :=
                if hzA : z ∈ A then some ⟨z, hzA⟩ else none
              have h2B1_add : IsTwoConn (addEdge B1 none yB) :=
                h2B1.mono (le_addEdge B1 none yB)
              have hcardB1 : 4 ≤ Fintype.card (Option {v : W // v ∈ A}) := by
                simp [Fintype.card_option, Fintype.card_coe]
                omega
              have hltB1 : Fintype.card (Option {v : W // v ∈ A}) < Fintype.card W := by
                simp only [Fintype.card_option, Fintype.card_coe]
                have hdisj_ins : Disjoint A (insert x Nx) := by
                  rw [Finset.disjoint_insert_right]
                  exact ⟨hx_not_A, hdisj_A_Nx⟩
                have hle_univ : (A ∪ insert x Nx).card ≤ Fintype.card W :=
                  Finset.card_le_univ _
                rw [Finset.card_union_of_disjoint hdisj_ins,
                  Finset.card_insert_of_notMem hx_not_Nx] at hle_univ
                omega
              have hdegB1 : ∀ o : Option {v : W // v ∈ A},
                  o ≠ none → o ≠ yB → o ≠ zB → 3 ≤ B1.degree o := by
                intro o hon hoy hoz
                cases o with
                | none => exact (hon rfl).elim
                | some a =>
                  have ha_ne_x : a.1 ≠ x := fun h ↦ hx_not_A (h ▸ a.2)
                  have ha_ne_y : a.1 ≠ y := fun heq ↦ hoy (congrArg some (Subtype.ext heq))
                  have ha_ne_z : a.1 ≠ z := by
                    intro hza
                    apply hoz
                    dsimp only [zB]
                    rw [dif_pos (hza ▸ a.2)]
                    exact congrArg some (Subtype.ext hza)
                  exact (hdeg a.1 ha_ne_x ha_ne_y ha_ne_z).trans
                    (degree_le_contractOne a (hbdy_A a.1 a.2) (hle1_Nx a.1 ha_ne_x ha_ne_y))
              obtain ⟨q1, q2, hq1_path, hq2_path, hq_mod⟩ :=
                ih (Fintype.card W ^ 3 - 1) hM_pos B1 none yB zB
                  (card_cube_add_edges_le_pred B1 hltB1)
                  hcardB1 (Option.some_ne_none _).symm h2B1_add hdegB1
              obtain ⟨u1, hu1Nx, r1, hr1_path, hr1_len, hr1_tl⟩ :=
                lift_walk_contractOne hdisj_A_Nx q1 hq1_path
              obtain ⟨u2, hu2Nx, r2, hr2_path, hr2_len, hr2_tl⟩ :=
                lift_walk_contractOne hdisj_A_Nx q2 hq2_path
              have hx_not_r1 : x ∉ r1.support := by
                rw [support_eq_cons_tail r1, List.mem_cons, not_or]
                exact ⟨fun h ↦ hx_not_Nx (h ▸ hu1Nx), fun hm ↦ hx_not_A (hr1_tl x hm)⟩
              have hx_not_r2 : x ∉ r2.support := by
                rw [support_eq_cons_tail r2, List.mem_cons, not_or]
                exact ⟨fun h ↦ hx_not_Nx (h ▸ hu2Nx), fun hm ↦ hx_not_A (hr2_tl x hm)⟩
              refine ⟨.cons ((G.mem_neighborFinset _ _).mp hu1Nx) r1,
                .cons ((G.mem_neighborFinset _ _).mp hu2Nx) r2,
                Walk.IsPath.cons hr1_path hx_not_r1,
                Walk.IsPath.cons hr2_path hx_not_r2, ?_⟩
              simp only [Walk.length_cons, hr1_len, hr2_len]
              omega
            · by_cases hA2 : A.card = 2
              · -- Subcase 5a2: `A.card = 2`, say `A = {y, w}` with `w ≠ y`.
                obtain ⟨w, hwA, hwy⟩ := Finset.exists_mem_ne (by omega : 1 < A.card) y
                have hpair_sub : ({y, w} : Finset W) ⊆ A := by
                  intro t ht
                  simp only [Finset.mem_insert, Finset.mem_singleton] at ht
                  rcases ht with rfl | rfl <;> assumption
                have hA_eq : A = {y, w} :=
                  (Finset.eq_of_subset_of_card_le hpair_sub
                    (by rw [hA2, Finset.card_pair hwy.symm])).symm
                have hw_ne_x : w ≠ x := fun h ↦ hx_not_A (h ▸ hwA)
                have hw_nb_sub : G.neighborFinset w ⊆ insert y (G.neighborFinset w ∩ Nx) := by
                  intro t ht
                  have hadj_wt : G.Adj w t := (G.mem_neighborFinset _ _).mp ht
                  by_cases htA : t ∈ A
                  · rw [hA_eq, Finset.mem_insert, Finset.mem_singleton] at htA
                    rcases htA with hty | htw
                    · rw [hty]; exact Finset.mem_insert_self y _
                    · exact (G.ne_of_adj hadj_wt htw.symm).elim
                  · exact Finset.mem_insert_of_mem
                      (Finset.mem_inter.mpr ⟨ht, hbdy_A w hwA t htA hadj_wt⟩)
                have hw_deg_le : G.degree w ≤ 2 := by
                  rw [← card_neighborFinset_eq_degree]
                  have hc1 := Finset.card_le_card hw_nb_sub
                  have hc2 := Finset.card_insert_le y (G.neighborFinset w ∩ Nx)
                  have hc3 := hle1_Nx w hw_ne_x hwy
                  omega
                have hw_deg_ge : 2 ≤ G.degree w := h2G.two_le_degree (by omega) w
                have hw_eq_z : w = z := by
                  by_contra hwz
                  have := hdeg w hw_ne_x hwy hwz
                  omega
                have hwy_not_inter : y ∉ G.neighborFinset w ∩ Nx :=
                  fun hm ↦ hy_not_Nx (Finset.mem_inter.mp hm).2
                have hw_card_eq : (insert y (G.neighborFinset w ∩ Nx)).card = 2 := by
                  have hc1 := Finset.card_le_card hw_nb_sub
                  rw [card_neighborFinset_eq_degree] at hc1
                  have hc2 : (insert y (G.neighborFinset w ∩ Nx)).card ≤ 2 := by
                    rw [Finset.card_insert_of_notMem hwy_not_inter]
                    have := hle1_Nx w hw_ne_x hwy
                    omega
                  omega
                have hw_nb_eq : G.neighborFinset w = insert y (G.neighborFinset w ∩ Nx) :=
                  Finset.eq_of_subset_of_card_le hw_nb_sub (by
                    rw [card_neighborFinset_eq_degree, hw_card_eq]; omega)
                have hadj_wy : G.Adj w y := by
                  have hm : y ∈ G.neighborFinset w := by rw [hw_nb_eq]; simp
                  exact (G.mem_neighborFinset _ _).mp hm
                have hw_inter_card : (G.neighborFinset w ∩ Nx).card = 1 := by
                  rw [Finset.card_insert_of_notMem hwy_not_inter] at hw_card_eq
                  omega
                obtain ⟨uw, huw_eq⟩ := Finset.card_eq_one.mp hw_inter_card
                have huw_mem : uw ∈ G.neighborFinset w ∩ Nx := by rw [huw_eq]; simp
                have hadj_w_uw : G.Adj w uw := (G.mem_neighborFinset _ _).mp (Finset.mem_inter.mp huw_mem).1
                have huw_Nx : uw ∈ Nx := (Finset.mem_inter.mp huw_mem).2
                -- Check if `y` has a neighbor `uy ∈ Nx` with `uy ≠ uw`.
                by_cases hex_uy : ∃ uy ∈ Nx, G.Adj uy y ∧ uy ≠ uw
                · rcases hex_uy with ⟨uy, huy_Nx, hadj_uy_y, huy_ne_uw⟩
                  have hadj_x_uy : G.Adj x uy := (G.mem_neighborFinset _ _).mp huy_Nx
                  have hadj_x_uw : G.Adj x uw := (G.mem_neighborFinset _ _).mp huw_Nx
                  set p1 : G.Walk x y := .cons hadj_x_uy (.cons hadj_uy_y .nil)
                  set p2 : G.Walk x y := .cons hadj_x_uw (.cons hadj_w_uw.symm (.cons hadj_wy .nil))
                  have hp1 : p1.IsPath := by
                    apply Walk.IsPath.cons (Walk.IsPath.cons Walk.IsPath.nil (by simp [G.ne_of_adj hadj_uy_y]))
                    simp only [Walk.support_cons, Walk.support_nil, List.mem_cons,
                      List.not_mem_nil, or_false, not_or]
                    exact ⟨G.ne_of_adj hadj_x_uy, hxy⟩
                  have hp2 : p2.IsPath := by
                    have hs1 : (Walk.cons hadj_wy .nil).IsPath :=
                      Walk.IsPath.cons Walk.IsPath.nil (by simp [hwy])
                    have hs2 : (Walk.cons hadj_w_uw.symm (.cons hadj_wy .nil)).IsPath := by
                      apply Walk.IsPath.cons hs1
                      simp only [Walk.support_cons, Walk.support_nil, List.mem_cons,
                        List.not_mem_nil, or_false, not_or]
                      exact ⟨(G.ne_of_adj hadj_w_uw).symm, fun h ↦ hy_not_Nx (h ▸ huw_Nx)⟩
                    apply Walk.IsPath.cons hs2
                    simp only [Walk.support_cons, Walk.support_nil, List.mem_cons,
                      List.not_mem_nil, or_false, not_or]
                    exact ⟨G.ne_of_adj hadj_x_uw, hw_ne_x.symm, hxy⟩
                  exact ⟨p1, p2, hp1, hp2, by simp [p1, p2]⟩
                · -- Otherwise `uw` separates `A = {y, w}` from `x`, contradicting `IsTwoConn G`!
                  push Not at hex_uy
                  exfalso
                  have hy_ne_uw : y ≠ uw := fun h ↦ hy_not_Nx (h.symm ▸ huw_Nx)
                  have hx_ne_uw : x ≠ uw := fun h ↦ hx_not_Nx (h.symm ▸ huw_Nx)
                  obtain ⟨p, hp⟩ := (reachable_induce_iff (U := {t : W | t ≠ uw})
                    hy_ne_uw hx_ne_uw).mp ((h2G.2 uw) ⟨y, hy_ne_uw⟩ ⟨x, hx_ne_uw⟩)
                  obtain ⟨q', hq'A, t_out, ht_outA, hadj_qt, ht_supp, _⟩ :=
                    first_exit A hyA hx_not_A p
                  have ht_Nx : t_out ∈ Nx := hbdy_A q' hq'A t_out ht_outA hadj_qt
                  have ht_ne_uw : t_out ≠ uw := hp t_out ht_supp
                  rw [hA_eq, Finset.mem_insert, Finset.mem_singleton] at hq'A
                  rcases hq'A with hqy | hqw
                  · rw [hqy] at hadj_qt
                    exact ht_ne_uw (hex_uy t_out ht_Nx hadj_qt.symm)
                  · rw [hqw] at hadj_qt
                    have hm : t_out ∈ G.neighborFinset w ∩ Nx :=
                      Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hadj_qt, ht_Nx⟩
                    rw [huw_eq, Finset.mem_singleton] at hm
                    exact ht_ne_uw hm
              · -- Subcase 5b: `A.card = 1`, i.e., `A = {y}`, so `G.neighborFinset y = Nx`!
                have hA1 : A.card = 1 := by
                  have hpos : 1 ≤ A.card := Finset.card_pos.mpr ⟨y, hyA⟩
                  omega
                obtain ⟨y0, hy0_eq⟩ := Finset.card_eq_one.mp hA1
                have hy0_y : y = y0 := Finset.mem_singleton.mp (hy0_eq ▸ hyA)
                subst hy0_y
                have hy_sub_Nx : G.neighborFinset y ⊆ Nx := by
                  intro t ht
                  have hadj_yt : G.Adj y t := (G.mem_neighborFinset _ _).mp ht
                  have ht_not_A : t ∉ A := by
                    rw [hy0_eq, Finset.mem_singleton]
                    exact (G.ne_of_adj hadj_yt).symm
                  exact hbdy_A y hyA t ht_not_A hadj_yt
                have hy_eq_Nx : G.neighborFinset y = Nx := by
                  apply Finset.eq_of_subset_of_card_le hy_sub_Nx
                  rw [card_neighborFinset_eq_degree, card_neighborFinset_eq_degree]
                  exact hdeg_le
                -- Pick `u ∈ Nx` with `u ≠ z`.
                have hex_u : ∃ u ∈ Nx, u ≠ z := by
                  by_cases hzNx : z ∈ Nx
                  · obtain ⟨u, huNx, huz⟩ := Finset.exists_mem_ne hNx_card z
                    exact ⟨u, huNx, huz⟩
                  · obtain ⟨u, huNx⟩ := Finset.card_pos.mp (by omega : 0 < Nx.card)
                    exact ⟨u, huNx, fun h ↦ hzNx (h ▸ huNx)⟩
                rcases hex_u with ⟨u, huNx, huz⟩
                have hux : u ≠ x := fun h ↦ hx_not_Nx (h ▸ huNx)
                have huy : u ≠ y := fun h ↦ hy_not_Nx (h ▸ huNx)
                have hu_deg : 3 ≤ G.degree u := hdeg u hux huy huz
                have hu_out : ∃ d0 : W, d0 ∉ insert x (insert y Nx) ∧ G.Adj u d0 := by
                  by_contra hall
                  push Not at hall
                  have hsub : G.neighborFinset u ⊆ ({x, y} : Finset W) := by
                    intro t ht
                    have hadj_ut : G.Adj u t := (G.mem_neighborFinset _ _).mp ht
                    have hmem : t ∈ insert x (insert y Nx) := by
                      by_contra hnot
                      exact hall t hnot hadj_ut
                    simp only [Finset.mem_insert] at hmem
                    rcases hmem with htx | hty | htNx
                    · rw [htx]; simp
                    · rw [hty]; simp
                    · exact (hNx_indep u huNx t htNx hadj_ut).elim
                  have hc1 := Finset.card_le_card hsub
                  have hc2 : ({x, y} : Finset W).card ≤ 2 := Finset.card_le_two
                  rw [card_neighborFinset_eq_degree] at hc1
                  omega
                rcases hu_out with ⟨d0, hd0_out, hadj_ud0⟩
                set U' := Finset.univ \ insert x (insert y Nx)
                have hd0U' : d0 ∈ U' := Finset.mem_sdiff.mpr ⟨Finset.mem_univ d0, hd0_out⟩
                set D := compIn G U' d0
                have hd0D : d0 ∈ D := self_mem_compIn hd0U'
                have hdisj_D_ins : Disjoint D (insert x (insert y Nx)) := by
                  rw [Finset.disjoint_left]
                  intro t htD hmem
                  exact (Finset.mem_sdiff.mp (compIn_subset htD)).2 hmem
                have hx_not_D : x ∉ D :=
                  fun hm ↦ Finset.disjoint_left.mp hdisj_D_ins hm (by simp)
                have hy_not_D : y ∉ D :=
                  fun hm ↦ Finset.disjoint_left.mp hdisj_D_ins hm (by simp)
                have hdisj_D_Nx : Disjoint D Nx := by
                  rw [Finset.disjoint_left]
                  intro t htD htNx
                  exact Finset.disjoint_left.mp hdisj_D_ins htD (by simp [htNx])
                have hbdy_D : ∀ d ∈ D, ∀ w ∉ D, G.Adj d w → w ∈ Nx := by
                  intro d hdD w hwD hadj_dw
                  by_cases hwU' : w ∈ U'
                  · exact (compIn_no_edge_out hdD hwU' hwD hadj_dw).elim
                  · simp only [U', Finset.mem_sdiff, Finset.mem_univ, true_and, not_not,
                      Finset.mem_insert] at hwU'
                    rcases hwU' with hwx | hwy | hwNx
                    · exfalso
                      rw [hwx] at hadj_dw
                      exact Finset.disjoint_left.mp hdisj_D_Nx hdD ((G.mem_neighborFinset _ _).mpr hadj_dw.symm)
                    · exfalso
                      rw [hwy] at hadj_dw
                      have hd_nb_y : d ∈ G.neighborFinset y := (G.mem_neighborFinset _ _).mpr hadj_dw.symm
                      rw [hy_eq_Nx] at hd_nb_y
                      exact Finset.disjoint_left.mp hdisj_D_Nx hdD hd_nb_y
                    · exact hwNx
                have hD_card : 2 ≤ D.card := by
                  by_contra hlt2
                  have hD1 : D.card = 1 := by
                    have hpos : 1 ≤ D.card := Finset.card_pos.mpr ⟨d0, hd0D⟩
                    omega
                  obtain ⟨d1, hd1_eq⟩ := Finset.card_eq_one.mp hD1
                  have hd1_d0 : d0 = d1 := Finset.mem_singleton.mp (hd1_eq ▸ hd0D)
                  subst hd1_d0
                  have hsub_d0 : G.neighborFinset d0 ⊆ G.neighborFinset d0 ∩ Nx := by
                    intro t ht
                    have hadj_dt : G.Adj d0 t := (G.mem_neighborFinset _ _).mp ht
                    have ht_not_D : t ∉ D := by
                      rw [hd1_eq, Finset.mem_singleton]
                      exact (G.ne_of_adj hadj_dt).symm
                    exact Finset.mem_inter.mpr ⟨ht, hbdy_D d0 hd0D t ht_not_D hadj_dt⟩
                  have hc1 := Finset.card_le_card hsub_d0
                  rw [card_neighborFinset_eq_degree] at hc1
                  have hc2 := hle1_Nx d0 (fun h ↦ hx_not_D (h ▸ hd0D)) (fun h ↦ hy_not_D (h ▸ hd0D))
                  have hc3 := h2G.two_le_degree (by omega) d0
                  omega
                set ND := Nx.filter (fun p ↦ ∃ d ∈ D, G.Adj d p)
                have hu_ND : u ∈ ND := by
                  simp only [ND, Finset.mem_filter]
                  exact ⟨huNx, d0, hd0D, hadj_ud0.symm⟩
                have hND_card : 2 ≤ ND.card := by
                  by_contra hlt2
                  have hND_sub : ND ⊆ {u} := by
                    intro p hp
                    rw [Finset.mem_singleton]
                    have hc_le : ND.card ≤ 1 := by omega
                    exact Finset.card_le_one.mp hc_le p hp u hu_ND
                  have hd0_ne_u : d0 ≠ u := fun h ↦ Finset.disjoint_left.mp hdisj_D_Nx hd0D (h ▸ huNx)
                  obtain ⟨p, hp⟩ := (reachable_induce_iff (U := {t : W | t ≠ u})
                    hd0_ne_u hux.symm).mp ((h2G.2 u) ⟨d0, hd0_ne_u⟩ ⟨x, hux.symm⟩)
                  obtain ⟨q', hq'D, w_out, hw_outD, hadj_qw, hw_supp, _⟩ :=
                    first_exit D hd0D hx_not_D p
                  have hw_ND : w_out ∈ ND := by
                    simp only [ND, Finset.mem_filter]
                    exact ⟨hbdy_D q' hq'D w_out hw_outD hadj_qw, q', hq'D, hadj_qw⟩
                  exact hp w_out hw_supp (Finset.mem_singleton.mp (hND_sub hw_ND))
                obtain ⟨v1, hv1_ND, hv1_ne_u⟩ := Finset.exists_mem_ne hND_card u
                set X0 : Finset W := {u}
                set X1 : Finset W := ND.erase u
                have hdisj_DX0 : Disjoint D X0 := by
                  rw [Finset.disjoint_singleton_right]
                  exact fun hm ↦ Finset.disjoint_left.mp hdisj_D_Nx hm huNx
                have hdisj_DX1 : Disjoint D X1 := by
                  rw [Finset.disjoint_left]
                  intro t htD htX1
                  have htNx : t ∈ Nx := (Finset.mem_filter.mp (Finset.mem_erase.mp htX1).2).1
                  exact Finset.disjoint_left.mp hdisj_D_Nx htD htNx
                have hdisj_01 : Disjoint X0 X1 := by
                  rw [Finset.disjoint_singleton_left]
                  exact Finset.notMem_erase u ND
                have hbdy_D01 : ∀ q ∈ D, ∀ w ∉ D, G.Adj q w → w ∈ X0 ∪ X1 := by
                  intro q hqD w hwD hadj_qw
                  have hwND : w ∈ ND :=
                    Finset.mem_filter.mpr ⟨hbdy_D q hqD w hwD hadj_qw, q, hqD, hadj_qw⟩
                  by_cases hwu : w = u
                  · subst hwu; simp [X0]
                  · exact Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨hwu, hwND⟩)
                have hex0 : ∃ q0 ∈ D, ∃ u0 ∈ X0, G.Adj q0 u0 :=
                  ⟨d0, hd0D, u, by simp [X0], hadj_ud0.symm⟩
                have hex1 : ∃ q1 ∈ D, ∃ u1 ∈ X1, G.Adj q1 u1 := by
                  have hv1_X1 : v1 ∈ X1 := Finset.mem_erase.mpr ⟨hv1_ne_u, hv1_ND⟩
                  rcases (Finset.mem_filter.mp hv1_ND).2 with ⟨q1, hq1D, hadj_q1⟩
                  exact ⟨q1, hq1D, v1, hv1_X1, hadj_q1⟩
                set G2 := contractTwo G D X0 X1
                have h2G2 : IsTwoConn (addEdge G2 (.inr 0) (.inr 1)) :=
                  isTwoConn_addEdge_contractTwo h2G hd0U' hdisj_DX0 hbdy_D01 hex0 hex1
                have hcardG2 : 4 ≤ Fintype.card ({v : W // v ∈ D} ⊕ Fin 2) := by
                  simp [Fintype.card_sum, Fintype.card_coe]
                  omega
                have hltG2 : Fintype.card ({v : W // v ∈ D} ⊕ Fin 2) < Fintype.card W := by
                  simp only [Fintype.card_sum, Fintype.card_coe, Fintype.card_fin]
                  have hle_u : (D ∪ insert x (insert y Nx)).card ≤ Fintype.card W :=
                    Finset.card_le_univ _
                  rw [Finset.card_union_of_disjoint hdisj_D_ins,
                    Finset.card_insert_of_notMem (by simp [hxy, hx_not_Nx]),
                    Finset.card_insert_of_notMem hy_not_Nx] at hle_u
                  omega
                set zG2 : {v : W // v ∈ D} ⊕ Fin 2 :=
                  if hzD : z ∈ D then .inl ⟨z, hzD⟩ else .inr 0
                have hdegG2 : ∀ s : {v : W // v ∈ D} ⊕ Fin 2,
                    s ≠ .inr 0 → s ≠ .inr 1 → s ≠ zG2 → 3 ≤ G2.degree s := by
                  intro s hs0 hs1 hsz
                  cases s with
                  | inr j =>
                    fin_cases j
                    · exact (hs0 rfl).elim
                    · exact (hs1 rfl).elim
                  | inl a =>
                    have hax : a.1 ≠ x := fun h ↦ hx_not_D (h ▸ a.2)
                    have hay : a.1 ≠ y := fun h ↦ hy_not_D (h ▸ a.2)
                    have haz : a.1 ≠ z := by
                      intro hza
                      apply hsz
                      dsimp only [zG2]
                      rw [dif_pos (hza ▸ a.2)]
                      exact congrArg Sum.inl (Subtype.ext hza)
                    have hX0_sub : G.neighborFinset a.1 ∩ X0 ⊆ G.neighborFinset a.1 ∩ Nx :=
                      Finset.inter_subset_inter_left (by simp [X0, huNx])
                    have hX1_sub : G.neighborFinset a.1 ∩ X1 ⊆ G.neighborFinset a.1 ∩ Nx := by
                      apply Finset.inter_subset_inter_left
                      intro t ht
                      exact (Finset.mem_filter.mp (Finset.mem_erase.mp ht).2).1
                    exact (hdeg a.1 hax hay haz).trans (degree_le_contractTwo a (hbdy_D01 a.1 a.2)
                      ((Finset.card_le_card hX0_sub).trans (hle1_Nx a.1 hax hay))
                      ((Finset.card_le_card hX1_sub).trans (hle1_Nx a.1 hax hay)))
                have h01_ne : (Sum.inr 0 : {v : W // v ∈ D} ⊕ Fin 2) ≠ .inr 1 := by intro h; simp at h
                obtain ⟨q1, q2, hq1_path, hq2_path, hq_mod⟩ :=
                  ih (Fintype.card W ^ 3 - 1) hM_pos G2 (.inr 0) (.inr 1) zG2
                    (card_cube_add_edges_le_pred G2 hltG2)
                    hcardG2 h01_ne h2G2 hdegG2
                obtain ⟨u0_1, hu0_1, p_1, hp1_X1, r1, hr1_path, hr1_len, hr1_supp⟩ :=
                  lift_walk_contractTwo hdisj_DX0 hdisj_DX1 hdisj_01 q1 hq1_path
                obtain ⟨u0_2, hu0_2, p_2, hp2_X1, r2, hr2_path, hr2_len, hr2_supp⟩ :=
                  lift_walk_contractTwo hdisj_DX0 hdisj_DX1 hdisj_01 q2 hq2_path
                rw [Finset.mem_singleton] at hu0_1 hu0_2
                subst u0_1; subst u0_2
                have hp1_Nx : p_1 ∈ Nx :=
                  (Finset.mem_filter.mp (Finset.mem_erase.mp hp1_X1).2).1
                have hp2_Nx : p_2 ∈ Nx :=
                  (Finset.mem_filter.mp (Finset.mem_erase.mp hp2_X1).2).1
                have hadj_xu : G.Adj x u := (G.mem_neighborFinset _ _).mp huNx
                have hadj_p1y : G.Adj p_1 y :=
                  ((G.mem_neighborFinset _ _).mp (hy_eq_Nx.symm ▸ hp1_Nx)).symm
                have hadj_p2y : G.Adj p_2 y :=
                  ((G.mem_neighborFinset _ _).mp (hy_eq_Nx.symm ▸ hp2_Nx)).symm
                have build_xy : ∀ (pi : W) (hpi_X1 : pi ∈ X1) (hadj_piy : G.Adj pi y)
                    (ri : G.Walk u pi), ri.IsPath →
                    (∀ t ∈ ri.support, t ∈ D ∨ t = u ∨ t = pi) →
                    ∃ wi : G.Walk x y, wi.IsPath ∧ wi.length = ri.length + 2 := by
                  intro pi hpi_X1 hadj_piy ri hri_path hri_supp
                  have hy_not_ri : y ∉ ri.support := by
                    intro hm
                    rcases hri_supp y hm with hyD | hyu | h_eq
                    · exact hy_not_D hyD
                    · exact huy hyu.symm
                    · exact (G.ne_of_adj hadj_piy) h_eq.symm
                  have hri_y_path : (ri.append (.cons hadj_piy .nil)).IsPath := by
                    apply append_isPath hri_path
                      (Walk.IsPath.cons Walk.IsPath.nil (by simp [G.ne_of_adj hadj_piy]))
                    intro t htr ht_end
                    simp only [Walk.support_cons, Walk.support_nil, List.mem_cons,
                      List.not_mem_nil, or_false] at ht_end
                    rcases ht_end with rfl | rfl
                    · rfl
                    · exact (hy_not_ri htr).elim
                  have hx_not_riy : x ∉ (ri.append (.cons hadj_piy .nil)).support := by
                    intro hm
                    rw [Walk.support_append] at hm
                    simp only [Walk.support_cons, Walk.support_nil, List.tail_cons,
                      List.mem_append, List.mem_singleton] at hm
                    rcases hm with hmr | h_eq
                    · rcases hri_supp x hmr with hxD | hxu | hxpi
                      · exact hx_not_D hxD
                      · exact hux hxu.symm
                      · have hpiNx := (Finset.mem_filter.mp (Finset.mem_erase.mp hpi_X1).2).1
                        exact hx_not_Nx (hxpi ▸ hpiNx)
                    · exact hxy h_eq
                  exact ⟨.cons hadj_xu (ri.append (.cons hadj_piy .nil)),
                    Walk.IsPath.cons hri_y_path hx_not_riy, by simp [Walk.length_append]⟩
                obtain ⟨w1, hw1_path, hw1_len⟩ :=
                  build_xy p_1 hp1_X1 hadj_p1y r1 hr1_path hr1_supp
                obtain ⟨w2, hw2_path, hw2_len⟩ :=
                  build_xy p_2 hp2_X1 hadj_p2y r2 hr2_path hr2_supp
                exact ⟨w1, w2, hw1_path, hw2_path, by rw [hw1_len, hw2_len, hr1_len, hr2_len]; omega⟩
    · -- Step 1b: `¬ IsTwoConn G` (cut-vertex reduction).
      -- First show `G.Connected`.
      have hG_conn : G.Connected := by
        set Cx0 := compIn G Finset.univ x
        have hx_Cx0 : x ∈ Cx0 := self_mem_compIn (Finset.mem_univ x)
        by_cases hfull : Cx0 = Finset.univ
        · have hreach : ∀ v : W, G.Reachable x v := by
            intro v
            have hv : v ∈ Cx0 := hfull ▸ Finset.mem_univ v
            rcases mem_compIn_iff.mp hv with ⟨_, p, _⟩
            exact ⟨p⟩
          exact @Connected.mk _ G (fun a b ↦ (hreach a).symm.trans (hreach b)) ⟨x⟩
        · exfalso
          have hy_not_Cx0 : y ∉ Cx0 := by
            intro hy_Cx0
            rcases mem_compIn_iff.mp hy_Cx0 with ⟨_, p_xy, _⟩
            apply hfull
            ext v
            simp only [Finset.mem_univ, iff_true]
            rw [mem_compIn_iff]
            refine ⟨Finset.mem_univ v, ?_⟩
            obtain ⟨q⟩ := h2conn.1 x v
            have liftG : ∀ {a b : W} (wlk : (addEdge G x y).Walk a b), G.Reachable a b := by
              intro a b wlk
              induction wlk with
              | nil => exact Reachable.refl _
              | @cons u1 u2 u3 hadj tl ihtl =>
                have hr_step : G.Reachable u1 u2 := by
                  rcases hadj with hadjG | ⟨_, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
                  · exact hadjG.reachable
                  · exact ⟨p_xy⟩
                  · exact ⟨p_xy.reverse⟩
                exact hr_step.trans ihtl
            obtain ⟨r⟩ := liftG q
            exact ⟨r, fun _ _ ↦ Finset.mem_univ _⟩
          have hcard_sum : Cx0.card + (Finset.univ \ Cx0).card = Fintype.card W := by
            have := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ Cx0)
            rw [Finset.card_univ] at this
            omega
          by_cases hCx0_2 : 2 ≤ Cx0.card
          · obtain ⟨w, hwCx0, hwx⟩ := Finset.exists_mem_ne hCx0_2 x
            obtain ⟨p, hp⟩ := (reachable_induce_iff (U := {t : W | t ≠ x})
              hwx hxy.symm).mp ((h2conn.2 x) ⟨w, hwx⟩ ⟨y, hxy.symm⟩)
            obtain ⟨q', hq'Cx0, t_out, ht_outCx0, hadj_qt, ht_supp, h_r⟩ :=
              first_exit Cx0 hwCx0 hy_not_Cx0 p
            rcases h_r with ⟨r_walk, hr_walk⟩
            have hq'_ne_x : q' ≠ x := hp q' (hr_walk q' (Walk.end_mem_support r_walk)).2
            have ht_ne_x : t_out ≠ x := hp t_out ht_supp
            have hadjG : G.Adj q' t_out := by
              rcases hadj_qt with hadjG | ⟨_, ⟨rfl, _⟩ | ⟨_, rfl⟩⟩
              · exact hadjG
              · exact (hq'_ne_x rfl).elim
              · exact (ht_ne_x rfl).elim
            exact compIn_no_edge_out hq'Cx0 (Finset.mem_univ t_out) ht_outCx0 hadjG
          · have hCo_2 : 2 ≤ (Finset.univ \ Cx0).card := by omega
            obtain ⟨w, hwCo, hwy⟩ := Finset.exists_mem_ne hCo_2 y
            have hw_not_Cx0 : w ∉ Cx0 := (Finset.mem_sdiff.mp hwCo).2
            obtain ⟨p, hp⟩ := (reachable_induce_iff (U := {t : W | t ≠ y}) hxy hwy).mp
              ((h2conn.2 y) ⟨x, hxy⟩ ⟨w, hwy⟩)
            obtain ⟨q', hq'Cx0, t_out, ht_outCx0, hadj_qt, ht_supp, r_walk, hr_walk⟩ :=
              first_exit Cx0 hx_Cx0 hw_not_Cx0 p
            have hq'_ne_y : q' ≠ y := hp q' (hr_walk q' (Walk.end_mem_support r_walk)).2
            have ht_ne_y : t_out ≠ y := hp t_out ht_supp
            have hadjG : G.Adj q' t_out := by
              rcases hadj_qt with hadjG | ⟨_, ⟨_, rfl⟩ | ⟨rfl, _⟩⟩
              · exact hadjG
              · exact (ht_ne_y rfl).elim
              · exact (hq'_ne_y rfl).elim
            exact compIn_no_edge_out hq'Cx0 (Finset.mem_univ t_out) ht_outCx0 hadjG
      -- Obtain cut-vertex `b : W` such that `G - b` is disconnected.
      have hex_b : ∃ b : W, ¬ (G.induce {v : W | v ≠ b}).Connected := by
        by_contra hall
        push Not at hall
        exact h2G ⟨hG_conn, hall⟩
      rcases hex_b with ⟨b, hb_cut⟩
      have hbx : b ≠ x := by
        rintro rfl
        apply hb_cut
        have heq : G.induce {v : W | v ≠ b} = (addEdge G b y).induce {v : W | v ≠ b} := by
          ext ⟨u1, hu1⟩ ⟨u2, hu2⟩
          simp only [induce_adj, addEdge]
          simp at hu1 hu2
          tauto
        rw [heq]
        exact h2conn.2 b
      have hby : b ≠ y := by
        rintro rfl
        apply hb_cut
        have heq : G.induce {v : W | v ≠ b} = (addEdge G x b).induce {v : W | v ≠ b} := by
          ext ⟨u1, hu1⟩ ⟨u2, hu2⟩
          simp only [induce_adj, addEdge]
          simp at hu1 hu2
          tauto
        rw [heq]
        exact h2conn.2 b
      set Ub := Finset.univ.erase b
      have hxUb : x ∈ Ub := Finset.mem_erase.mpr ⟨hbx.symm, Finset.mem_univ x⟩
      have hyUb : y ∈ Ub := Finset.mem_erase.mpr ⟨hby.symm, Finset.mem_univ y⟩
      set Cx := compIn G Ub x
      set Cy := compIn G Ub y
      have hxCx : x ∈ Cx := self_mem_compIn hxUb
      have hyCy : y ∈ Cy := self_mem_compIn hyUb
      have hy_not_Cx : y ∉ Cx := by
        intro hyCx
        rcases mem_compIn_iff.mp hyCx with ⟨_, p_xy, hp_xy⟩
        apply hb_cut
        apply connected_induce_of_base x hbx.symm
        intro a ha
        obtain ⟨q, hq⟩ := (reachable_induce_iff (U := {t : W | t ≠ b}) hbx.symm ha).mp
          ((h2conn.2 b) ⟨x, hbx.symm⟩ ⟨a, ha⟩)
        have liftUb : ∀ {u1 u2 : W} (wlk : (addEdge G x y).Walk u1 u2),
            (∀ t ∈ wlk.support, t ≠ b) →
            ∃ r : G.Walk u1 u2, ∀ t ∈ r.support, t ≠ b := by
          intro u1 u2 wlk
          induction wlk with
          | nil =>
            intro hno
            exact ⟨.nil, hno⟩
          | @cons s1 s2 s3 hadj_step tl ihtl =>
            intro hno
            obtain ⟨r_tl, hr_tl⟩ := ihtl (fun t ht ↦ hno t (by simp [ht]))
            have hs1 : s1 ≠ b := hno s1 (by simp)
            rcases hadj_step with hadjG | ⟨_, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
            · refine ⟨.cons hadjG r_tl, fun t ht ↦ ?_⟩
              simp only [Walk.support_cons, List.mem_cons] at ht
              rcases ht with rfl | ht
              · exact hs1
              · exact hr_tl t ht
            · refine ⟨p_xy.append r_tl, fun t ht ↦ ?_⟩
              rw [Walk.support_append] at ht
              rcases List.mem_append.mp ht with ht1 | ht2
              · exact (Finset.mem_erase.mp (hp_xy t ht1)).1
              · exact hr_tl t (List.mem_of_mem_tail ht2)
            · refine ⟨p_xy.reverse.append r_tl, fun t ht ↦ ?_⟩
              rw [Walk.support_append] at ht
              rcases List.mem_append.mp ht with ht1 | ht2
              · rw [Walk.support_reverse, List.mem_reverse] at ht1
                exact (Finset.mem_erase.mp (hp_xy t ht1)).1
              · exact hr_tl t (List.mem_of_mem_tail ht2)
        obtain ⟨r, hr⟩ := liftUb q hq
        exact (reachable_induce_iff hbx.symm ha).mpr ⟨r, hr⟩
      have hdisj_CxCy : Disjoint Cx Cy := by
        rw [Finset.disjoint_left]
        intro w hwCx hwCy
        rcases mem_compIn_iff.mp hwCx with ⟨_, p1, hp1⟩
        rcases mem_compIn_iff.mp hwCy with ⟨_, p2, hp2⟩
        apply hy_not_Cx
        rw [mem_compIn_iff]
        refine ⟨hyUb, p1.append p2.reverse, fun t ht ↦ ?_⟩
        rw [Walk.support_append] at ht
        rcases List.mem_append.mp ht with ht1 | ht2
        · exact hp1 t ht1
        · have ht2' := List.mem_of_mem_tail ht2
          rw [Walk.support_reverse, List.mem_reverse] at ht2'
          exact hp2 t ht2'
      have hUb_eq : Ub = Cx ∪ Cy := by
        apply Finset.Subset.antisymm
        · intro v hvUb
          have hvb : v ≠ b := (Finset.mem_erase.mp hvUb).1
          obtain ⟨q, hq⟩ := (reachable_induce_iff (U := {t : W | t ≠ b}) hvb hbx.symm).mp
            ((h2conn.2 b) ⟨v, hvb⟩ ⟨x, hbx.symm⟩)
          have splitXY : ∀ {u1 u2 : W} (wlk : (addEdge G x y).Walk u1 u2),
              u2 = x → (∀ t ∈ wlk.support, t ≠ b) →
              (∃ r : G.Walk x u1, ∀ t ∈ r.support, t ∈ Ub) ∨
              (∃ r : G.Walk y u1, ∀ t ∈ r.support, t ∈ Ub) := by
            intro u1 u2 wlk
            induction wlk with
            | @nil u0 =>
              intro hu0 _
              subst u0
              exact Or.inl ⟨.nil, by simp [hxUb]⟩
            | @cons s1 s2 s3 hadj_step tl ihtl =>
              intro hs3 hno
              have hs1Ub : s1 ∈ Ub := Finset.mem_erase.mpr ⟨hno s1 (by simp), Finset.mem_univ s1⟩
              have hno_tl : ∀ t ∈ tl.support, t ≠ b := fun t ht ↦ hno t (by simp [ht])
              clear hno
              rcases hadj_step with hadjG | ⟨_, ⟨hs1x, _⟩ | ⟨hs1y, _⟩⟩
              · rcases ihtl hs3 hno_tl with ⟨rx, hrx⟩ | ⟨ry, hry⟩
                · refine Or.inl ⟨rx.append (.cons hadjG.symm .nil), fun t ht ↦ ?_⟩
                  rw [Walk.support_append] at ht
                  simp only [Walk.support_cons, Walk.support_nil, List.tail_cons,
                    List.mem_append, List.mem_singleton] at ht
                  rcases ht with ht1 | rfl
                  · exact hrx t ht1
                  · exact hs1Ub
                · refine Or.inr ⟨ry.append (.cons hadjG.symm .nil), fun t ht ↦ ?_⟩
                  rw [Walk.support_append] at ht
                  simp only [Walk.support_cons, Walk.support_nil, List.tail_cons,
                    List.mem_append, List.mem_singleton] at ht
                  rcases ht with ht1 | rfl
                  · exact hry t ht1
                  · exact hs1Ub
              · subst s1
                exact Or.inl ⟨.nil, by simp [hxUb]⟩
              · subst s1
                exact Or.inr ⟨.nil, by simp [hyUb]⟩
          rcases splitXY q rfl hq with ⟨rx, hrx⟩ | ⟨ry, hry⟩
          · exact Finset.mem_union_left _ (mem_compIn_iff.mpr ⟨hvUb, rx, hrx⟩)
          · exact Finset.mem_union_right _ (mem_compIn_iff.mpr ⟨hvUb, ry, hry⟩)
        · exact Finset.union_subset compIn_subset compIn_subset
      have hb_not_Cx : b ∉ Cx := fun hm ↦ (Finset.mem_erase.mp (compIn_subset hm)).1 rfl
      have hb_not_Cy : b ∉ Cy := fun hm ↦ (Finset.mem_erase.mp (compIn_subset hm)).1 rfl
      -- Helper: simple `(s0, b)`-path inside `Cs ∪ {b}` for `Cs = compIn G Ub s0`.
      have path_to_b : ∀ (s0 : W) (hs0 : s0 ∈ Ub),
          (∃ q ∈ compIn G Ub s0, G.Adj q b) ∧
          ∃ p : G.Walk s0 b, p.IsPath ∧ ∀ t ∈ p.support, t ∈ compIn G Ub s0 ∨ t = b := by
        intro s0 hs0
        set Cs := compIn G Ub s0
        have hs0_Cs : s0 ∈ Cs := self_mem_compIn hs0
        have hb_not_Cs : b ∉ Cs := fun hm ↦ (Finset.mem_erase.mp (compIn_subset hm)).1 rfl
        obtain ⟨p0⟩ := hG_conn s0 b
        obtain ⟨q', hq'Cs, w_out, hw_outCs, hadj_qw, _, r_sq, hr_sq⟩ :=
          first_exit Cs hs0_Cs hb_not_Cs p0
        have hw_eq_b : w_out = b := by
          by_contra hneb
          have hwUb : w_out ∈ Ub := Finset.mem_erase.mpr ⟨hneb, Finset.mem_univ w_out⟩
          exact compIn_no_edge_out hq'Cs hwUb hw_outCs hadj_qw
        subst w_out
        set r_full : G.Walk s0 b := r_sq.append (.cons hadj_qw .nil)
        set p_clean := r_full.toPath
        refine ⟨⟨q', hq'Cs, hadj_qw⟩, p_clean.1, p_clean.2, fun t ht ↦ ?_⟩
        have ht_full := Walk.support_toPath_subset_support r_full ht
        rw [Walk.support_append] at ht_full
        simp only [Walk.support_cons, Walk.support_nil, List.tail_cons, List.mem_append,
          List.mem_singleton] at ht_full
        rcases ht_full with ht1 | rfl
        · exact Or.inl (hr_sq t ht1).1
        · exact Or.inr rfl
      obtain ⟨⟨qx, hqxCx, hadj_qxb⟩, px_b, hpx_path, hpx_supp⟩ := path_to_b x hxUb
      obtain ⟨⟨qy, hqyCy, hadj_qyb⟩, py_b, hpy_path, hpy_supp⟩ := path_to_b y hyUb
      -- Helper: if `3 ≤ Cs.card`, apply IH to `contractOne G Cs {b}`.
      have solve_large_side : ∀ (s0 o0 : W) (hs0 : s0 ∈ Ub) (ho0 : o0 ∈ Ub),
          ((s0 = x ∧ o0 = y) ∨ (s0 = y ∧ o0 = x)) →
          3 ≤ (compIn G Ub s0).card →
          (∃ p_ob : G.Walk o0 b, p_ob.IsPath ∧ ∀ t ∈ p_ob.support, t ∈ compIn G Ub o0 ∨ t = b) →
          (∃ q_s ∈ compIn G Ub s0, G.Adj q_s b) →
          ∃ (p1 p2 : G.Walk s0 o0), p1.IsPath ∧ p2.IsPath ∧ p1.length % 3 ≠ p2.length % 3 := by
        intro s0 o0 hs0 ho0 hpair hCs3 ⟨p_ob, hpob_path, hpob_supp⟩ ⟨q_s, hqs_Cs, hadj_qsb⟩
        set Cs := compIn G Ub s0
        set Co := compIn G Ub o0
        have hs0_Cs : s0 ∈ Cs := self_mem_compIn hs0
        have ho0_Co : o0 ∈ Co := self_mem_compIn ho0
        have hdisj_so : Disjoint Cs Co := by
          rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact hdisj_CxCy
          · exact hdisj_CxCy.symm
        have ho0_not_Cs : o0 ∉ Cs := Finset.disjoint_right.mp hdisj_so ho0_Co
        have hb_not_Cs : b ∉ Cs := fun hm ↦ (Finset.mem_erase.mp (compIn_subset hm)).1 rfl
        have hdisj_Cs_b : Disjoint Cs ({b} : Finset W) :=
          Finset.disjoint_singleton_right.mpr hb_not_Cs
        -- Notice `compIn (addEdge G x y) (Finset.univ \ {b, o0}) s0 = Cs`!
        set U_add := Finset.univ \ ({b, o0} : Finset W)
        have hs0_ne_b : s0 ≠ b := (Finset.mem_erase.mp hs0).1
        have hs0_ne_o0 : s0 ≠ o0 := by
          rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact hxy
          · exact hxy.symm
        have hs0_Uadd : s0 ∈ U_add := by
          simp [U_add, hs0_ne_b, hs0_ne_o0]
        have hCs_eq_add : compIn (addEdge G x y) U_add s0 = Cs := by
          apply Finset.Subset.antisymm
          · intro v hv
            rcases mem_compIn_iff.mp hv with ⟨_, p, hp⟩
            have hpG : ∃ r : G.Walk s0 v, ∀ t ∈ r.support, t ∈ Ub := by
              -- Any walk in `U_add` avoids `o0`, so it never uses the new edge `{x, y}`!
              have walk_no_xy : ∀ {u1 u2 : W} (wlk : (addEdge G x y).Walk u1 u2),
                  (∀ t ∈ wlk.support, t ∈ U_add) →
                  ∃ r : G.Walk u1 u2, ∀ t ∈ r.support, t ∈ Ub := by
                intro u1 u2 wlk
                induction wlk with
                | @nil u0 =>
                  intro hmem
                  have hu0 := hmem u0 (by simp)
                  simp only [U_add, Finset.mem_sdiff, Finset.mem_univ, Finset.mem_insert,
                    Finset.mem_singleton, true_and, not_or] at hu0
                  exact ⟨.nil, by simp [Ub, hu0.1]⟩
                | @cons a1 a2 a3 hadj_step tl ihtl =>
                  intro hmem
                  have ha1 := hmem a1 (by simp)
                  have ha2 := hmem a2 (by simp)
                  simp only [U_add, Finset.mem_sdiff, Finset.mem_univ, Finset.mem_insert,
                    Finset.mem_singleton, true_and, not_or] at ha1 ha2
                  have hadjG : G.Adj a1 a2 := by
                    rcases hadj_step with hadjG | ⟨_, ⟨ha1x, ha2y⟩ | ⟨ha1y, ha2x⟩⟩
                    · exact hadjG
                    · rcases hpair with ⟨_, hoy⟩ | ⟨hsy, hox⟩
                      · exact (ha2.2 (ha2y.trans hoy.symm)).elim
                      · exact (ha1.2 (ha1x.trans hox.symm)).elim
                    · rcases hpair with ⟨_, hoy⟩ | ⟨hsy, hox⟩
                      · exact (ha1.2 (ha1y.trans hoy.symm)).elim
                      · exact (ha2.2 (ha2x.trans hox.symm)).elim
                  obtain ⟨r_tl, hr_tl⟩ := ihtl (fun t ht ↦ hmem t (by simp [ht]))
                  refine ⟨.cons hadjG r_tl, fun t ht ↦ ?_⟩
                  simp only [Walk.support_cons, List.mem_cons] at ht
                  rcases ht with rfl | ht
                  · exact Finset.mem_erase.mpr ⟨ha1.1, Finset.mem_univ _⟩
                  · exact hr_tl t ht
              exact walk_no_xy p hp
            rcases hpG with ⟨r, hr⟩
            exact mem_compIn_iff.mpr ⟨hr v (Walk.end_mem_support r), r, hr⟩
          · intro v hv
            rcases mem_compIn_iff.mp hv with ⟨_, p, hp⟩
            have hp_Cs := walk_in_U_stays_in_compIn hs0_Cs p hp
            rw [mem_compIn_iff]
            have liftAdd : ∀ {u1 u2 : W} (wlk : G.Walk u1 u2),
                (∀ t ∈ wlk.support, t ∈ Cs) →
                ∃ r : (addEdge G x y).Walk u1 u2, ∀ t ∈ r.support, t ∈ U_add := by
              intro u1 u2 wlk
              induction wlk with
              | @nil u0 =>
                intro hmem
                have hu0Cs := hmem u0 (by simp)
                have hu0_b : u0 ≠ b := fun h ↦ hb_not_Cs (h ▸ hu0Cs)
                have hu0_o : u0 ≠ o0 := fun h ↦ ho0_not_Cs (h ▸ hu0Cs)
                exact ⟨.nil, by simp [U_add, hu0_b, hu0_o]⟩
              | @cons a1 a2 _ hadjG tl ihtl =>
                intro hmem
                have ha1Cs := hmem a1 (by simp)
                have ha1_b : a1 ≠ b := fun h ↦ hb_not_Cs (h ▸ ha1Cs)
                have ha1_o : a1 ≠ o0 := fun h ↦ ho0_not_Cs (h ▸ ha1Cs)
                let hadj_a : (addEdge G x y).Adj a1 a2 := Or.inl hadjG
                obtain ⟨r_tl, hr_tl⟩ := ihtl (fun t ht ↦ hmem t (by simp [ht]))
                refine ⟨.cons hadj_a r_tl, fun t ht ↦ ?_⟩
                simp only [Walk.support_cons, List.mem_cons] at ht
                rcases ht with rfl | ht
                · simp [U_add, ha1_b, ha1_o]
                · exact hr_tl t ht
            obtain ⟨r_add, hr_add⟩ := liftAdd p hp_Cs
            exact ⟨hr_add v (Walk.end_mem_support r_add), r_add, hr_add⟩
        set H1 := contractOne G Cs {b}
        have hbdy_Cs_G : ∀ a ∈ Cs, ∀ w ∉ Cs, G.Adj a w → w ∈ ({b} : Finset W) := by
          intro a haCs w hwCs hadj_aw
          rw [Finset.mem_singleton]
          by_contra hwb
          exact compIn_no_edge_out haCs (Finset.mem_erase.mpr ⟨hwb, Finset.mem_univ w⟩) hwCs hadj_aw
        have h_adj_none : ∀ (a : {v : W // v ∈ Cs}),
            (addEdge H1 none (some ⟨s0, hs0_Cs⟩)).Adj none (some a) ↔
              (contractOne (addEdge G x y) Cs ({b, o0} : Finset W)).Adj none (some a) := by
          intro a
          dsimp only [addEdge, H1, contractOne]
          have hbo_ne_xy : ¬((b = x ∧ a.1 = y) ∨ (b = y ∧ a.1 = x)) :=
            fun h ↦ h.elim (fun h1 ↦ hbx h1.1) (fun h2 ↦ hby h2.1)
          constructor
          · rintro (⟨u', hu'b, hadj_ua⟩ | ⟨_, ⟨_, h_eq⟩ | ⟨h_bad, _⟩⟩)
            · rw [Finset.mem_singleton] at hu'b
              subst u'
              exact ⟨b, by simp, Or.inl hadj_ua⟩
            · have ha_s0 : a.1 = s0 := congrArg Subtype.val (Option.some.inj h_eq)
              refine ⟨o0, by simp, Or.inr ⟨hxy, ?_⟩⟩
              rcases hpair with ⟨hsx, hoy⟩ | ⟨hsy, hox⟩
              · exact Or.inr ⟨hoy, ha_s0.trans hsx⟩
              · exact Or.inl ⟨hox, ha_s0.trans hsy⟩
            · cases h_bad
          · rintro ⟨u', hu'_bo, hadj_u⟩
            simp only [Finset.mem_insert, Finset.mem_singleton] at hu'_bo
            rcases hu'_bo with hu'b | hu'o
            · subst u'
              rcases hadj_u with hadj_ba | ⟨_, h_imp⟩
              · exact Or.inl ⟨b, Finset.mem_singleton_self b, hadj_ba⟩
              · exact (hbo_ne_xy h_imp).elim
            · subst u'
              rcases hadj_u with hadj_oa | ⟨_, h_xy⟩
              · exact (compIn_no_edge_out a.2 ho0 ho0_not_Cs hadj_oa.symm).elim
              · refine Or.inr ⟨(Option.some_ne_none _).symm, Or.inl ⟨rfl, congrArg some (Subtype.ext ?_)⟩⟩
                rcases hpair with ⟨hsx, hoy⟩ | ⟨hsy, hox⟩
                · rcases h_xy with ⟨h1, _⟩ | ⟨_, h2⟩
                  · exact (hxy (h1.symm.trans hoy)).elim
                  · exact h2.trans hsx.symm
                · rcases h_xy with ⟨_, h2⟩ | ⟨h1, _⟩
                  · exact h2.trans hsy.symm
                  · exact (hxy (hox.symm.trans h1)).elim
        have hH1_add_eq : addEdge H1 none (some ⟨s0, hs0_Cs⟩) =
            contractOne (addEdge G x y) Cs ({b, o0} : Finset W) := by
          ext u1 u2
          cases u1 <;> cases u2
          · simp [addEdge, H1, contractOne]
          · rename_i a2
            exact h_adj_none a2
          · rename_i a1
            rw [SimpleGraph.adj_comm, SimpleGraph.adj_comm (contractOne _ _ _)]
            exact h_adj_none a1
          · rename_i a1 a2
            dsimp only [addEdge, H1, contractOne]
            constructor
            · rintro (hadjG | ⟨_, ⟨h_bad, _⟩ | ⟨_, h_bad⟩⟩)
              · exact Or.inl hadjG
              · cases h_bad
              · cases h_bad
            · rintro (hadjG | ⟨_, ⟨ha1x, ha2y⟩ | ⟨ha1y, ha2x⟩⟩)
              · exact Or.inl hadjG
              · exfalso
                rcases hpair with ⟨_, hoy⟩ | ⟨_, hox⟩
                · exact ho0_not_Cs (hoy.symm ▸ ha2y ▸ a2.2)
                · exact ho0_not_Cs (hox.symm ▸ ha1x ▸ a1.2)
              · exfalso
                rcases hpair with ⟨_, hoy⟩ | ⟨_, hox⟩
                · exact ho0_not_Cs (hoy.symm ▸ ha1y ▸ a1.2)
                · exact ho0_not_Cs (hox.symm ▸ ha2x ▸ a2.2)
        have h2H1_add : IsTwoConn (addEdge H1 none (some ⟨s0, hs0_Cs⟩)) := by
          rw [hH1_add_eq, ← hCs_eq_add]
          apply isTwoConn_contractOne h2conn hs0_Uadd (by rw [hCs_eq_add]; omega)
            (by rw [hCs_eq_add]; exact ho0_not_Cs)
          intro a ha w hw hadj_add
          rw [hCs_eq_add] at ha hw
          by_cases hw_bo : w ∈ ({b, o0} : Finset W)
          · exact hw_bo
          · have hw_Uadd : w ∈ U_add := Finset.mem_sdiff.mpr ⟨Finset.mem_univ w, hw_bo⟩
            rw [← hCs_eq_add] at ha hw
            exact (compIn_no_edge_out ha hw_Uadd hw hadj_add).elim
        have hcardH1 : 4 ≤ Fintype.card (Option {v : W // v ∈ Cs}) := by
          simp [Fintype.card_option, Fintype.card_coe]
          omega
        have hltH1 : Fintype.card (Option {v : W // v ∈ Cs}) < Fintype.card W := by
          simp only [Fintype.card_option, Fintype.card_coe]
          have hsub_u : (Cs ∪ insert b ({o0} : Finset W)).card ≤ Fintype.card W :=
            Finset.card_le_univ _
          have hbo_ne : b ≠ o0 := by
            rcases hpair with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> assumption
          have hdisj_Cs_bo : Disjoint Cs (insert b ({o0} : Finset W)) := by
            simp [Finset.disjoint_insert_right, hb_not_Cs, ho0_not_Cs]
          rw [Finset.card_union_of_disjoint hdisj_Cs_bo,
            Finset.card_insert_of_notMem (Finset.notMem_singleton.mpr hbo_ne),
            Finset.card_singleton] at hsub_u
          omega
        set zH1 : Option {v : W // v ∈ Cs} :=
          if hzCs : z ∈ Cs then some ⟨z, hzCs⟩ else none
        have hdegH1 : ∀ o : Option {v : W // v ∈ Cs},
            o ≠ none → o ≠ some ⟨s0, hs0_Cs⟩ → o ≠ zH1 → 3 ≤ H1.degree o := by
          intro o hon hos hoz
          cases o with
          | none => exact (hon rfl).elim
          | some a =>
            have ha_ne_s0 : a.1 ≠ s0 := fun heq ↦ hos (congrArg some (Subtype.ext heq))
            have ha_ne_o0 : a.1 ≠ o0 := fun h ↦ ho0_not_Cs (h ▸ a.2)
            have ha_ne_x : a.1 ≠ x := by
              rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> assumption
            have ha_ne_y : a.1 ≠ y := by
              rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> assumption
            have ha_ne_z : a.1 ≠ z := by
              intro hza
              apply hoz
              dsimp only [zH1]
              rw [dif_pos (hza ▸ a.2)]
              exact congrArg some (Subtype.ext hza)
            have hle1_b : (G.neighborFinset a.1 ∩ ({b} : Finset W)).card ≤ 1 :=
              (Finset.card_le_card Finset.inter_subset_right).trans (by simp)
            exact (hdeg a.1 ha_ne_x ha_ne_y ha_ne_z).trans
              (degree_le_contractOne a (hbdy_Cs_G a.1 a.2) hle1_b)
        obtain ⟨q1, q2, hq1_path, hq2_path, hq_mod⟩ :=
          ih (Fintype.card W ^ 3 - 1) hM_pos H1 none (some ⟨s0, hs0_Cs⟩) zH1
            (card_cube_add_edges_le_pred H1 hltH1)
            hcardH1 (Option.some_ne_none _).symm h2H1_add hdegH1
        obtain ⟨ub1, hub1, r1, hr1_path, hr1_len, hr1_tl⟩ :=
          lift_walk_contractOne hdisj_Cs_b q1 hq1_path
        obtain ⟨ub2, hub2, r2, hr2_path, hr2_len, hr2_tl⟩ :=
          lift_walk_contractOne hdisj_Cs_b q2 hq2_path
        rw [Finset.mem_singleton] at hub1 hub2
        subst ub1; subst ub2
        have hdisj_r_pob : ∀ (ri : G.Walk b s0), (∀ t ∈ ri.support.tail, t ∈ Cs) →
            ∀ t ∈ ri.reverse.support, t ∈ p_ob.reverse.support → t = b := by
          intro ri hri_tl t ht1 ht2
          rw [Walk.support_reverse, List.mem_reverse] at ht1 ht2
          rw [support_eq_cons_tail ri, List.mem_cons] at ht1
          rcases ht1 with rfl | ht1_tl
          · rfl
          · have htCs : t ∈ Cs := hri_tl t ht1_tl
            rcases hpob_supp t ht2 with htCo | rfl
            · exact (Finset.disjoint_left.mp hdisj_so htCs htCo).elim
            · rfl
        refine ⟨r1.reverse.append p_ob.reverse, r2.reverse.append p_ob.reverse,
          append_isPath hr1_path.reverse hpob_path.reverse (hdisj_r_pob r1 hr1_tl),
          append_isPath hr2_path.reverse hpob_path.reverse (hdisj_r_pob r2 hr2_tl), ?_⟩
        simp only [Walk.length_append, Walk.length_reverse, hr1_len, hr2_len]
        omega
      -- Now apply `solve_large_side` if `3 ≤ Cx.card` or `3 ≤ Cy.card`, else `Cx.card ≤ 2` and `Cy.card ≤ 2`.
      by_cases hCx3 : 3 ≤ Cx.card
      · exact solve_large_side x y hxUb hyUb (Or.inl ⟨rfl, rfl⟩) hCx3
          ⟨py_b, hpy_path, hpy_supp⟩ ⟨qx, hqxCx, hadj_qxb⟩
      · by_cases hCy3 : 3 ≤ Cy.card
        · obtain ⟨p1, p2, hp1, hp2, hmod⟩ :=
            solve_large_side y x hyUb hxUb (Or.inr ⟨rfl, rfl⟩) hCy3
              ⟨px_b, hpx_path, hpx_supp⟩ ⟨qy, hqyCy, hadj_qyb⟩
          exact ⟨p1.reverse, p2.reverse, hp1.reverse, hp2.reverse, by simpa using hmod⟩
        · -- Small case: `Cx.card ≤ 2` and `Cy.card ≤ 2`, with `Cx.card + Cy.card = Fintype.card W - 1 ≥ 3`.
          have hsum_card : Cx.card + Cy.card = Fintype.card W - 1 := by
            have hcUb : Ub.card = Fintype.card W - 1 := by
              simp [Ub, Finset.card_erase_of_mem]
            rw [← hcUb, hUb_eq, Finset.card_union_of_disjoint hdisj_CxCy]
          have solve_card2_side : ∀ (s0 o0 : W) (hs0 : s0 ∈ Ub) (ho0 : o0 ∈ Ub),
              ((s0 = x ∧ o0 = y) ∨ (s0 = y ∧ o0 = x)) →
              (compIn G Ub s0).card = 2 →
              (compIn G Ub o0).card ≤ 2 →
              (∃ p_ob : G.Walk o0 b, p_ob.IsPath ∧ ∀ t ∈ p_ob.support, t ∈ compIn G Ub o0 ∨ t = b) →
              ∃ (p1 p2 : G.Walk s0 o0), p1.IsPath ∧ p2.IsPath ∧ p1.length % 3 ≠ p2.length % 3 := by
            intro s0 o0 hs0 ho0 hpair hCs2 hCo2 ⟨p_ob, hpob_path, hpob_supp⟩
            set Cs := compIn G Ub s0
            set Co := compIn G Ub o0
            have hs0_Cs : s0 ∈ Cs := self_mem_compIn hs0
            have ho0_Co : o0 ∈ Co := self_mem_compIn ho0
            have hdisj_so : Disjoint Cs Co := by
              rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
              · exact hdisj_CxCy
              · exact hdisj_CxCy.symm
            have hb_not_Cs : b ∉ Cs := fun hm ↦ (Finset.mem_erase.mp (compIn_subset hm)).1 rfl
            have hb_not_Co : b ∉ Co := fun hm ↦ (Finset.mem_erase.mp (compIn_subset hm)).1 rfl
            obtain ⟨w, hwCs, hws0⟩ := Finset.exists_mem_ne (by omega : 1 < Cs.card) s0
            have hCs_eq : Cs = {s0, w} :=
              (Finset.eq_of_subset_of_card_le
                (by intro t ht; simp only [Finset.mem_insert, Finset.mem_singleton] at ht;
                    rcases ht with rfl | rfl <;> assumption)
                (by rw [hCs2, Finset.card_pair hws0.symm])).symm
            have hw_ne_b : w ≠ b := fun h ↦ hb_not_Cs (h ▸ hwCs)
            have hw_ne_o0 : w ≠ o0 := fun h ↦ Finset.disjoint_left.mp hdisj_so hwCs (h ▸ ho0_Co)
            have hw_ne_x : w ≠ x := by
              rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> assumption
            have hw_ne_y : w ≠ y := by
              rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> assumption
            have hw_nb_sub : G.neighborFinset w ⊆ ({s0, b} : Finset W) := by
              intro t ht
              have hadj_wt : G.Adj w t := (G.mem_neighborFinset _ _).mp ht
              by_cases htUb : t ∈ Ub
              · have htCs : t ∈ Cs := by
                  by_contra hnot
                  exact compIn_no_edge_out hwCs htUb hnot hadj_wt
                rw [hCs_eq, Finset.mem_insert, Finset.mem_singleton] at htCs
                rcases htCs with rfl | rfl
                · simp
                · exact (G.ne_of_adj hadj_wt rfl).elim
              · simp only [Ub, Finset.mem_erase, Finset.mem_univ, and_true, not_not] at htUb
                subst t; simp
            have hw_deg_ge2 : 2 ≤ G.degree w := by
              have hdeg_add : 2 ≤ (addEdge G x y).degree w := h2conn.two_le_degree (by omega) w
              have heq_deg : (addEdge G x y).degree w = G.degree w := by
                rw [← card_neighborFinset_eq_degree, ← card_neighborFinset_eq_degree]
                congr 1; ext t
                rw [SimpleGraph.mem_neighborFinset, SimpleGraph.mem_neighborFinset]
                dsimp only [addEdge]
                tauto
              omega
            have hw_nb_eq : G.neighborFinset w = ({s0, b} : Finset W) := by
              apply Finset.eq_of_subset_of_card_le hw_nb_sub
              have hc2 : ({s0, b} : Finset W).card ≤ 2 := Finset.card_le_two
              rw [card_neighborFinset_eq_degree]
              omega
            have hadj_ws0 : G.Adj w s0 := (G.mem_neighborFinset _ _).mp (by rw [hw_nb_eq]; simp)
            have hadj_wb : G.Adj w b := (G.mem_neighborFinset _ _).mp (by rw [hw_nb_eq]; simp)
            have hw_deg_eq2 : G.degree w = 2 := by
              rw [← card_neighborFinset_eq_degree, hw_nb_eq,
                Finset.card_pair (Finset.mem_erase.mp hs0).1]
            have hw_eq_z : w = z := by
              by_contra hwz
              have := hdeg w hw_ne_x hw_ne_y hwz
              omega
            -- If `G.Adj s0 b`, then `s0 - b` (len 1) and `s0 - w - b` (len 2) + `p_ob.reverse` finish!
            by_cases hadj_s0b : G.Adj s0 b
            · set r1 : G.Walk s0 b := .cons hadj_s0b .nil
              set r2 : G.Walk s0 b := .cons hadj_ws0.symm (.cons hadj_wb .nil)
              have hr1_path : r1.IsPath :=
                Walk.IsPath.cons Walk.IsPath.nil (by simp [(Finset.mem_erase.mp hs0).1])
              have hr2_path : r2.IsPath := by
                apply Walk.IsPath.cons (Walk.IsPath.cons Walk.IsPath.nil (by simp [hw_ne_b]))
                simp only [Walk.support_cons, Walk.support_nil, List.mem_cons,
                  List.not_mem_nil, or_false, not_or]
                exact ⟨hws0.symm, (Finset.mem_erase.mp hs0).1⟩
              have hdisj1 : ∀ t ∈ r1.support, t ∈ p_ob.reverse.support → t = b := by
                intro t ht1 ht2
                rw [Walk.support_reverse, List.mem_reverse] at ht2
                simp only [r1, Walk.support_cons, Walk.support_nil, List.mem_cons,
                  List.not_mem_nil, or_false] at ht1
                rcases ht1 with hts | htb
                · rw [hts] at ht2 ⊢
                  rcases hpob_supp s0 ht2 with hs0_Co | h_eq
                  · exact (Finset.disjoint_left.mp hdisj_so hs0_Cs hs0_Co).elim
                  · exact h_eq
                · exact htb
              have hdisj2 : ∀ t ∈ r2.support, t ∈ p_ob.reverse.support → t = b := by
                intro t ht1 ht2
                rw [Walk.support_reverse, List.mem_reverse] at ht2
                simp only [r2, Walk.support_cons, Walk.support_nil, List.mem_cons,
                  List.not_mem_nil, or_false] at ht1
                rcases ht1 with hts | htw | htb
                · rw [hts] at ht2 ⊢
                  rcases hpob_supp s0 ht2 with hs0_Co | h_eq
                  · exact (Finset.disjoint_left.mp hdisj_so hs0_Cs hs0_Co).elim
                  · exact h_eq
                · rw [htw] at ht2 ⊢
                  rcases hpob_supp w ht2 with hw_Co | h_eq
                  · exact (Finset.disjoint_left.mp hdisj_so hwCs hw_Co).elim
                  · exact h_eq
                · exact htb
              refine ⟨r1.append p_ob.reverse, r2.append p_ob.reverse,
                append_isPath hr1_path hpob_path.reverse hdisj1,
                append_isPath hr2_path hpob_path.reverse hdisj2, ?_⟩
              simp only [r1, r2, Walk.length_append, Walk.length_cons, Walk.length_nil,
                Walk.length_reverse]
              omega
            · -- Otherwise `¬ G.Adj s0 b`! Inspect `Co.card ∈ {1, 2}`:
              by_cases hCo_eq2 : Co.card = 2
              · obtain ⟨w', hw'Co, hw'o0⟩ := Finset.exists_mem_ne (by omega : 1 < Co.card) o0
                have hCo_eq : Co = {o0, w'} :=
                  (Finset.eq_of_subset_of_card_le
                    (by intro t ht; simp only [Finset.mem_insert, Finset.mem_singleton] at ht;
                        rcases ht with rfl | rfl <;> assumption)
                    (by rw [hCo_eq2, Finset.card_pair hw'o0.symm])).symm
                have hw'_ne_s0 : w' ≠ s0 :=
                  fun h ↦ Finset.disjoint_right.mp hdisj_so hw'Co (h ▸ hs0_Cs)
                have hw'_ne_x : w' ≠ x := by
                  rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> assumption
                have hw'_ne_y : w' ≠ y := by
                  rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> assumption
                have hw'_ne_z : w' ≠ z := by
                  rw [← hw_eq_z]
                  exact fun h ↦ Finset.disjoint_left.mp hdisj_so (h.symm ▸ hwCs) hw'Co
                have hw'_nb_sub : G.neighborFinset w' ⊆ ({o0, b} : Finset W) := by
                  intro t ht
                  have hadj_w't : G.Adj w' t := (G.mem_neighborFinset _ _).mp ht
                  by_cases htUb : t ∈ Ub
                  · have htCo : t ∈ Co := by
                      by_contra hnot
                      exact compIn_no_edge_out hw'Co htUb hnot hadj_w't
                    rw [hCo_eq, Finset.mem_insert, Finset.mem_singleton] at htCo
                    rcases htCo with rfl | rfl
                    · simp
                    · exact (G.ne_of_adj hadj_w't rfl).elim
                  · simp only [Ub, Finset.mem_erase, Finset.mem_univ, and_true, not_not] at htUb
                    subst t; simp
                have hc1 := Finset.card_le_card hw'_nb_sub
                have hc2 : ({o0, b} : Finset W).card ≤ 2 := Finset.card_le_two
                rw [card_neighborFinset_eq_degree] at hc1
                have hc3 := hdeg w' hw'_ne_x hw'_ne_y hw'_ne_z
                omega
              · have hCo_eq1 : Co.card = 1 := by
                  have hpos : 1 ≤ Co.card := Finset.card_pos.mpr ⟨o0, ho0_Co⟩
                  omega
                obtain ⟨o1, ho1_eq⟩ := Finset.card_eq_one.mp hCo_eq1
                have ho1_o0 : o0 = o1 := Finset.mem_singleton.mp (ho1_eq ▸ ho0_Co)
                subst o1
                -- Now `Ub = {s0, w, o0}` and `¬ G.Adj s0 b`, so `G.neighborFinset b ⊆ {w, o0}`!
                have hb_nb_sub : G.neighborFinset b ⊆ ({w, o0} : Finset W) := by
                  intro t ht
                  have hadj_bt : G.Adj b t := (G.mem_neighborFinset _ _).mp ht
                  have htUb : t ∈ Ub :=
                    Finset.mem_erase.mpr ⟨(G.ne_of_adj hadj_bt).symm, Finset.mem_univ t⟩
                  have ht_union : t ∈ Cs ∪ Co := by
                    rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
                    · rwa [← hUb_eq]
                    · rw [Finset.union_comm]; rwa [← hUb_eq]
                  rw [hCs_eq, ho1_eq] at ht_union
                  simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at ht_union
                  rcases ht_union with (rfl | rfl) | rfl
                  · exact (hadj_s0b hadj_bt.symm).elim
                  · simp
                  · simp
                have hc1 := Finset.card_le_card hb_nb_sub
                have hc2 : ({w, o0} : Finset W).card ≤ 2 := Finset.card_le_two
                rw [card_neighborFinset_eq_degree] at hc1
                have hb_ne_z : b ≠ z := by rw [← hw_eq_z]; exact hw_ne_b.symm
                have hc3 := hdeg b hbx hby hb_ne_z
                omega
          by_cases hCx2 : Cx.card = 2
          · exact solve_card2_side x y hxUb hyUb (Or.inl ⟨rfl, rfl⟩) hCx2 (by change Cy.card ≤ 2; omega)
              ⟨py_b, hpy_path, hpy_supp⟩
          · have hCy2 : Cy.card = 2 := by
              have hpos : 1 ≤ Cx.card := Finset.card_pos.mpr ⟨x, hxCx⟩
              omega
            obtain ⟨p1, p2, hp1, hp2, hmod⟩ :=
              solve_card2_side y x hyUb hxUb (Or.inr ⟨rfl, rfl⟩) hCy2 (by change Cx.card ≤ 2; omega)
                ⟨px_b, hpx_path, hpx_supp⟩
            exact ⟨p1.reverse, p2.reverse, hp1.reverse, hp2.reverse, by simpa using hmod⟩

/- ### Section 3: Tree distances, 4-point condition, Helly, and cycle-tree modulo 3 -/

noncomputable def uPath {U : Type*} {T : SimpleGraph U} (hT : T.IsTree) (a b : U) : T.Walk a b :=
  (hT.existsUnique_path a b).choose

lemma uPath_isPath {U : Type*} {T : SimpleGraph U} (hT : T.IsTree) (a b : U) :
    (uPath hT a b).IsPath :=
  (hT.existsUnique_path a b).choose_spec.1

lemma eq_uPath_of_isPath {U : Type*} {T : SimpleGraph U} (hT : T.IsTree) {a b : U}
    {p : T.Walk a b} (hp : p.IsPath) : p = uPath hT a b :=
  (hT.existsUnique_path a b).choose_spec.2 p hp

noncomputable def tDist {U : Type*} {T : SimpleGraph U} (hT : T.IsTree) (a b : U) : ℕ :=
  (uPath hT a b).length

@[simp]
lemma uPath_self {U : Type*} {T : SimpleGraph U} (hT : T.IsTree) (a : U) :
    uPath hT a a = .nil :=
  (eq_uPath_of_isPath hT Walk.IsPath.nil).symm

@[simp]
lemma tDist_self {U : Type*} {T : SimpleGraph U} (hT : T.IsTree) (a : U) :
    tDist hT a a = 0 := by
  simp [tDist]

lemma uPath_reverse {U : Type*} {T : SimpleGraph U} (hT : T.IsTree) (a b : U) :
    (uPath hT a b).reverse = uPath hT b a :=
  eq_uPath_of_isPath hT (uPath_isPath hT a b).reverse

lemma tDist_comm {U : Type*} {T : SimpleGraph U} (hT : T.IsTree) (a b : U) :
    tDist hT a b = tDist hT b a := by
  rw [tDist, tDist, ← uPath_reverse, Walk.length_reverse]

lemma tDist_eq_zero_iff {U : Type*} {T : SimpleGraph U} (hT : T.IsTree) {a b : U} :
    tDist hT a b = 0 ↔ a = b := by
  constructor
  · intro h0
    by_contra hab
    have := one_le_length_of_ne hab (uPath hT a b)
    rw [← tDist] at this
    omega
  · rintro rfl
    exact tDist_self hT a

lemma uPath_split {U : Type*} [DecidableEq U] {T : SimpleGraph U} (hT : T.IsTree)
    {a b m : U} (hm : m ∈ (uPath hT a b).support) :
    uPath hT a b = (uPath hT a m).append (uPath hT m b) := by
  have hp := uPath_isPath hT a b
  have h1 : (uPath hT a b).takeUntil m hm = uPath hT a m :=
    eq_uPath_of_isPath hT (hp.takeUntil hm)
  have h2 : (uPath hT a b).dropUntil m hm = uPath hT m b :=
    eq_uPath_of_isPath hT (hp.dropUntil hm)
  have hspec := Walk.take_spec (uPath hT a b) hm
  rw [h1, h2] at hspec
  exact hspec.symm

lemma tDist_split {U : Type*} [DecidableEq U] {T : SimpleGraph U} (hT : T.IsTree)
    {a b m : U} (hm : m ∈ (uPath hT a b).support) :
    tDist hT a b = tDist hT a m + tDist hT m b := by
  have h := congrArg Walk.length (uPath_split hT hm)
  simpa [tDist, Walk.length_append] using h

lemma uPath_support_triangle {U : Type*} [DecidableEq U] {T : SimpleGraph U} (hT : T.IsTree)
    (a b c : U) {v : U} (hv : v ∈ (uPath hT a c).support) :
    v ∈ (uPath hT a b).support ∨ v ∈ (uPath hT b c).support := by
  set w := (uPath hT a b).append (uPath hT b c)
  have heq : w.toPath.1 = uPath hT a c := eq_uPath_of_isPath hT w.toPath.2
  rw [← heq] at hv
  have hv_w : v ∈ w.support := Walk.support_toPath_subset_support w hv
  rw [Walk.support_append] at hv_w
  rcases List.mem_append.mp hv_w with h1 | h2
  · exact Or.inl h1
  · exact Or.inr (List.mem_of_mem_tail h2)

lemma uPath_subpath_support {U : Type*} [DecidableEq U] {T : SimpleGraph U} (hT : T.IsTree)
    {a b x y : U} (hx : x ∈ (uPath hT a b).support) (hy : y ∈ (uPath hT a b).support) :
    ∀ v ∈ (uPath hT x y).support, v ∈ (uPath hT a b).support := by
  have hsplit := uPath_split hT hx
  have hy' : y ∈ (uPath hT a x).support ∨ y ∈ (uPath hT x b).support := by
    rw [hsplit, Walk.support_append] at hy
    rcases List.mem_append.mp hy with h1 | h2
    · exact Or.inl h1
    · exact Or.inr (List.mem_of_mem_tail h2)
  rcases hy' with hy1 | hy2
  · have hy1_rev : y ∈ (uPath hT x a).support := by
      rw [← uPath_reverse, Walk.support_reverse, List.mem_reverse]
      exact hy1
    intro v hv
    have hv_xa : v ∈ (uPath hT x a).support := by
      rw [uPath_split hT hy1_rev, Walk.support_append]
      exact List.mem_append_left _ hv
    rw [← uPath_reverse, Walk.support_reverse, List.mem_reverse] at hv_xa
    rw [hsplit, Walk.support_append]
    exact List.mem_append_left _ hv_xa
  · intro v hv
    have hv_xb : v ∈ (uPath hT x b).support := by
      rw [uPath_split hT hy2, Walk.support_append]
      exact List.mem_append_left _ hv
    rw [hsplit, Walk.support_append]
    rw [support_eq_cons_tail (uPath hT x b), List.mem_cons] at hv_xb
    rcases hv_xb with rfl | htl
    · exact List.mem_append_left _ (Walk.end_mem_support _)
    · exact List.mem_append_right _ htl

lemma tree_median {U : Type*} [DecidableEq U] {T : SimpleGraph U} (hT : T.IsTree)
    (x y z : U) :
    ∃ m : U, m ∈ (uPath hT x y).support ∧
      m ∈ (uPath hT x z).support ∧
      m ∈ (uPath hT y z).support := by
  set S := (uPath hT x z).support.toFinset
  have hxS : x ∈ S := List.mem_toFinset.mpr (Walk.start_mem_support _)
  obtain ⟨m, hmS, q, hq_path, hq_sub, hq_tail⟩ :=
    last_mem_suffix S hxS (uPath hT x y) (uPath_isPath hT x y)
  have hm_xz : m ∈ (uPath hT x z).support := List.mem_toFinset.mp hmS
  have hm_xy : m ∈ (uPath hT x y).support := hq_sub m (Walk.start_mem_support q)
  have hq_eq : q = uPath hT m y := eq_uPath_of_isPath hT hq_path
  set r : T.Walk y z := (uPath hT y m).append (uPath hT m z)
  have hr_path : r.IsPath := by
    apply append_isPath (uPath_isPath hT y m) (uPath_isPath hT m z)
    intro t ht_ym ht_mz
    have ht_q : t ∈ q.support := by
      rw [hq_eq, ← uPath_reverse, Walk.support_reverse, List.mem_reverse]
      exact ht_ym
    have ht_xz : t ∈ S := by
      rw [List.mem_toFinset]
      exact uPath_subpath_support hT hm_xz (Walk.end_mem_support _) t ht_mz
    rw [support_eq_cons_tail q, List.mem_cons] at ht_q
    rcases ht_q with rfl | htl
    · rfl
    · exact (hq_tail t htl ht_xz).elim
  have hr_eq : r = uPath hT y z := eq_uPath_of_isPath hT hr_path
  refine ⟨m, hm_xy, hm_xz, ?_⟩
  rw [← hr_eq, Walk.support_append]
  exact List.mem_append_left _ (Walk.end_mem_support _)

lemma median_legs_disjoint {U : Type*} [DecidableEq U] {T : SimpleGraph U} (hT : T.IsTree)
    {a b m t : U} (hm : m ∈ (uPath hT a b).support)
    (hta : t ∈ (uPath hT m a).support) (htb : t ∈ (uPath hT m b).support) :
    t = m := by
  have hp : ((uPath hT a m).append (uPath hT m b)).IsPath := by
    rw [← uPath_split hT hm]
    exact uPath_isPath hT a b
  rw [Walk.isPath_def, Walk.support_append, List.nodup_append'] at hp
  have hta' : t ∈ (uPath hT a m).support := by
    rw [← uPath_reverse, Walk.support_reverse, List.mem_reverse]
    exact hta
  rw [support_eq_cons_tail (uPath hT m b), List.mem_cons] at htb
  rcases htb with rfl | htl
  · rfl
  · exact (List.disjoint_left.mp hp.2.2 hta' htl).elim

lemma four_point_of_leg {U : Type*} [DecidableEq U] {T : SimpleGraph U} (hT : T.IsTree)
    {a b c w m v : U}
    (hm_ab : m ∈ (uPath hT a b).support)
    (hm_ac : m ∈ (uPath hT a c).support)
    (hm_bc : m ∈ (uPath hT b c).support)
    (hv : v ∈ (uPath hT m a).support)
    (hq_disj : ∀ t ∈ (uPath hT v w).support.tail,
      t ∉ (uPath hT m a).support ∧ t ∉ (uPath hT m b).support ∧ t ∉ (uPath hT m c).support) :
    tDist hT a b + tDist hT c w = tDist hT a c + tDist hT b w := by
  have hd_ab : tDist hT a b = tDist hT m a + tDist hT m b := by
    rw [tDist_split hT hm_ab, tDist_comm hT a m]
  have hd_ac : tDist hT a c = tDist hT m a + tDist hT m c := by
    rw [tDist_split hT hm_ac, tDist_comm hT a m]
  have hd_ma : tDist hT m a = tDist hT m v + tDist hT v a := tDist_split hT hv
  have _ := hd_ma
  -- For any `x ∈ {b, c}` where `uPath m x` only shares `m` with `uPath m a`:
  have leg_dist : ∀ (x : U), m ∈ (uPath hT a x).support →
      (∀ t ∈ (uPath hT v w).support.tail, t ∉ (uPath hT m x).support) →
      tDist hT x w = tDist hT m x + tDist hT m v + tDist hT v w := by
    intro x hmx hqx
    have hxv_path : ((uPath hT x m).append (uPath hT m v)).IsPath := by
      apply append_isPath (uPath_isPath hT x m) (uPath_isPath hT m v)
      intro t ht_xm ht_mv
      have ht_mx : t ∈ (uPath hT m x).support := by
        rw [← uPath_reverse, Walk.support_reverse, List.mem_reverse]
        exact ht_xm
      have ht_ma : t ∈ (uPath hT m a).support :=
        uPath_subpath_support hT (Walk.start_mem_support _) hv t ht_mv
      have hm_xa : m ∈ (uPath hT x a).support := by
        rw [← uPath_reverse, Walk.support_reverse, List.mem_reverse]
        exact hmx
      exact median_legs_disjoint hT hm_xa ht_mx ht_ma
    have hxv_eq : (uPath hT x m).append (uPath hT m v) = uPath hT x v :=
      eq_uPath_of_isPath hT hxv_path
    have hxw_path : ((uPath hT x v).append (uPath hT v w)).IsPath := by
      apply append_isPath (uPath_isPath hT x v) (uPath_isPath hT v w)
      intro t ht_xv ht_vw
      rw [support_eq_cons_tail (uPath hT v w), List.mem_cons] at ht_vw
      rcases ht_vw with rfl | htl
      · rfl
      · exfalso
        rw [← hxv_eq, Walk.support_append] at ht_xv
        rcases List.mem_append.mp ht_xv with h1 | h2
        · have ht_mx : t ∈ (uPath hT m x).support := by
            rw [← uPath_reverse, Walk.support_reverse, List.mem_reverse]
            exact h1
          exact hqx t htl ht_mx
        · have ht_ma : t ∈ (uPath hT m a).support :=
            uPath_subpath_support hT (Walk.start_mem_support _) hv t (List.mem_of_mem_tail h2)
          exact (hq_disj t htl).1 ht_ma
    have hxw_eq := congrArg Walk.length (eq_uPath_of_isPath hT hxw_path)
    have hxv_len := congrArg Walk.length hxv_eq
    simp only [Walk.length_append] at hxw_eq hxv_len
    change tDist hT x v + tDist hT v w = tDist hT x w at hxw_eq
    change tDist hT x m + tDist hT m v = tDist hT x v at hxv_len
    rw [tDist_comm hT x m] at hxv_len
    have _ := hm_bc
    omega
  have hbw := leg_dist b hm_ab (fun t htl ↦ (hq_disj t htl).2.1)
  have hcw := leg_dist c hm_ac (fun t htl ↦ (hq_disj t htl).2.2)
  omega

lemma tree_four_point {U : Type*} [DecidableEq U] {T : SimpleGraph U} (hT : T.IsTree)
    (x y z w : U) :
    tDist hT x y + tDist hT z w = tDist hT x z + tDist hT y w ∨
    tDist hT x y + tDist hT z w = tDist hT x w + tDist hT y z ∨
    tDist hT x z + tDist hT y w = tDist hT x w + tDist hT y z := by
  obtain ⟨m, hm_xy, hm_xz, hm_yz⟩ := tree_median hT x y z
  set S := (uPath hT m x).support.toFinset ∪ (uPath hT m y).support.toFinset ∪
    (uPath hT m z).support.toFinset
  have hmS : m ∈ S := by
    simp only [S, Finset.mem_union, List.mem_toFinset]
    exact Or.inl (Or.inl (Walk.start_mem_support _))
  obtain ⟨v, hvS, q, hq_path, _, hq_tail⟩ :=
    last_mem_suffix S hmS (uPath hT m w) (uPath_isPath hT m w)
  have hq_eq : q = uPath hT v w := eq_uPath_of_isPath hT hq_path
  have hdisj : ∀ t ∈ (uPath hT v w).support.tail,
      t ∉ (uPath hT m x).support ∧ t ∉ (uPath hT m y).support ∧ t ∉ (uPath hT m z).support := by
    intro t htl
    rw [← hq_eq] at htl
    have htS := hq_tail t htl
    simp only [S, Finset.mem_union, List.mem_toFinset, not_or] at htS
    exact ⟨htS.1.1, htS.1.2, htS.2⟩
  simp only [S, Finset.mem_union, List.mem_toFinset] at hvS
  have hm_yx : m ∈ (uPath hT y x).support := by
    rw [← uPath_reverse, Walk.support_reverse, List.mem_reverse]; exact hm_xy
  have hm_zx : m ∈ (uPath hT z x).support := by
    rw [← uPath_reverse, Walk.support_reverse, List.mem_reverse]; exact hm_xz
  have hm_zy : m ∈ (uPath hT z y).support := by
    rw [← uPath_reverse, Walk.support_reverse, List.mem_reverse]; exact hm_yz
  rcases hvS with (hvx | hvy) | hvz
  · exact Or.inl (four_point_of_leg hT hm_xy hm_xz hm_yz hvx hdisj)
  · right; left
    have h := four_point_of_leg hT hm_yx hm_yz hm_xz hvy
      (fun t htl ↦ ⟨(hdisj t htl).2.1, (hdisj t htl).1, (hdisj t htl).2.2⟩)
    rw [tDist_comm hT y x] at h
    omega
  · right; right
    have h := four_point_of_leg hT hm_zx hm_zy hm_xy hvz
      (fun t htl ↦ ⟨(hdisj t htl).2.2, (hdisj t htl).1, (hdisj t htl).2.1⟩)
    rw [tDist_comm hT z x, tDist_comm hT z y] at h
    omega

lemma tree_helly {U : Type*} [DecidableEq U] {T : SimpleGraph U} (hT : T.IsTree)
    (r0 : U) {k : ℕ} (hk : 0 < k) (a b : Fin k → U)
    (hinter : ∀ i j : Fin k, ∃ w : U,
      w ∈ (uPath hT (a i) (b i)).support ∧ w ∈ (uPath hT (a j) (b j)).support) :
    ∃ v : U, ∀ i : Fin k, v ∈ (uPath hT (a i) (b i)).support := by
  have top_ex : ∀ i : Fin k, ∃ m : U,
      m ∈ (uPath hT (a i) (b i)).support ∧
      m ∈ (uPath hT r0 (a i)).support ∧
      m ∈ (uPath hT r0 (b i)).support :=
    fun i ↦ by
      obtain ⟨m, h1, h2, h3⟩ := tree_median hT r0 (a i) (b i)
      exact ⟨m, h3, h1, h2⟩
  let top : Fin k → U := fun i ↦ (top_ex i).choose
  have htop_ab : ∀ i, top i ∈ (uPath hT (a i) (b i)).support := fun i ↦ (top_ex i).choose_spec.1
  have htop_a : ∀ i, top i ∈ (uPath hT r0 (a i)).support := fun i ↦ (top_ex i).choose_spec.2.1
  have htop_b : ∀ i, top i ∈ (uPath hT r0 (b i)).support := fun i ↦ (top_ex i).choose_spec.2.2
  -- Key property: for any `w ∈ uPath (a i) (b i)`, `top i ∈ uPath r0 w`!
  have htop_on_r0 : ∀ (i : Fin k) (w : U),
      w ∈ (uPath hT (a i) (b i)).support → top i ∈ (uPath hT r0 w).support := by
    intro i w hw
    rw [uPath_split hT (htop_ab i), Walk.support_append] at hw
    rcases List.mem_append.mp hw with hw1 | hw2
    · have hw_ta : w ∈ (uPath hT (top i) (a i)).support := by
        rw [← uPath_reverse, Walk.support_reverse, List.mem_reverse]; exact hw1
      have hw_r0a : w ∈ (uPath hT r0 (a i)).support :=
        uPath_subpath_support hT (htop_a i) (Walk.end_mem_support _) w hw_ta
      -- Wait: uPath r0 (a i) = (uPath r0 (top i)).append (uPath (top i) (a i)), and w ∈ uPath (top i) (a i)!
      have hpath_r0w : ((uPath hT r0 (top i)).append (uPath hT (top i) w)).IsPath := by
        have hfull : ((uPath hT r0 (top i)).append (uPath hT (top i) (a i))).IsPath := by
          rw [← uPath_split hT (htop_a i)]
          exact uPath_isPath hT r0 (a i)
        apply append_isPath (uPath_isPath hT r0 (top i)) (uPath_isPath hT (top i) w)
        intro t ht1 ht2
        have ht2' : t ∈ (uPath hT (top i) (a i)).support :=
          uPath_subpath_support hT (Walk.start_mem_support _) hw_ta t ht2
        rw [Walk.isPath_def, Walk.support_append, List.nodup_append'] at hfull
        rw [support_eq_cons_tail (uPath hT (top i) (a i)), List.mem_cons] at ht2'
        rcases ht2' with rfl | htl
        · rfl
        · exact (List.disjoint_left.mp hfull.2.2 ht1 htl).elim
      rw [← eq_uPath_of_isPath hT hpath_r0w, Walk.support_append]
      exact List.mem_append_left _ (Walk.end_mem_support _)
    · have hw_tb : w ∈ (uPath hT (top i) (b i)).support := List.mem_of_mem_tail hw2
      have hpath_r0w : ((uPath hT r0 (top i)).append (uPath hT (top i) w)).IsPath := by
        have hfull : ((uPath hT r0 (top i)).append (uPath hT (top i) (b i))).IsPath := by
          rw [← uPath_split hT (htop_b i)]
          exact uPath_isPath hT r0 (b i)
        apply append_isPath (uPath_isPath hT r0 (top i)) (uPath_isPath hT (top i) w)
        intro t ht1 ht2
        have ht2' : t ∈ (uPath hT (top i) (b i)).support :=
          uPath_subpath_support hT (Walk.start_mem_support _) hw_tb t ht2
        rw [Walk.isPath_def, Walk.support_append, List.nodup_append'] at hfull
        rw [support_eq_cons_tail (uPath hT (top i) (b i)), List.mem_cons] at ht2'
        rcases ht2' with rfl | htl
        · rfl
        · exact (List.disjoint_left.mp hfull.2.2 ht1 htl).elim
      rw [← eq_uPath_of_isPath hT hpath_r0w, Walk.support_append]
      exact List.mem_append_left _ (Walk.end_mem_support _)
  -- Choose `i0 : Fin k` maximizing `tDist hT r0 (top i0)`.
  have hne : (Finset.univ : Finset (Fin k)).Nonempty :=
    ⟨⟨0, hk⟩, Finset.mem_univ _⟩
  obtain ⟨i0, _, hi0_max⟩ := Finset.exists_max_image Finset.univ (fun i ↦ tDist hT r0 (top i)) hne
  refine ⟨top i0, fun j ↦ ?_⟩
  obtain ⟨w, hwi0, hwj⟩ := hinter i0 j
  have h1 : top i0 ∈ (uPath hT r0 w).support := htop_on_r0 i0 w hwi0
  have h2 : top j ∈ (uPath hT r0 w).support := htop_on_r0 j w hwj
  have hle : tDist hT r0 (top j) ≤ tDist hT r0 (top i0) := hi0_max j (Finset.mem_univ j)
  rw [uPath_split hT h1, Walk.support_append] at h2
  rcases List.mem_append.mp h2 with h_before | h_after
  · -- `top j ∈ uPath r0 (top i0)`, so `top i0 ∈ uPath (top j) w ⊆ uPath (a j) (b j)`!
    have hsplit_r0w := uPath_split hT (htop_on_r0 j w hwj)
    have hsplit_i0 := uPath_split hT h_before
    have hi0_on_jw : top i0 ∈ (uPath hT (top j) w).support := by
      have hp_jw : ((uPath hT (top j) (top i0)).append (uPath hT (top i0) w)).IsPath := by
        have hfull : ((uPath hT r0 (top i0)).append (uPath hT (top i0) w)).IsPath := by
          rw [← uPath_split hT h1]
          exact uPath_isPath hT r0 w
        apply append_isPath (uPath_isPath hT (top j) (top i0)) (uPath_isPath hT (top i0) w)
        intro t ht1 ht2
        have ht1' : t ∈ (uPath hT r0 (top i0)).support :=
          uPath_subpath_support hT h_before (Walk.end_mem_support _) t ht1
        rw [Walk.isPath_def, Walk.support_append, List.nodup_append'] at hfull
        rw [support_eq_cons_tail (uPath hT (top i0) w), List.mem_cons] at ht2
        rcases ht2 with rfl | htl
        · rfl
        · exact (List.disjoint_left.mp hfull.2.2 ht1' htl).elim
      rw [← eq_uPath_of_isPath hT hp_jw, Walk.support_append]
      exact List.mem_append_left _ (Walk.end_mem_support _)
    exact uPath_subpath_support hT (htop_ab j) hwj (top i0) hi0_on_jw
  · -- `top j ∈ (uPath (top i0) w).support.tail`, impossible since `tDist r0 (top j) ≤ tDist r0 (top i0)`!
    have hj_mem : top j ∈ (uPath hT (top i0) w).support := List.mem_of_mem_tail h_after
    have hd_r0j : tDist hT r0 (top j) = tDist hT r0 (top i0) + tDist hT (top i0) (top j) := by
      have hp_r0j : ((uPath hT r0 (top i0)).append (uPath hT (top i0) (top j))).IsPath := by
        have hfull : ((uPath hT r0 (top i0)).append (uPath hT (top i0) w)).IsPath := by
          rw [← uPath_split hT h1]
          exact uPath_isPath hT r0 w
        apply append_isPath (uPath_isPath hT r0 (top i0)) (uPath_isPath hT (top i0) (top j))
        intro t ht1 ht2
        have ht2' : t ∈ (uPath hT (top i0) w).support :=
          uPath_subpath_support hT (Walk.start_mem_support _) hj_mem t ht2
        rw [Walk.isPath_def, Walk.support_append, List.nodup_append'] at hfull
        rw [support_eq_cons_tail (uPath hT (top i0) w), List.mem_cons] at ht2'
        rcases ht2' with rfl | htl
        · rfl
        · exact (List.disjoint_left.mp hfull.2.2 ht1 htl).elim
      have heq := congrArg Walk.length (eq_uPath_of_isPath hT hp_r0j)
      simpa [tDist, Walk.length_append] using heq.symm
    have h0 : tDist hT (top i0) (top j) = 0 := by omega
    rw [(tDist_eq_zero_iff hT).mp h0]
    exact htop_ab j

/- Cyclic vertex sequence from a simple cycle, and `cycle_tree_mod3`. -/

lemma eq_of_mod_eq_of_lt_add {m a b : ℕ} (hab : a ≤ b) (hlt : b < a + m) (hmod : a % m = b % m) :
    a = b := by
  have hm : 0 < m := by omega
  have h1 := Nat.div_add_mod a m
  have h2 := Nat.div_add_mod b m
  rw [hmod] at h1
  by_cases hdiv : b / m ≤ a / m
  · have hmul : m * (b / m) ≤ m * (a / m) := Nat.mul_le_mul_left m hdiv
    omega
  · have hdiv' : a / m + 1 ≤ b / m := by omega
    have hmul : m * (a / m + 1) ≤ m * (b / m) := Nat.mul_le_mul_left m hdiv'
    have hmul' : m * (a / m) + m ≤ m * (b / m) := by linarith
    omega

structure IsCyclicSeq {V : Type*} (G : SimpleGraph V) (m : ℕ) (c : ℕ → V) : Prop where
  three_le : 3 ≤ m
  per : ∀ i, c (i + m) = c i
  adj : ∀ i, G.Adj (c i) (c (i + 1))
  inj : ∀ {i j}, i < m → j < m → c i = c j → i = j

lemma IsCyclicSeq.add_mul {V : Type*} {G : SimpleGraph V} {m : ℕ} {c : ℕ → V}
    (hc : IsCyclicSeq G m c) (r : ℕ) : ∀ q : ℕ, c (r + m * q) = c r
  | 0 => by simp
  | q + 1 => by
    have heq : r + m * (q + 1) = (r + m * q) + m := by ring
    rw [heq, hc.per, hc.add_mul r q]

lemma IsCyclicSeq.mod_eq {V : Type*} {G : SimpleGraph V} {m : ℕ} {c : ℕ → V}
    (hc : IsCyclicSeq G m c) (i : ℕ) : c (i % m) = c i := by
  have h := hc.add_mul (i % m) (i / m)
  rw [Nat.mod_add_div] at h
  exact h.symm

lemma IsCyclicSeq.eq_iff {V : Type*} {G : SimpleGraph V} {m : ℕ} {c : ℕ → V}
    (hc : IsCyclicSeq G m c) {i j : ℕ} : c i = c j ↔ i % m = j % m := by
  have hm : 0 < m := by have := hc.three_le; omega
  rw [← hc.mod_eq i, ← hc.mod_eq j]
  exact ⟨hc.inj (Nat.mod_lt _ hm) (Nat.mod_lt _ hm), congrArg c⟩

def cArc {V : Type*} {G : SimpleGraph V} {m : ℕ} {c : ℕ → V} (hc : IsCyclicSeq G m c)
    (s : ℕ) : ∀ k : ℕ, G.Walk (c s) (c (s + k))
  | 0 => .nil
  | k + 1 => (cArc hc s k).append (.cons (hc.adj (s + k)) .nil)

@[simp]
lemma cArc_length {V : Type*} {G : SimpleGraph V} {m : ℕ} {c : ℕ → V}
    (hc : IsCyclicSeq G m c) (s k : ℕ) : (cArc hc s k).length = k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [cArc, Walk.length_append, ih]

lemma mem_cArc_support {V : Type*} {G : SimpleGraph V} {m : ℕ} {c : ℕ → V}
    (hc : IsCyclicSeq G m c) (s k : ℕ) (v : V) :
    v ∈ (cArc hc s k).support ↔ ∃ t ≤ k, v = c (s + t) := by
  induction k with
  | zero =>
    simp [cArc]
  | succ k ih =>
    dsimp only [cArc]
    rw [Walk.support_append]
    simp only [Walk.support_cons, Walk.support_nil, List.tail_cons, List.mem_append,
      List.mem_singleton, ih]
    constructor
    · rintro (⟨t, htk, rfl⟩ | rfl)
      · exact ⟨t, by omega, rfl⟩
      · exact ⟨k + 1, le_rfl, rfl⟩
    · rintro ⟨t, htk1, rfl⟩
      by_cases htk : t ≤ k
      · exact Or.inl ⟨t, htk, rfl⟩
      · have hteq : t = k + 1 := by omega
        subst hteq
        exact Or.inr rfl

lemma cArc_isPath {V : Type*} {G : SimpleGraph V} {m : ℕ} {c : ℕ → V}
    (hc : IsCyclicSeq G m c) (s : ℕ) {k : ℕ} (hk : k < m) :
    (cArc hc s k).IsPath := by
  induction k with
  | zero => exact Walk.IsPath.nil
  | succ k ih =>
    dsimp only [cArc]
    apply append_isPath (ih (by omega))
      (Walk.IsPath.cons Walk.IsPath.nil (by simp only [Walk.support_nil, List.mem_singleton]; exact G.ne_of_adj (hc.adj (s + k))))
    intro v hv1 hv2
    rw [mem_cArc_support] at hv1
    rcases hv1 with ⟨t, htk, rfl⟩
    simp only [Walk.support_cons, Walk.support_nil, List.mem_cons,
      List.not_mem_nil, or_false] at hv2
    rcases hv2 with heq | heq
    · exact heq
    · exfalso
      have heq' : c (s + t) = c (s + (k + 1)) := heq
      have hmod := (hc.eq_iff).mp heq'
      have h_eq := eq_of_mod_eq_of_lt_add (a := s + t) (b := s + (k + 1))
        (by omega) (by omega) hmod
      omega

def mapSubWalk {V : Type*} {G : SimpleGraph V} {H : Finset V}
    {T : SimpleGraph {w : V // w ∈ (H : Set V)}}
    (hTG : ∀ x y, T.Adj x y → G.Adj x.1 y.1) :
    ∀ {a b : {w : V // w ∈ (H : Set V)}}, T.Walk a b → G.Walk a.1 b.1
  | _, _, .nil => .nil
  | _, _, .cons hadj rest => .cons (hTG _ _ hadj) (mapSubWalk hTG rest)

@[simp]
lemma mapSubWalk_length {V : Type*} {G : SimpleGraph V} {H : Finset V}
    {T : SimpleGraph {w : V // w ∈ (H : Set V)}}
    (hTG : ∀ x y, T.Adj x y → G.Adj x.1 y.1)
    {a b : {w : V // w ∈ (H : Set V)}} (p : T.Walk a b) :
    (mapSubWalk hTG p).length = p.length := by
  induction p with
  | nil => rfl
  | cons _ _ ih =>
    dsimp only [mapSubWalk]
    rw [Walk.length_cons, Walk.length_cons, ih]

lemma mapSubWalk_support_mem {V : Type*} {G : SimpleGraph V} {H : Finset V}
    {T : SimpleGraph {w : V // w ∈ (H : Set V)}}
    (hTG : ∀ x y, T.Adj x y → G.Adj x.1 y.1)
    {a b : {w : V // w ∈ (H : Set V)}} (p : T.Walk a b) :
    ∀ v ∈ (mapSubWalk hTG p).support,
      ∃ hv : v ∈ (H : Set V), (⟨v, hv⟩ : {w : V // w ∈ (H : Set V)}) ∈ p.support := by
  induction p with
  | @nil u0 =>
    intro v hv
    dsimp only [mapSubWalk] at hv
    simp only [Walk.support_nil, List.mem_singleton] at hv
    subst hv
    exact ⟨u0.2, Walk.start_mem_support _⟩
  | @cons u0 _ _ _ rest ih =>
    intro v hv
    dsimp only [mapSubWalk] at hv
    simp only [Walk.support_cons, List.mem_cons] at hv
    rcases hv with rfl | hv
    · exact ⟨u0.2, Walk.start_mem_support _⟩
    · obtain ⟨hvH, hvm⟩ := ih v hv
      exact ⟨hvH, List.mem_cons_of_mem _ hvm⟩

lemma mapSubWalk_isPath {V : Type*} {G : SimpleGraph V} {H : Finset V}
    {T : SimpleGraph {w : V // w ∈ (H : Set V)}}
    (hTG : ∀ x y, T.Adj x y → G.Adj x.1 y.1)
    {a b : {w : V // w ∈ (H : Set V)}} {p : T.Walk a b} (hp : p.IsPath) :
    (mapSubWalk hTG p).IsPath := by
  induction p with
  | nil => exact Walk.IsPath.nil
  | @cons u0 _ _ _ rest ih =>
    have hnd := hp.support_nodup
    simp only [Walk.support_cons, List.nodup_cons] at hnd
    dsimp only [mapSubWalk]
    apply Walk.IsPath.cons (ih hp.of_cons)
    intro hm
    obtain ⟨huH, hum⟩ := mapSubWalk_support_mem hTG rest u0.1 hm
    have heq : (⟨u0.1, huH⟩ : {w : V // w ∈ (H : Set V)}) = u0 := Subtype.ext rfl
    exact hnd.1 (heq ▸ hum)

theorem cycle_tree_mod3 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    {m : ℕ} (hm5 : 5 ≤ m) (hm3 : m % 3 ≠ 0)
    {c : ℕ → V} (hc : IsCyclicSeq G m c)
    {H : Finset V} (hc_not_H : ∀ i, c i ∉ H)
    {T : SimpleGraph {w : V // w ∈ (H : Set V)}} (hT : T.IsTree)
    (hTG : ∀ x y, T.Adj x y → G.Adj x.1 y.1)
    (u : ℕ → {w : V // w ∈ (H : Set V)})
    (hu_adj : ∀ i, i < m → G.Adj (c i) (u i).1) :
    HasMod3Cycle G := by
  by_contra hno_mod3
  -- Helper: bridge walk `c i - u i -> T -> u j - c j` for `i < m, j < m, i ≠ j`.
  have mkBridge : ∀ (i j : ℕ), i < m → j < m → i ≠ j →
      ∃ b : G.Walk (c i) (c j), b.IsPath ∧ b.length = tDist hT (u i) (u j) + 2 ∧
        ∀ v ∈ b.support, v = c i ∨ v = c j ∨
          ∃ hv : v ∈ (H : Set V),
            (⟨v, hv⟩ : {w : V // w ∈ (H : Set V)}) ∈ (uPath hT (u i) (u j)).support := by
    intro i j hi hj hij
    have hci_ne_cj : c i ≠ c j := fun heq ↦ hij (hc.inj hi hj heq)
    set tWalk := mapSubWalk hTG (uPath hT (u i) (u j))
    have ht_path : tWalk.IsPath := mapSubWalk_isPath hTG (uPath_isPath hT (u i) (u j))
    have hcj_not_t : c j ∉ tWalk.support := by
      intro hm
      obtain ⟨hcH, _⟩ := mapSubWalk_support_mem hTG _ (c j) hm
      exact hc_not_H j hcH
    have hr_path : (tWalk.append (.cons (hu_adj j hj).symm .nil)).IsPath := by
      apply append_isPath ht_path
        (Walk.IsPath.cons Walk.IsPath.nil (by simp [G.ne_of_adj (hu_adj j hj).symm]))
      intro v hv1 hv2
      simp only [Walk.support_cons, Walk.support_nil, List.mem_cons,
        List.not_mem_nil, or_false] at hv2
      rcases hv2 with rfl | rfl
      · rfl
      · exact (hcj_not_t hv1).elim
    have hci_not_r : c i ∉ (tWalk.append (.cons (hu_adj j hj).symm .nil)).support := by
      intro hm
      rw [Walk.support_append] at hm
      simp only [Walk.support_cons, Walk.support_nil, List.tail_cons, List.mem_append,
        List.mem_singleton] at hm
      rcases hm with hm1 | heq
      · obtain ⟨hcH, _⟩ := mapSubWalk_support_mem hTG _ (c i) hm1
        exact hc_not_H i hcH
      · exact hci_ne_cj heq
    set b : G.Walk (c i) (c j) :=
      .cons (hu_adj i hi) (tWalk.append (.cons (hu_adj j hj).symm .nil))
    refine ⟨b, Walk.IsPath.cons hr_path hci_not_r, ?_, ?_⟩
    · simp [b, tWalk, tDist, Walk.length_append]
    · intro v hv
      simp only [b, Walk.support_cons, Walk.support_append, Walk.support_nil, List.tail_cons,
        List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | hvt | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inr (mapSubWalk_support_mem hTG _ v hvt))
      · exact Or.inr (Or.inl rfl)
  -- Single-bridge congruence exclusion for `i < j < m`.
  have single_excl : ∀ (i j : ℕ), i < j → j < m →
      (tDist hT (u i) (u j) + 2 + (j - i)) % 3 ≠ 0 ∧
      (tDist hT (u i) (u j) + 2 + (m + i - j)) % 3 ≠ 0 := by
    intro i j hij hj
    have hi : i < m := by omega
    have hci_ne_cj : c i ≠ c j := fun heq ↦ (Nat.ne_of_lt hij) (hc.inj hi hj heq)
    obtain ⟨b, hb_path, hb_len, hb_supp⟩ := mkBridge i j hi hj (Nat.ne_of_lt hij)
    constructor
    · intro hmod0
      apply hno_mod3
      have hij_eq : i + (j - i) = j := by omega
      set a0 : G.Walk (c i) (c (i + (j - i))) := cArc hc i (j - i)
      have ha0_path : a0.IsPath := cArc_isPath hc i (by omega)
      set a : G.Walk (c i) (c j) := a0.copy rfl (congrArg c hij_eq)
      have ha_path : a.IsPath := (Walk.isPath_copy _ _ _).mpr ha0_path
      apply cycle_of_two_paths_mod3 hci_ne_cj hb_path ha_path
      · intro v hvb hva
        rw [Walk.support_copy, mem_cArc_support] at hva
        rcases hva with ⟨t, _, rfl⟩
        rcases hb_supp (c (i + t)) hvb with h1 | h2 | ⟨hcH, _⟩
        · exact Or.inl h1
        · exact Or.inr h2
        · exact (hc_not_H (i + t) hcH).elim
      · rw [hb_len, Walk.length_copy, cArc_length]
        exact hmod0
    · intro hmod0
      apply hno_mod3
      have hji_eq : c (j + (m + i - j)) = c i := by
        have h1 : j + (m + i - j) = i + m := by omega
        rw [h1, hc.per]
      set a0 : G.Walk (c j) (c (j + (m + i - j))) := cArc hc j (m + i - j)
      have ha0_path : a0.IsPath := cArc_isPath hc j (by omega)
      set a : G.Walk (c i) (c j) := (a0.copy rfl hji_eq).reverse
      have ha_path : a.IsPath := ((Walk.isPath_copy _ _ _).mpr ha0_path).reverse
      apply cycle_of_two_paths_mod3 hci_ne_cj hb_path ha_path
      · intro v hvb hva
        rw [Walk.support_reverse, List.mem_reverse, Walk.support_copy, mem_cArc_support] at hva
        rcases hva with ⟨t, _, rfl⟩
        rcases hb_supp (c (j + t)) hvb with h1 | h2 | ⟨hcH, _⟩
        · exact Or.inl h1
        · exact Or.inr h2
        · exact (hc_not_H (j + t) hcH).elim
      · rw [hb_len, Walk.length_reverse, Walk.length_copy, cArc_length]
        exact hmod0
  -- Split into `m % 3 = 1` (`m ≥ 7`) and `m % 3 = 2` (`m ≥ 5`).
  have hm_cases : m % 3 = 1 ∨ m % 3 = 2 := by omega
  rcases hm_cases with hm1 | hm2
  · -- Case `m % 3 = 1`: `m ≥ 7`, 4-point tree contradiction on `{0, 1, 2, 4, 5}`!
    have hm7 : 7 ≤ m := by omega
    have hd01 : tDist hT (u 0) (u 1) % 3 = 2 := by
      have h := single_excl 0 1 (by omega) (by omega); omega
    have hd12 : tDist hT (u 1) (u 2) % 3 = 2 := by
      have h := single_excl 1 2 (by omega) (by omega); omega
    have hd45 : tDist hT (u 4) (u 5) % 3 = 2 := by
      have h := single_excl 4 5 (by omega) (by omega); omega
    have hd04 : tDist hT (u 0) (u 4) % 3 = 2 := by
      have h := single_excl 0 4 (by omega) (by omega); omega
    have hd15 : tDist hT (u 1) (u 5) % 3 = 2 := by
      have h := single_excl 1 5 (by omega) (by omega); omega
    have hd14 : tDist hT (u 1) (u 4) % 3 = 2 := by
      have h := single_excl 1 4 (by omega) (by omega); omega
    have hd25 : tDist hT (u 2) (u 5) % 3 = 2 := by
      have h := single_excl 2 5 (by omega) (by omega); omega
    have hd02 : tDist hT (u 0) (u 2) % 3 ≠ 2 := by
      have h := (single_excl 0 2 (by omega) (by omega)).1; omega
    have hd24 : tDist hT (u 2) (u 4) % 3 ≠ 2 := by
      have h := (single_excl 2 4 (by omega) (by omega)).1; omega
    have hd05 : tDist hT (u 0) (u 5) % 3 ≠ 2 := by
      have h := (single_excl 0 5 (by omega) (by omega)).2; omega
    have heq24 : tDist hT (u 2) (u 4) % 3 = tDist hT (u 0) (u 2) % 3 := by
      have fp1 := tree_four_point hT (u 0) (u 1) (u 2) (u 4); omega
    have heq05 : tDist hT (u 0) (u 5) % 3 = tDist hT (u 0) (u 2) % 3 := by
      have fp2 := tree_four_point hT (u 0) (u 1) (u 2) (u 5); omega
    have fp3 := tree_four_point hT (u 0) (u 2) (u 4) (u 5)
    omega
  · -- Case `m % 3 = 2`: `m ≥ 5`, 5 diagonals on `{0, 1, 2, 3, 4}` + `tree_helly`!
    have hd01 : tDist hT (u 0) (u 1) % 3 ≠ 0 := by
      have h := (single_excl 0 1 (by omega) (by omega)).1; omega
    have hd12 : tDist hT (u 1) (u 2) % 3 ≠ 0 := by
      have h := (single_excl 1 2 (by omega) (by omega)).1; omega
    have hd02 : tDist hT (u 0) (u 2) % 3 = 0 := by
      have h := single_excl 0 2 (by omega) (by omega); omega
    have hd13 : tDist hT (u 1) (u 3) % 3 = 0 := by
      have h := single_excl 1 3 (by omega) (by omega); omega
    have hd24 : tDist hT (u 2) (u 4) % 3 = 0 := by
      have h := single_excl 2 4 (by omega) (by omega); omega
    have hd03 : tDist hT (u 0) (u 3) % 3 = 0 := by
      have h := single_excl 0 3 (by omega) (by omega); omega
    have hd14 : tDist hT (u 1) (u 4) % 3 = 0 := by
      have h := single_excl 1 4 (by omega) (by omega); omega
    -- Shape A: two non-overlapping bridges with unit C-edges `(j1, j2)` and `(i1, i2)`.
    have inter_short : ∀ (i1 j1 i2 j2 : ℕ),
        i1 < m → j1 < m → i2 < m → j2 < m →
        i1 ≠ j1 → i1 ≠ i2 → i1 ≠ j2 → j1 ≠ i2 → j1 ≠ j2 → i2 ≠ j2 →
        G.Adj (c j1) (c j2) → G.Adj (c i1) (c i2) →
        tDist hT (u i1) (u j1) % 3 = 0 → tDist hT (u i2) (u j2) % 3 = 0 →
        ∃ w, w ∈ (uPath hT (u i1) (u j1)).support ∧ w ∈ (uPath hT (u i2) (u j2)).support := by
      intro i1 j1 i2 j2 hi1 hj1 hi2 hj2 h1 h2 h3 h4 h5 h6 hadj_j hadj_i hd1 hd2
      by_contra hno_w
      push Not at hno_w
      apply hno_mod3
      obtain ⟨b1, hb1_path, hb1_len, hb1_supp⟩ := mkBridge i1 j1 hi1 hj1 h1
      obtain ⟨b2, hb2_path, hb2_len, hb2_supp⟩ := mkBridge i2 j2 hi2 hj2 h6
      have hcj2_not_b1 : c j2 ∉ b1.support := by
        intro hm
        rcases hb1_supp (c j2) hm with heq | heq | ⟨hcH, _⟩
        · exact h3 (hc.inj hi1 hj2 heq.symm)
        · exact h5 (hc.inj hj1 hj2 heq.symm)
        · exact hc_not_H j2 hcH
      have hci1_not_b2 : c i1 ∉ b2.support := by
        intro hm
        rcases hb2_supp (c i1) hm with heq | heq | ⟨hcH, _⟩
        · exact h2 (hc.inj hi1 hi2 heq)
        · exact h3 (hc.inj hi1 hj2 heq)
        · exact hc_not_H i1 hcH
      set P : G.Walk (c i1) (c j2) := b1.append (.cons hadj_j .nil)
      set Q : G.Walk (c i1) (c j2) := .cons hadj_i b2
      have hP_path : P.IsPath := by
        apply append_isPath hb1_path
          (Walk.IsPath.cons Walk.IsPath.nil (by simp [G.ne_of_adj hadj_j]))
        intro v hv1 hv2
        simp only [Walk.support_cons, Walk.support_nil, List.mem_cons,
          List.not_mem_nil, or_false] at hv2
        rcases hv2 with rfl | rfl
        · rfl
        · exact (hcj2_not_b1 hv1).elim
      have hQ_path : Q.IsPath := Walk.IsPath.cons hb2_path hci1_not_b2
      have hci1_ne_cj2 : c i1 ≠ c j2 := fun heq ↦ h3 (hc.inj hi1 hj2 heq)
      apply cycle_of_two_paths_mod3 hci1_ne_cj2 hP_path hQ_path
      · intro v hvP hvQ
        simp only [P, Walk.support_append, Walk.support_cons, Walk.support_nil, List.tail_cons,
          List.mem_append, List.mem_singleton] at hvP
        simp only [Q, Walk.support_cons, List.mem_cons] at hvQ
        rcases hvP with hvb1 | rfl
        · rcases hvQ with rfl | hvb2
          · exact Or.inl rfl
          · rcases hb1_supp v hvb1 with rfl | rfl | ⟨hvH1, hvm1⟩
            · exact Or.inl rfl
            · rcases hb2_supp (c j1) hvb2 with heq | heq | ⟨hcH, _⟩
              · exact (h4 (hc.inj hj1 hi2 heq)).elim
              · exact (h5 (hc.inj hj1 hj2 heq)).elim
              · exact (hc_not_H j1 hcH).elim
            · rcases hb2_supp v hvb2 with rfl | rfl | ⟨hvH2, hvm2⟩
              · exact (hc_not_H i2 hvH1).elim
              · exact Or.inr rfl
              · have heq_sub : (⟨v, hvH2⟩ : {w : V // w ∈ (H : Set V)}) = ⟨v, hvH1⟩ :=
                  Subtype.ext rfl
                exact (hno_w ⟨v, hvH1⟩ hvm1 (heq_sub ▸ hvm2)).elim
        · exact Or.inr rfl
      · simp only [P, Q, Walk.length_append, Walk.length_cons, Walk.length_nil, hb1_len, hb2_len]
        omega
    -- Shape B: bridges `(0, j1)` and `(i2, 4)` with `j1, i2 ∈ {1, 2, 3}`, `j1 ≠ i2`, `G.Adj (c j1) (c i2)`,
    -- closed by the long arc `c 4 -> ... -> c m = c 0` of length `m - 4`.
    have inter_long : ∀ (j1 i2 : ℕ),
        1 ≤ j1 → j1 ≤ 3 → 1 ≤ i2 → i2 ≤ 3 → j1 ≠ i2 →
        G.Adj (c j1) (c i2) →
        tDist hT (u 0) (u j1) % 3 = 0 → tDist hT (u i2) (u 4) % 3 = 0 →
        ∃ w, w ∈ (uPath hT (u 0) (u j1)).support ∧ w ∈ (uPath hT (u i2) (u 4)).support := by
      intro j1 i2 hj1_lo hj1_hi hi2_lo hi2_hi hj1_ne_i2 hadj_mid hd1 hd2
      by_contra hno_w
      push Not at hno_w
      apply hno_mod3
      obtain ⟨b1, hb1_path, hb1_len, hb1_supp⟩ := mkBridge 0 j1 (by omega) (by omega) (by omega)
      obtain ⟨b2, hb2_path, hb2_len, hb2_supp⟩ := mkBridge i2 4 (by omega) (by omega) (by omega)
      have hci2_not_b1 : c i2 ∉ b1.support := by
        intro hm
        rcases hb1_supp (c i2) hm with heq | heq | ⟨hcH, _⟩
        · have := hc.inj (by omega) (by omega) heq; omega
        · exact hj1_ne_i2.symm (hc.inj (by omega) (by omega) heq)
        · exact hc_not_H i2 hcH
      have hb1_mid_path : (b1.append (.cons hadj_mid .nil)).IsPath := by
        apply append_isPath hb1_path
          (Walk.IsPath.cons Walk.IsPath.nil (by simp [G.ne_of_adj hadj_mid]))
        intro v hv1 hv2
        simp only [Walk.support_cons, Walk.support_nil, List.mem_cons,
          List.not_mem_nil, or_false] at hv2
        rcases hv2 with rfl | rfl
        · rfl
        · exact (hci2_not_b1 hv1).elim
      set P : G.Walk (c 0) (c 4) := (b1.append (.cons hadj_mid .nil)).append b2
      have hP_path : P.IsPath := by
        apply append_isPath hb1_mid_path hb2_path
        intro v hv1 hv2
        rw [Walk.support_append] at hv1
        simp only [Walk.support_cons, Walk.support_nil, List.tail_cons, List.mem_append,
          List.mem_singleton] at hv1
        rcases hv1 with hvb1 | rfl
        · exfalso
          rcases hb1_supp v hvb1 with rfl | rfl | ⟨hvH1, hvm1⟩
          · rcases hb2_supp (c 0) hv2 with heq | heq | ⟨hcH, _⟩
            · have := hc.inj (by omega) (by omega) heq; omega
            · have := hc.inj (by omega) (by omega) heq; omega
            · exact hc_not_H 0 hcH
          · rcases hb2_supp (c j1) hv2 with heq | heq | ⟨hcH, _⟩
            · exact hj1_ne_i2 (hc.inj (by omega) (by omega) heq)
            · have := hc.inj (by omega) (by omega) heq; omega
            · exact hc_not_H j1 hcH
          · rcases hb2_supp v hv2 with rfl | rfl | ⟨hvH2, hvm2⟩
            · exact hc_not_H i2 hvH1
            · exact hc_not_H 4 hvH1
            · have heq_sub : (⟨v, hvH2⟩ : {w : V // w ∈ (H : Set V)}) = ⟨v, hvH1⟩ :=
                Subtype.ext rfl
              exact hno_w ⟨v, hvH1⟩ hvm1 (heq_sub ▸ hvm2)
        · rfl
      have h4m_eq : c (4 + (m - 4)) = c 0 := by
        have h1 : 4 + (m - 4) = 0 + m := by omega
        rw [h1, hc.per]
      set a0 : G.Walk (c 4) (c (4 + (m - 4))) := cArc hc 4 (m - 4)
      have ha0_path : a0.IsPath := cArc_isPath hc 4 (by omega)
      set Q : G.Walk (c 0) (c 4) := (a0.copy rfl h4m_eq).reverse
      have hQ_path : Q.IsPath := ((Walk.isPath_copy _ _ _).mpr ha0_path).reverse
      have hc0_ne_c4 : c 0 ≠ c 4 := fun heq ↦ by
        have := hc.inj (by omega) (by omega) heq; omega
      apply cycle_of_two_paths_mod3 hc0_ne_c4 hP_path hQ_path
      · intro v hvP hvQ
        rw [Walk.support_reverse, List.mem_reverse, Walk.support_copy, mem_cArc_support] at hvQ
        rcases hvQ with ⟨t, htm4, rfl⟩
        by_cases ht0 : t = 0
        · subst ht0; exact Or.inr rfl
        · by_cases htm : t = m - 4
          · subst htm; exact Or.inl h4m_eq
          · exfalso
            have h4t_lt : 4 + t < m := by omega
            simp only [P, Walk.support_append, Walk.support_cons, Walk.support_nil, List.tail_cons,
              List.mem_append, List.mem_singleton] at hvP
            rcases hvP with (hvb1 | heq_i2) | hvb2
            · rcases hb1_supp (c (4 + t)) hvb1 with heq | heq | ⟨hcH, _⟩
              · have := hc.inj h4t_lt (by omega) heq; omega
              · have := hc.inj h4t_lt (by omega) heq; omega
              · exact hc_not_H (4 + t) hcH
            · have := hc.inj h4t_lt (by omega) heq_i2; omega
            · rcases hb2_supp (c (4 + t)) (List.mem_of_mem_tail hvb2) with heq | heq | ⟨hcH, _⟩
              · have := hc.inj h4t_lt (by omega) heq; omega
              · have := hc.inj h4t_lt (by omega) heq; omega
              · exact hc_not_H (4 + t) hcH
      · simp only [P, Q, a0, Walk.length_append, Walk.length_cons, Walk.length_nil,
          Walk.length_reverse, Walk.length_copy, cArc_length, hb1_len, hb2_len]
        omega
    -- Apply `tree_helly` to the 5 diagonal paths `(0,2), (1,3), (2,4), (0,3), (1,4)`.
    let aF : Fin 5 → {w : V // w ∈ (H : Set V)} := ![u 0, u 1, u 2, u 0, u 1]
    let bF : Fin 5 → {w : V // w ∈ (H : Set V)} := ![u 2, u 3, u 4, u 3, u 4]
    have hcomm_supp : ∀ x y, ∀ w,
        w ∈ (uPath hT x y).support ↔ w ∈ (uPath hT y x).support := by
      intro x y w
      rw [← uPath_reverse hT x y, Walk.support_reverse, List.mem_reverse]
    have hinter5 : ∀ p q : Fin 5, ∃ w,
        w ∈ (uPath hT (aF p) (bF p)).support ∧ w ∈ (uPath hT (aF q) (bF q)).support := by
      have symm_pair : ∀ {x1 y1 x2 y2},
          (∃ w, w ∈ (uPath hT x1 y1).support ∧ w ∈ (uPath hT x2 y2).support) →
          ∃ w, w ∈ (uPath hT x2 y2).support ∧ w ∈ (uPath hT x1 y1).support :=
        fun ⟨w, h1, h2⟩ ↦ ⟨w, h2, h1⟩
      have p01 := inter_short 0 2 1 3 (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (hc.adj 2) (hc.adj 0) hd02 hd13
      have p12 := inter_short 1 3 2 4 (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (hc.adj 3) (hc.adj 1) hd13 hd24
      have p34 := inter_short 0 3 1 4 (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (hc.adj 3) (hc.adj 0) hd03 hd14
      have p04 := inter_long 2 1 (by omega) (by omega) (by omega) (by omega) (by omega)
        (hc.adj 1).symm hd02 hd14
      have p32 := inter_long 3 2 (by omega) (by omega) (by omega) (by omega) (by omega)
        (hc.adj 2).symm hd03 hd24
      intro p q
      fin_cases p <;> fin_cases q <;> dsimp only [aF, bF, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_fin_one]
      -- Diagonal `(p = q)` and endpoint-sharing pairs, plus the 5 non-incident pairs:
      · exact ⟨u 0, Walk.start_mem_support _, Walk.start_mem_support _⟩
      · exact p01
      · exact ⟨u 2, Walk.end_mem_support _, Walk.start_mem_support _⟩
      · exact ⟨u 0, Walk.start_mem_support _, Walk.start_mem_support _⟩
      · exact p04
      · exact symm_pair p01
      · exact ⟨u 1, Walk.start_mem_support _, Walk.start_mem_support _⟩
      · exact p12
      · exact ⟨u 3, Walk.end_mem_support _, Walk.end_mem_support _⟩
      · exact ⟨u 1, Walk.start_mem_support _, Walk.start_mem_support _⟩
      · exact ⟨u 2, Walk.start_mem_support _, Walk.end_mem_support _⟩
      · exact symm_pair p12
      · exact ⟨u 2, Walk.start_mem_support _, Walk.start_mem_support _⟩
      · exact symm_pair p32
      · exact ⟨u 4, Walk.end_mem_support _, Walk.end_mem_support _⟩
      · exact ⟨u 0, Walk.start_mem_support _, Walk.start_mem_support _⟩
      · exact ⟨u 3, Walk.end_mem_support _, Walk.end_mem_support _⟩
      · exact p32
      · exact ⟨u 0, Walk.start_mem_support _, Walk.start_mem_support _⟩
      · exact p34
      · exact symm_pair p04
      · exact ⟨u 1, Walk.start_mem_support _, Walk.start_mem_support _⟩
      · exact ⟨u 4, Walk.end_mem_support _, Walk.end_mem_support _⟩
      · exact symm_pair p34
      · exact ⟨u 1, Walk.start_mem_support _, Walk.start_mem_support _⟩
    obtain ⟨v0, hv0⟩ := tree_helly hT (u 0) (by omega) aF bF hinter5
    have hm02 : v0 ∈ (uPath hT (u 0) (u 2)).support := hv0 0
    have hm13 : v0 ∈ (uPath hT (u 1) (u 3)).support := hv0 1
    have hm24 : v0 ∈ (uPath hT (u 2) (u 4)).support := hv0 2
    have hm03 : v0 ∈ (uPath hT (u 0) (u 3)).support := hv0 3
    have hm14 : v0 ∈ (uPath hT (u 1) (u 4)).support := hv0 4
    have hs02 := tDist_split hT hm02
    have hs13 := tDist_split hT hm13
    have hs24 := tDist_split hT hm24
    have hs03 := tDist_split hT hm03
    have hs14 := tDist_split hT hm14
    rw [tDist_comm hT (u 0) v0] at hs02 hs03
    rw [tDist_comm hT (u 1) v0] at hs13 hs14
    rw [tDist_comm hT (u 2) v0] at hs24
    rcases uPath_support_triangle hT (u 0) (u 1) (u 2) hm02 with hm01 | hm12
    · have hs01 := tDist_split hT hm01
      rw [tDist_comm hT (u 0) v0] at hs01
      omega
    · have hs12 := tDist_split hT hm12
      rw [tDist_comm hT (u 1) v0] at hs12
      omega

/- ### Section 4: Chen-Saito one-deficient theorem and main proof -/

def wVert {V : Type*} {G : SimpleGraph V} : ∀ {u v : V}, G.Walk u v → ℕ → V
  | u, _, .nil, _ => u
  | u, _, .cons _ _, 0 => u
  | _, _, .cons _ rest, k + 1 => wVert rest k

@[simp]
lemma wVert_zero {V : Type*} {G : SimpleGraph V} {u v : V} (p : G.Walk u v) :
    wVert p 0 = u := by
  cases p <;> rfl

lemma wVert_length {V : Type*} {G : SimpleGraph V} {u v : V} (p : G.Walk u v) :
    wVert p p.length = v := by
  induction p with
  | nil => rfl
  | cons _ rest ih =>
    simp only [Walk.length_cons, wVert]
    exact ih

lemma wVert_adj_succ {V : Type*} {G : SimpleGraph V} {u v : V} (p : G.Walk u v) :
    ∀ {k : ℕ}, k < p.length → G.Adj (wVert p k) (wVert p (k + 1)) := by
  induction p with
  | nil =>
    intro k hk
    simp at hk
  | cons hadj rest ih =>
    intro k hk
    cases k with
    | zero =>
      simp only [wVert, wVert_zero]
      exact hadj
    | succ k' =>
      simp only [Walk.length_cons] at hk
      exact ih (by omega)

lemma wVert_mem_support {V : Type*} {G : SimpleGraph V} {u v : V} (p : G.Walk u v) :
    ∀ {k : ℕ}, k ≤ p.length → wVert p k ∈ p.support := by
  induction p with
  | nil =>
    intro _ _
    simp [wVert]
  | cons _ rest ih =>
    intro k hk
    cases k with
    | zero => simp [wVert]
    | succ k' =>
      simp only [Walk.length_cons] at hk
      simp only [wVert, Walk.support_cons, List.mem_cons]
      exact Or.inr (ih (by omega))

lemma wVert_mem_tail {V : Type*} {G : SimpleGraph V} {u v : V} (p : G.Walk u v) :
    ∀ {k : ℕ}, 1 ≤ k → k ≤ p.length → wVert p k ∈ p.support.tail := by
  cases p with
  | nil =>
    intro k hk1 hk2
    simp at hk2
    omega
  | cons _ rest =>
    intro k hk1 hk2
    cases k with
    | zero => omega
    | succ k' =>
      simp only [Walk.length_cons] at hk2
      simp only [wVert, Walk.support_cons, List.tail_cons]
      exact wVert_mem_support rest (by omega)

lemma mem_support_iff_wVert {V : Type*} {G : SimpleGraph V} {u v : V} (p : G.Walk u v) (w : V) :
    w ∈ p.support ↔ ∃ k ≤ p.length, wVert p k = w := by
  induction p with
  | nil =>
    simp only [Walk.support_nil, List.mem_singleton, Walk.length_nil, Nat.le_zero, exists_eq_left,
      wVert]
    exact ⟨fun h ↦ h.symm, fun h ↦ h.symm⟩
  | cons _ rest ih =>
    simp only [Walk.support_cons, List.mem_cons, Walk.length_cons, ih]
    constructor
    · rintro (rfl | ⟨k, hk, rfl⟩)
      · exact ⟨0, by omega, rfl⟩
      · exact ⟨k + 1, by omega, rfl⟩
    · rintro ⟨k, hk, rfl⟩
      cases k with
      | zero => exact Or.inl rfl
      | succ k' => exact Or.inr ⟨k', by omega, rfl⟩

lemma nodup_tail_wVert_inj {V : Type*} {G : SimpleGraph V} {u v : V} {p : G.Walk u v}
    (hnd : p.support.tail.Nodup) :
    ∀ {i j : ℕ}, 1 ≤ i → i ≤ p.length → 1 ≤ j → j ≤ p.length →
      wVert p i = wVert p j → i = j := by
  induction p with
  | nil =>
    intro i _ hi1 hi2
    simp at hi2
    omega
  | @cons a b c _ rest ih =>
    simp only [Walk.support_cons, List.tail_cons, Walk.length_cons] at hnd ⊢
    rw [support_eq_cons_tail rest, List.nodup_cons] at hnd
    intro i j hi1 hi2 hj1 hj2 heq
    cases i with
    | zero => omega
    | succ i' =>
      cases j with
      | zero => omega
      | succ j' =>
        simp only [wVert] at heq
        cases i' with
        | zero =>
          cases j' with
          | zero => rfl
          | succ j'' =>
            exfalso
            rw [wVert_zero] at heq
            have hv := wVert_mem_tail rest (k := j'' + 1) (by omega) (by omega)
            rw [← heq] at hv
            exact hnd.1 hv
        | succ i'' =>
          cases j' with
          | zero =>
            exfalso
            rw [wVert_zero] at heq
            have hv := wVert_mem_tail rest (k := i'' + 1) (by omega) (by omega)
            rw [heq] at hv
            exact hnd.1 hv
          | succ j'' =>
            exact congrArg (· + 1) (ih hnd.2 (by omega) (by omega) (by omega) (by omega) heq)

lemma isCycle_to_cyclicSeq {V : Type*} [DecidableEq V] {G : SimpleGraph V} {v0 : V}
    {C : G.Walk v0 v0} (hC : C.IsCycle) :
    let m := C.length
    let c := fun i ↦ wVert C (i % m)
    IsCyclicSeq G m c ∧
      (∀ w : V, w ∈ C.support ↔ ∃ i < m, c i = w) ∧
      C.support.toFinset = (Finset.range m).image c ∧
      C.support.toFinset.card = m := by
  set m := C.length
  set c : ℕ → V := fun i ↦ wVert C (i % m)
  have hm3 : 3 ≤ m := hC.three_le_length
  have hm_pos : 0 < m := by omega
  have hnd : C.support.tail.Nodup := hC.support_nodup
  have hinj : ∀ {i j : ℕ}, i < m → j < m → c i = c j → i = j := by
    intro i j hi hj heq
    dsimp only [c] at heq
    rw [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] at heq
    by_cases hi0 : i = 0
    · subst i
      by_cases hj0 : j = 0
      · exact hj0.symm
      · exfalso
        rw [wVert_zero] at heq
        have heq_m : wVert C m = wVert C j := (wVert_length C).trans heq
        have := nodup_tail_wVert_inj hnd (by omega) le_rfl (by omega) (by omega) heq_m
        omega
    · by_cases hj0 : j = 0
      · subst j
        exfalso
        rw [wVert_zero] at heq
        have heq_m : wVert C i = wVert C m := heq.trans (wVert_length C).symm
        have := nodup_tail_wVert_inj hnd (by omega) (by omega) (by omega) le_rfl heq_m
        omega
      · exact nodup_tail_wVert_inj hnd (by omega) (by omega) (by omega) (by omega) heq
  have hadj_c : ∀ i : ℕ, G.Adj (c i) (c (i + 1)) := by
    intro i
    dsimp only [c]
    set r := i % m
    have hr : r < m := Nat.mod_lt i hm_pos
    have hadj_r : G.Adj (wVert C r) (wVert C (r + 1)) := wVert_adj_succ C hr
    have hdiv := Nat.div_add_mod i m
    by_cases hrm : r + 1 < m
    · have hmod1 : (i + 1) % m = r + 1 := by
        have heq_i : i + 1 = (r + 1) + m * (i / m) := by omega
        rw [heq_i, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hrm]
      rwa [hmod1]
    · have hrm_eq : r + 1 = m := by omega
      have hmod0 : (i + 1) % m = 0 := by
        have heq_i : i + 1 = m * (i / m + 1) := by
          have : m * (i / m + 1) = m * (i / m) + m := by ring
          omega
        rw [heq_i, Nat.mul_mod_right]
      rw [hmod0, wVert_zero]
      rw [hrm_eq] at hadj_r
      change G.Adj (wVert C r) (wVert C C.length) at hadj_r
      rwa [wVert_length C] at hadj_r
  have hc : IsCyclicSeq G m c :=
    { three_le := hm3
      per := fun i ↦ by dsimp only [c]; rw [Nat.add_mod_right]
      adj := hadj_c
      inj := hinj }
  have hsupp : ∀ w : V, w ∈ C.support ↔ ∃ i < m, c i = w := by
    intro w
    rw [mem_support_iff_wVert]
    constructor
    · rintro ⟨k, hkm, rfl⟩
      by_cases hlt : k < m
      · refine ⟨k, hlt, ?_⟩
        dsimp only [c]
        rw [Nat.mod_eq_of_lt hlt]
      · have hkeq : k = m := by omega
        subst k
        refine ⟨0, hm_pos, ?_⟩
        dsimp only [c]
        rw [Nat.zero_mod, wVert_zero, wVert_length]
    · rintro ⟨i, him, rfl⟩
      refine ⟨i, le_of_lt him, ?_⟩
      dsimp only [c]
      rw [Nat.mod_eq_of_lt him]
  have hfin : C.support.toFinset = (Finset.range m).image c := by
    ext w
    rw [List.mem_toFinset, hsupp, Finset.mem_image]
    simp only [Finset.mem_range]
  have hcard : C.support.toFinset.card = m := by
    rw [hfin, Finset.card_image_of_injOn, Finset.card_range]
    intro i hi j hj heq
    exact hinj (Finset.mem_coe.mp hi |> Finset.mem_range.mp)
      (Finset.mem_coe.mp hj |> Finset.mem_range.mp) heq
  exact ⟨hc, hsupp, hfin, hcard⟩

lemma cycle_of_path_and_edge {V : Type*} {G : SimpleGraph V} {a b : V}
    {p : G.Walk a b} (hp : p.IsPath) (hlen : 2 ≤ p.length) (hadj : G.Adj a b) :
    ∃ C : G.Walk a a, C.IsCycle ∧ C.length = p.length + 1 ∧
      ∀ v ∈ C.support, v ∈ p.support := by
  set e : G.Walk a b := .cons hadj .nil
  have he : e.IsPath := Walk.IsPath.cons Walk.IsPath.nil
    (by simp only [Walk.support_nil, List.mem_singleton]; exact G.ne_of_adj hadj)
  have hdisj : p.support.tail.Disjoint e.reverse.support.tail := by
    rw [List.disjoint_left]
    intro t htp hte
    have hte_rev : t ∈ e.reverse.support.tail := hte
    have h_eq_rev : e.reverse.support = [b, a] := by
      rw [Walk.support_reverse]
      simp [e]
    rw [h_eq_rev] at hte_rev
    simp only [List.tail_cons, List.mem_singleton] at hte_rev
    have hnd := hp.support_nodup
    rw [support_eq_cons_tail p, List.nodup_cons] at hnd
    exact hnd.1 (hte_rev ▸ htp)
  refine ⟨p.append e.reverse, hp.isCycle_append he.reverse hdisj (Or.inl (by omega)), ?_, ?_⟩
  · simp [e, Walk.length_append]
  · intro v hv
    rw [Walk.support_append] at hv
    rcases List.mem_append.mp hv with hv1 | hv2
    · exact hv1
    · have h_eq_rev : e.reverse.support = [b, a] := by
        rw [Walk.support_reverse]
        simp [e]
      rw [h_eq_rev] at hv2
      simp only [List.tail_cons, List.mem_singleton] at hv2
      rw [hv2]
      exact Walk.start_mem_support p

lemma exists_cycle_of_deg_ge_two {U : Type*} [Fintype U] [DecidableEq U] [Nonempty U]
    (H : SimpleGraph U) [DecidableRel H.Adj] (hdeg : ∀ u : U, 2 ≤ H.degree u) :
    ∃ (v : U) (C : H.Walk v v), C.IsCycle := by
  classical
  have hcard_pos : 0 < Fintype.card U := Fintype.card_pos
  have path_lt : ∀ {a b : U} {p : H.Walk a b}, p.IsPath → p.length < Fintype.card U := by
    intro a b p hp
    have hle := hp.support_nodup.length_le_card
    rw [Walk.length_support] at hle
    omega
  set S : Finset ℕ := (Finset.range (Fintype.card U)).filter
    (fun k ↦ ∃ (a b : U) (p : H.Walk a b), p.IsPath ∧ p.length = k)
  have h0S : 0 ∈ S := by
    obtain ⟨u0⟩ := ‹Nonempty U›
    simp only [S, Finset.mem_filter, Finset.mem_range]
    exact ⟨hcard_pos, u0, u0, .nil, Walk.IsPath.nil, rfl⟩
  set L := S.max' ⟨0, h0S⟩
  have hLS : L ∈ S := S.max'_mem ⟨0, h0S⟩
  simp only [S, Finset.mem_filter, Finset.mem_range] at hLS
  rcases hLS with ⟨_, a, b, p, hp, hpL⟩
  have hnb_sub : ∀ w ∈ H.neighborFinset a, w ∈ p.support := by
    intro w hw
    by_contra hnot
    have hadj_aw : H.Adj a w := (H.mem_neighborFinset _ _).mp hw
    set p' : H.Walk w b := .cons hadj_aw.symm p
    have hp'_path : p'.IsPath := Walk.IsPath.cons hp hnot
    have hL1_mem : L + 1 ∈ S := by
      simp only [S, Finset.mem_filter, Finset.mem_range]
      exact ⟨by simpa [p', hpL] using path_lt hp'_path, w, b, p', hp'_path, by simp [p', hpL]⟩
    have hle_max : L + 1 ≤ L := S.le_max' (L + 1) hL1_mem
    omega
  have hnb_card : 2 ≤ (H.neighborFinset a).card := by
    rw [card_neighborFinset_eq_degree]
    exact hdeg a
  cases p with
  | nil =>
    obtain ⟨w, hw⟩ := Finset.card_pos.mp (by omega : 0 < (H.neighborFinset a).card)
    have hwa : w = a := by simpa using hnb_sub w hw
    exact (H.ne_of_adj ((H.mem_neighborFinset _ _).mp hw) hwa.symm).elim
  | @cons _ a1 _ hadj_a1 rest =>
    obtain ⟨w, hw_nb, hwa1⟩ := Finset.exists_mem_ne hnb_card a1
    have hadj_aw : H.Adj a w := (H.mem_neighborFinset _ _).mp hw_nb
    have hw_supp : w ∈ (Walk.cons hadj_a1 rest).support := hnb_sub w hw_nb
    set q := (Walk.cons hadj_a1 rest).takeUntil w hw_supp
    have hq_path : q.IsPath := hp.takeUntil hw_supp
    have hq_ge1 : 1 ≤ q.length := one_le_length_of_ne (H.ne_of_adj hadj_aw) q
    have hq_ge2 : 2 ≤ q.length := by
      by_contra hlt2
      have hq1 : q.length = 1 := by omega
      have hspec := Walk.take_spec (Walk.cons hadj_a1 rest) hw_supp
      change q.append _ = Walk.cons hadj_a1 rest at hspec
      have hw1 := congrArg (fun x ↦ wVert x 1) hspec
      have h_rhs : wVert (Walk.cons hadj_a1 rest) 1 = a1 := wVert_zero rest
      have walk_len1 : ∀ {x y : U} (w1 : H.Walk x y) (w2 : H.Walk y b),
          w1.length = 1 → wVert (w1.append w2) 1 = y := by
        intro x y w1 w2 hw_len
        cases w1 with
        | nil => cases hw_len
        | @cons _ _ _ _ q_tl =>
          cases q_tl with
          | nil => exact wVert_zero w2
          | cons _ _ => cases hw_len
      have h_lhs : wVert (q.append ((Walk.cons hadj_a1 rest).dropUntil w hw_supp)) 1 = w :=
        walk_len1 q _ hq1
      exact hwa1 (h_lhs.symm.trans (hw1.trans h_rhs))
    obtain ⟨C, hC, _, _⟩ := cycle_of_path_and_edge hq_path hq_ge2 hadj_aw
    exact ⟨a, C, hC⟩

lemma two_paths_across_comp {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    [DecidableRel G.Adj] {r u v q0 w_out : V}
    (h2G : IsTwoConn G) (hdeg : ∀ w : V, w ≠ r → 3 ≤ G.degree w)
    (huv : u ≠ v)
    (hq0 : q0 ∈ Finset.univ \ ({u, v} : Finset V))
    (hQ_card : 2 ≤ (compIn G (Finset.univ \ ({u, v} : Finset V)) q0).card)
    (hw_out_Q : w_out ∉ compIn G (Finset.univ \ ({u, v} : Finset V)) q0)
    (hw_out_u : w_out ≠ u) (hw_out_v : w_out ≠ v) :
    let Q := compIn G (Finset.univ \ ({u, v} : Finset V)) q0
    ∃ (p1 p2 : G.Walk u v), p1.IsPath ∧ p2.IsPath ∧ p1.length % 3 ≠ p2.length % 3 ∧
      (∀ t ∈ p1.support, t ∈ Q ∨ t = u ∨ t = v) ∧
      (∀ t ∈ p2.support, t ∈ Q ∨ t = u ∨ t = v) := by
  set U := Finset.univ \ ({u, v} : Finset V)
  set Q := compIn G U q0
  have hq0Q : q0 ∈ Q := self_mem_compIn hq0
  have hu_not_Q : u ∉ Q := fun hm ↦ by
    have h := compIn_subset hm; simp [U] at h
  have hv_not_Q : v ∉ Q := fun hm ↦ by
    have h := compIn_subset hm; simp [U] at h
  -- Both `u` and `v` have neighbors in `Q` since `IsTwoConn G` and `w_out ∉ Q ∪ {u, v}`.
  have hex_u : ∃ qu ∈ Q, G.Adj u qu := by
    have hq0_ne_v : q0 ≠ v := fun h ↦ hv_not_Q (h ▸ hq0Q)
    obtain ⟨p, hp⟩ := (reachable_induce_iff (U := {t : V | t ≠ v}) hq0_ne_v hw_out_v).mp
      ((h2G.2 v) ⟨q0, hq0_ne_v⟩ ⟨w_out, hw_out_v⟩)
    obtain ⟨qu, hquQ, z_ex, hz_exQ, hadj_qz, hz_supp, _⟩ := first_exit Q hq0Q hw_out_Q p
    have hz_ne_v : z_ex ≠ v := hp z_ex hz_supp
    have hz_eq_u : z_ex = u := by
      by_contra hneu
      have hzU : z_ex ∈ U := by simp [U, hneu, hz_ne_v]
      exact compIn_no_edge_out hquQ hzU hz_exQ hadj_qz
    rw [hz_eq_u] at hadj_qz
    exact ⟨qu, hquQ, hadj_qz.symm⟩
  have hex_v : ∃ qv ∈ Q, G.Adj v qv := by
    have hq0_ne_u : q0 ≠ u := fun h ↦ hu_not_Q (h ▸ hq0Q)
    obtain ⟨p, hp⟩ := (reachable_induce_iff (U := {t : V | t ≠ u}) hq0_ne_u hw_out_u).mp
      ((h2G.2 u) ⟨q0, hq0_ne_u⟩ ⟨w_out, hw_out_u⟩)
    obtain ⟨qv, hqvQ, z_ex, hz_exQ, hadj_qz, hz_supp, _⟩ := first_exit Q hq0Q hw_out_Q p
    have hz_ne_u : z_ex ≠ u := hp z_ex hz_supp
    have hz_eq_v : z_ex = v := by
      by_contra hnev
      have hzU : z_ex ∈ U := by simp [U, hz_ne_u, hnev]
      exact compIn_no_edge_out hqvQ hzU hz_exQ hadj_qz
    rw [hz_eq_v] at hadj_qz
    exact ⟨qv, hqvQ, hadj_qz.symm⟩
  rcases hex_u with ⟨qu, hquQ, hadj_u_qu⟩
  rcases hex_v with ⟨qv, hqvQ, hadj_v_qv⟩
  set SQ := Q ∪ ({u, v} : Finset V)
  set GQ := G.induce (SQ : Set V)
  set uQ : {w : V // w ∈ (SQ : Set V)} := ⟨u, by simp [SQ]⟩
  set vQ : {w : V // w ∈ (SQ : Set V)} := ⟨v, by simp [SQ]⟩
  set zQ : {w : V // w ∈ (SQ : Set V)} :=
    if hrSQ : r ∈ (SQ : Set V) then ⟨r, hrSQ⟩ else uQ
  have huvQ : uQ ≠ vQ := fun heq ↦ huv (Subtype.mk.inj heq)
  have hcard_SQ : 4 ≤ Fintype.card (SQ : Set V) := by
    have hc_eq : Fintype.card (SQ : Set V) = SQ.card := by
      convert Fintype.card_coe SQ
      exact Finset.mem_coe
    have hdisj_Q_uv : Disjoint Q ({u, v} : Finset V) := by
      simp [Finset.disjoint_insert_right, hu_not_Q, hv_not_Q]
    have hcard_u : SQ.card = Q.card + 2 := by
      rw [Finset.card_union_of_disjoint hdisj_Q_uv, Finset.card_pair huv]
    omega
  have h2GQ : IsTwoConn (addEdge GQ uQ vQ) := by
    set KQ := addEdge GQ uQ vQ
    have hadj_uvQ : KQ.Adj uQ vQ := addEdge_adj_self GQ huvQ
    have hQ_conn := connected_induce_compIn (G := G) hq0
    have hcut_uQ : (KQ.induce {t | t ≠ uQ}).Connected := by
      apply connected_induce_of_base vQ huvQ.symm
      intro t ht
      by_cases htv : t = vQ
      · subst htv; exact Reachable.refl _
      · have htQ : t.1 ∈ Q := by
          have hm : t.1 ∈ SQ := t.2
          simp only [SQ, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hm
          rcases hm with hm | h_eq | h_eq
          · exact hm
          · exact (ht (Subtype.ext h_eq)).elim
          · exact (htv (Subtype.ext h_eq)).elim
        obtain ⟨p⟩ := hQ_conn.preconnected ⟨qv, hqvQ⟩ ⟨t.1, htQ⟩
        let mapQ : ∀ {x1 x2 : {w : V // w ∈ (Q : Set V)}}
            (wlk : (G.induce (Q : Set V)).Walk x1 x2),
            (KQ.induce {z | z ≠ uQ}).Walk
              ⟨⟨x1.1, Finset.mem_coe.mpr (Finset.mem_union_left _ x1.2)⟩,
                fun heq ↦ hu_not_Q (Subtype.mk.inj heq ▸ x1.2)⟩
              ⟨⟨x2.1, Finset.mem_coe.mpr (Finset.mem_union_left _ x2.2)⟩,
                fun heq ↦ hu_not_Q (Subtype.mk.inj heq ▸ x2.2)⟩ := by
          intro x1 x2 wlk
          induction wlk with
          | nil => exact .nil
          | @cons y1 y2 _ hadj tl ihtl =>
            have hadj' : (KQ.induce {z | z ≠ uQ}).Adj
                ⟨⟨y1.1, Finset.mem_coe.mpr (Finset.mem_union_left _ y1.2)⟩,
                  fun heq ↦ hu_not_Q (Subtype.mk.inj heq ▸ y1.2)⟩
                ⟨⟨y2.1, Finset.mem_coe.mpr (Finset.mem_union_left _ y2.2)⟩,
                  fun heq ↦ hu_not_Q (Subtype.mk.inj heq ▸ y2.2)⟩ :=
              Or.inl (induce_adj_val hadj)
            exact .cons hadj' ihtl
        have hqv_ne : (⟨qv, Finset.mem_coe.mpr (Finset.mem_union_left _ hqvQ)⟩ :
            {w : V // w ∈ (SQ : Set V)}) ≠ uQ :=
          fun heq ↦ hu_not_Q (Subtype.mk.inj heq ▸ hqvQ)
        have hadj_v_qvQ : (KQ.induce {z | z ≠ uQ}).Adj ⟨vQ, huvQ.symm⟩ ⟨_, hqv_ne⟩ :=
          Or.inl hadj_v_qv
        exact hadj_v_qvQ.reachable.trans ⟨mapQ p⟩
    have hcut_vQ : (KQ.induce {t | t ≠ vQ}).Connected := by
      apply connected_induce_of_base uQ huvQ
      intro t ht
      by_cases htu : t = uQ
      · subst htu; exact Reachable.refl _
      · have htQ : t.1 ∈ Q := by
          have hm : t.1 ∈ SQ := t.2
          simp only [SQ, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hm
          rcases hm with hm | h_eq | h_eq
          · exact hm
          · exact (htu (Subtype.ext h_eq)).elim
          · exact (ht (Subtype.ext h_eq)).elim
        obtain ⟨p⟩ := hQ_conn.preconnected ⟨qu, hquQ⟩ ⟨t.1, htQ⟩
        let mapQ : ∀ {x1 x2 : {w : V // w ∈ (Q : Set V)}}
            (wlk : (G.induce (Q : Set V)).Walk x1 x2),
            (KQ.induce {z | z ≠ vQ}).Walk
              ⟨⟨x1.1, Finset.mem_coe.mpr (Finset.mem_union_left _ x1.2)⟩,
                fun heq ↦ hv_not_Q (Subtype.mk.inj heq ▸ x1.2)⟩
              ⟨⟨x2.1, Finset.mem_coe.mpr (Finset.mem_union_left _ x2.2)⟩,
                fun heq ↦ hv_not_Q (Subtype.mk.inj heq ▸ x2.2)⟩ := by
          intro x1 x2 wlk
          induction wlk with
          | nil => exact .nil
          | @cons y1 y2 _ hadj tl ihtl =>
            have hadj' : (KQ.induce {z | z ≠ vQ}).Adj
                ⟨⟨y1.1, Finset.mem_coe.mpr (Finset.mem_union_left _ y1.2)⟩,
                  fun heq ↦ hv_not_Q (Subtype.mk.inj heq ▸ y1.2)⟩
                ⟨⟨y2.1, Finset.mem_coe.mpr (Finset.mem_union_left _ y2.2)⟩,
                  fun heq ↦ hv_not_Q (Subtype.mk.inj heq ▸ y2.2)⟩ :=
              Or.inl (induce_adj_val hadj)
            exact .cons hadj' ihtl
        have hqu_ne : (⟨qu, Finset.mem_coe.mpr (Finset.mem_union_left _ hquQ)⟩ :
            {w : V // w ∈ (SQ : Set V)}) ≠ vQ :=
          fun heq ↦ hv_not_Q (Subtype.mk.inj heq ▸ hquQ)
        have hadj_u_quQ : (KQ.induce {z | z ≠ vQ}).Adj ⟨uQ, huvQ⟩ ⟨_, hqu_ne⟩ :=
          Or.inl hadj_u_qu
        exact hadj_u_quQ.reachable.trans ⟨mapQ p⟩
    refine ⟨?_, fun c ↦ ?_⟩
    · have hr0 : ∀ t, KQ.Reachable uQ t := by
        intro t
        by_cases htv : t = vQ
        · subst htv; exact hadj_uvQ.reachable
        · obtain ⟨p⟩ := hcut_vQ ⟨uQ, huvQ⟩ ⟨t, htv⟩
          exact ⟨liftWalk p⟩
      exact @Connected.mk _ KQ (fun t1 t2 ↦ (hr0 t1).symm.trans (hr0 t2)) ⟨uQ⟩
    · by_cases hcu : c = uQ
      · subst hcu; exact hcut_uQ
      · by_cases hcv : c = vQ
        · subst hcv; exact hcut_vQ
        · have hcQ : c.1 ∈ Q := by
            have hm : c.1 ∈ SQ := c.2
            simp only [SQ, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hm
            rcases hm with hm | h_eq | h_eq
            · exact hm
            · exact (hcu (Subtype.ext h_eq)).elim
            · exact (hcv (Subtype.ext h_eq)).elim
          have hu_ne_c : uQ ≠ c := Ne.symm hcu
          have hv_ne_c : vQ ≠ c := Ne.symm hcv
          have hadj_uv_sub : (KQ.induce {t | t ≠ c}).Adj ⟨uQ, hu_ne_c⟩ ⟨vQ, hv_ne_c⟩ :=
            hadj_uvQ
          apply connected_induce_of_base uQ hu_ne_c
          intro t ht
          by_cases htu : t = uQ
          · subst htu; exact Reachable.refl _
          · by_cases htv : t = vQ
            · subst htv; exact hadj_uv_sub.reachable
            · have htQ : t.1 ∈ Q := by
                have hm : t.1 ∈ SQ := t.2
                simp only [SQ, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hm
                rcases hm with hm | h_eq | h_eq
                · exact hm
                · exact (htu (Subtype.ext h_eq)).elim
                · exact (htv (Subtype.ext h_eq)).elim
              have htc1 : t.1 ≠ c.1 := fun heq ↦ ht (Subtype.ext heq)
              have hwc1 : w_out ≠ c.1 := fun h ↦ hw_out_Q (h ▸ hcQ)
              obtain ⟨p, hp⟩ := (reachable_induce_iff (U := {w : V | w ≠ c.1})
                htc1 hwc1).mp ((h2G.2 c.1) ⟨t.1, htc1⟩ ⟨w_out, hwc1⟩)
              obtain ⟨q', hq'Q, w_ex, hw_exQ, hadj_qw, _, r_wk, hr_wk⟩ :=
                first_exit Q htQ hw_out_Q p
              have hw_uv : w_ex = u ∨ w_ex = v := by
                by_contra hnot
                push Not at hnot
                have hwU : w_ex ∈ U := by simp [U, hnot.1, hnot.2]
                exact compIn_no_edge_out hq'Q hwU hw_exQ hadj_qw
              have hq'_sub : (⟨q', Finset.mem_coe.mpr (Finset.mem_union_left _ hq'Q)⟩ :
                  {w : V // w ∈ (SQ : Set V)}) ≠ c := by
                intro heq
                exact hp q' (hr_wk q' (Walk.end_mem_support r_wk)).2 (Subtype.mk.inj heq)
              have liftToKQ : ∀ {x1 x2 : V} (hx1 : x1 ∈ Q) (hx2 : x2 ∈ Q)
                  (h1c : (⟨x1, Finset.mem_coe.mpr (Finset.mem_union_left _ hx1)⟩ :
                    {w : V // w ∈ (SQ : Set V)}) ≠ c)
                  (h2c : (⟨x2, Finset.mem_coe.mpr (Finset.mem_union_left _ hx2)⟩ :
                    {w : V // w ∈ (SQ : Set V)}) ≠ c)
                  (wlk : G.Walk x1 x2),
                  (∀ s ∈ wlk.support, ∃ hs : s ∈ Q,
                    (⟨s, Finset.mem_coe.mpr (Finset.mem_union_left _ hs)⟩ :
                      {w : V // w ∈ (SQ : Set V)}) ≠ c) →
                  (KQ.induce {z | z ≠ c}).Reachable ⟨_, h1c⟩ ⟨_, h2c⟩ := by
                intro x1 x2 hx1 hx2 h1c h2c wlk
                induction wlk with
                | nil => intro _; exact Reachable.refl _
                | @cons s1 s2 _ hadj_s tl ihtl =>
                  intro hmem
                  obtain ⟨hs2Q, hs2c⟩ := hmem s2 (by simp)
                  have hadj_KQ : (KQ.induce {z | z ≠ c}).Adj ⟨_, h1c⟩ ⟨_, hs2c⟩ :=
                    Or.inl hadj_s
                  exact hadj_KQ.reachable.trans
                    (ihtl hs2Q hx2 hs2c h2c (fun s hs ↦ hmem s (by simp [hs])))
              have hr_KQ : (KQ.induce {z | z ≠ c}).Reachable ⟨t, ht⟩ ⟨_, hq'_sub⟩ := by
                have ht_eq : (⟨t.1, Finset.mem_coe.mpr (Finset.mem_union_left _ htQ)⟩ :
                    {w : V // w ∈ (SQ : Set V)}) = t := Subtype.ext rfl
                have hr0_KQ := liftToKQ htQ hq'Q (ht_eq.symm ▸ ht) hq'_sub r_wk
                  (fun s hs ↦ ⟨(hr_wk s hs).1,
                    fun heq ↦ hp s (hr_wk s hs).2 (Subtype.mk.inj heq)⟩)
                convert hr0_KQ
              rcases hw_uv with hwu | hwv
              · rw [hwu] at hadj_qw
                have hadj_uq : (KQ.induce {z | z ≠ c}).Adj ⟨uQ, hu_ne_c⟩ ⟨_, hq'_sub⟩ :=
                  Or.inl hadj_qw.symm
                exact hadj_uq.reachable.trans hr_KQ.symm
              · rw [hwv] at hadj_qw
                have hadj_vq : (KQ.induce {z | z ≠ c}).Adj ⟨vQ, hv_ne_c⟩ ⟨_, hq'_sub⟩ :=
                  Or.inl hadj_qw.symm
                exact hadj_uv_sub.reachable.trans (hadj_vq.reachable.trans hr_KQ.symm)
  have hdegGQ : ∀ w : {x : V // x ∈ (SQ : Set V)},
      w ≠ uQ → w ≠ vQ → w ≠ zQ → 3 ≤ GQ.degree w := by
    intro w hwu hwv hwz
    have hwQ : w.1 ∈ Q := by
      have hm : w.1 ∈ SQ := w.2
      simp only [SQ, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hm
      rcases hm with hm | h_eq | h_eq
      · exact hm
      · exact (hwu (Subtype.ext h_eq)).elim
      · exact (hwv (Subtype.ext h_eq)).elim
    have hw_eq : (⟨w.1, Finset.mem_coe.mpr (Finset.mem_union_left _ hwQ)⟩ :
        {x : V // x ∈ (SQ : Set V)}) = w := Subtype.ext rfl
    rw [← hw_eq, degree_induce_compIn_union hwQ]
    · apply hdeg w.1
      intro hwr
      apply hwz
      dsimp only [zQ]
      rw [dif_pos (hwr ▸ w.2)]
      exact Subtype.ext hwr
    · intro t ht
      simp only [U, Finset.mem_sdiff, Finset.mem_univ, true_and, not_not] at ht
      exact ht
  obtain ⟨q1, q2, hq1_path, hq2_path, hq_mod⟩ :=
    two_paths_mod3_z _ GQ uQ vQ zQ le_rfl hcard_SQ huvQ h2GQ hdegGQ
  have supp_lift : ∀ (qi : GQ.Walk uQ vQ),
      ∀ t ∈ (liftWalk qi).support, t ∈ Q ∨ t = u ∨ t = v := by
    intro qi t ht
    have htSQ : t ∈ SQ := Finset.mem_coe.mp (support_liftWalk_subset qi t ht)
    simp only [SQ, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at htSQ
    exact htSQ
  refine ⟨liftWalk q1, liftWalk q2, isPath_liftWalk hq1_path, isPath_liftWalk hq2_path, ?_,
    supp_lift q1, supp_lift q2⟩
  simpa using hq_mod

lemma no_two_large_comps {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    [DecidableRel G.Adj] {r u v q1 q2 : V}
    (hno_mod3 : ¬ HasMod3Cycle G)
    (h2G : IsTwoConn G) (hdeg : ∀ w : V, w ≠ r → 3 ≤ G.degree w)
    (huv : u ≠ v)
    (hq1 : q1 ∈ Finset.univ \ ({u, v} : Finset V))
    (hq2 : q2 ∈ Finset.univ \ ({u, v} : Finset V))
    (hdisj : Disjoint (compIn G (Finset.univ \ ({u, v} : Finset V)) q1)
                      (compIn G (Finset.univ \ ({u, v} : Finset V)) q2))
    (hcard1 : 2 ≤ (compIn G (Finset.univ \ ({u, v} : Finset V)) q1).card)
    (hcard2 : 2 ≤ (compIn G (Finset.univ \ ({u, v} : Finset V)) q2).card) :
    False := by
  set U := Finset.univ \ ({u, v} : Finset V)
  set Q1 := compIn G U q1
  set Q2 := compIn G U q2
  have hq1_Q1 : q1 ∈ Q1 := self_mem_compIn hq1
  have hq2_Q2 : q2 ∈ Q2 := self_mem_compIn hq2
  have hq2_not_Q1 : q2 ∉ Q1 := Finset.disjoint_right.mp hdisj hq2_Q2
  have hq1_not_Q2 : q1 ∉ Q2 := Finset.disjoint_left.mp hdisj hq1_Q1
  have hq1_uv : q1 ≠ u ∧ q1 ≠ v := by
    simp only [U, Finset.mem_sdiff, Finset.mem_univ, Finset.mem_insert,
      Finset.mem_singleton, true_and, not_or] at hq1
    exact hq1
  have hq2_uv : q2 ≠ u ∧ q2 ≠ v := by
    simp only [U, Finset.mem_sdiff, Finset.mem_univ, Finset.mem_insert,
      Finset.mem_singleton, true_and, not_or] at hq2
    exact hq2
  obtain ⟨p1, p2, hp1, hp2, hp_mod, hp1_s, hp2_s⟩ :=
    two_paths_across_comp h2G hdeg huv hq1 hcard1 hq2_not_Q1 hq2_uv.1 hq2_uv.2
  obtain ⟨r1, r2, hr1, hr2, hr_mod, hr1_s, hr2_s⟩ :=
    two_paths_across_comp h2G hdeg huv hq2 hcard2 hq1_not_Q2 hq1_uv.1 hq1_uv.2
  have pair_disj : ∀ (pa rb : G.Walk u v),
      (∀ t ∈ pa.support, t ∈ Q1 ∨ t = u ∨ t = v) →
      (∀ t ∈ rb.support, t ∈ Q2 ∨ t = u ∨ t = v) →
      ∀ t ∈ pa.support, t ∈ rb.support → t = u ∨ t = v := by
    intro pa rb hpa hrb t h1 h2
    rcases hpa t h1 with ht1 | htu | htv
    · rcases hrb t h2 with ht2 | htu | htv
      · exact (Finset.disjoint_left.mp hdisj ht1 ht2).elim
      · exact Or.inl htu
      · exact Or.inr htv
    · exact Or.inl htu
    · exact Or.inr htv
  have hcomb : (p1.length + r1.length) % 3 = 0 ∨ (p1.length + r2.length) % 3 = 0 ∨
      (p2.length + r1.length) % 3 = 0 ∨ (p2.length + r2.length) % 3 = 0 := by omega
  rcases hcomb with h0 | h0 | h0 | h0
  · exact hno_mod3 (cycle_of_two_paths_mod3 huv hp1 hr1 (pair_disj p1 r1 hp1_s hr1_s) h0)
  · exact hno_mod3 (cycle_of_two_paths_mod3 huv hp1 hr2 (pair_disj p1 r2 hp1_s hr2_s) h0)
  · exact hno_mod3 (cycle_of_two_paths_mod3 huv hp2 hr1 (pair_disj p2 r1 hp2_s hr1_s) h0)
  · exact hno_mod3 (cycle_of_two_paths_mod3 huv hp2 hr2 (pair_disj p2 r2 hp2_s hr2_s) h0)

lemma sort_three_lt {m : ℕ} {s : Finset ℕ} (hs3 : 3 ≤ s.card) (hlt : ∀ i ∈ s, i < m) :
    ∃ i0 i1 i2 : ℕ, i0 ∈ s ∧ i1 ∈ s ∧ i2 ∈ s ∧ i0 < i1 ∧ i1 < i2 ∧ i2 < m := by
  have hne0 : s.Nonempty := Finset.card_pos.mp (by omega)
  set i0 := s.min' hne0
  have hi0 : i0 ∈ s := s.min'_mem hne0
  set s1 := s.erase i0
  have hs1_card : 2 ≤ s1.card := by rw [Finset.card_erase_of_mem hi0]; omega
  have hne1 : s1.Nonempty := Finset.card_pos.mp (by omega)
  set i1 := s1.min' hne1
  have hi1_s1 : i1 ∈ s1 := s1.min'_mem hne1
  have hi1 : i1 ∈ s := Finset.mem_of_mem_erase hi1_s1
  have hi0_lt_i1 : i0 < i1 := lt_of_le_of_ne (s.min'_le i1 hi1) (Finset.ne_of_mem_erase hi1_s1).symm
  set s2 := s1.erase i1
  have hs2_card : 1 ≤ s2.card := by rw [Finset.card_erase_of_mem hi1_s1]; omega
  have hne2 : s2.Nonempty := Finset.card_pos.mp (by omega)
  set i2 := s2.min' hne2
  have hi2_s2 : i2 ∈ s2 := s2.min'_mem hne2
  have hi2_s1 : i2 ∈ s1 := Finset.mem_of_mem_erase hi2_s2
  have hi2 : i2 ∈ s := Finset.mem_of_mem_erase hi2_s1
  have hi1_lt_i2 : i1 < i2 := lt_of_le_of_ne (s1.min'_le i2 hi2_s1) (Finset.ne_of_mem_erase hi2_s2).symm
  exact ⟨i0, i1, i2, hi0, hi1, hi2, hi0_lt_i1, hi1_lt_i2, hlt i2 hi2⟩

theorem one_deficient :
    ∀ (N : ℕ) {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
      (r : V),
      Fintype.card V = N →
      3 ≤ Fintype.card V →
      G.Connected →
      (∀ v : V, v ≠ r → 3 ≤ G.degree v) →
      HasMod3Cycle G := by
  intro N
  induction N using Nat.strongRecOn with
  | ind N ih =>
    intro V _ _ G _ r hN hcard3 hG_conn hdeg
    by_contra hno_mod3
    -- Triangle-free helper.
    have no_tri : ∀ x y z : V, G.Adj x y → G.Adj y z → ¬ G.Adj x z := by
      intro x y z hxy hyz hxz
      apply hno_mod3
      have hne_yz : y ≠ z := G.ne_of_adj hyz
      set p : G.Walk x z := .cons hxy (.cons hyz .nil)
      have hp : p.IsPath := by
        apply Walk.IsPath.cons (Walk.IsPath.cons Walk.IsPath.nil (by simp [hne_yz]))
        simp only [Walk.support_cons, Walk.support_nil, List.mem_cons,
          List.not_mem_nil, or_false, not_or]
        exact ⟨G.ne_of_adj hxy, G.ne_of_adj hxz⟩
      obtain ⟨C, hC, hC_len, _⟩ := cycle_of_path_and_edge hp (by simp [p]) hxz
      exact ⟨x, C, hC, by rw [hC_len]; simp [p]⟩
    -- Step 2.1: `5 ≤ Fintype.card V`.
    have hcard5 : 5 ≤ Fintype.card V := by
      by_contra hlt5
      -- Pick a vertex `u ≠ r`: since `3 ≤ Fintype.card V`, `u` has degree `≥ 3`, so `4 ≤ card V`!
      obtain ⟨u, _, hur⟩ : ∃ u ∈ (Finset.univ : Finset V), u ≠ r :=
        Finset.exists_mem_ne (by simp; omega) r
      have hu3 : 3 ≤ G.degree u := hdeg u hur
      have hlt_u := G.degree_lt_card_verts u
      have hcard4 : Fintype.card V = 4 := by omega
      -- Since `card V = 4` and `3 ≤ G.degree u`, `u` is adjacent to all 3 other vertices!
      -- Also pick `v ≠ r` with `v ≠ u`: `v` also has `3 ≤ G.degree v`, so `v` is adjacent to a third vertex `w`, forming triangle `u - v - w`!
      have hsub_ur : ({u, r} : Finset V).card ≤ 2 := Finset.card_le_two
      obtain ⟨v, _, hv_not⟩ := Finset.exists_mem_notMem_of_card_lt_card
        (s := {u, r}) (t := Finset.univ) (by simp [hcard4]; omega)
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hv_not
      have hv3 : 3 ≤ G.degree v := hdeg v hv_not.2
      -- Both `G.neighborFinset u` and `G.neighborFinset v` have size `3` inside `Finset.univ` of size `4`:
      -- Look at `G.neighborFinset u ∩ G.neighborFinset v`: inside `univ \ {u, v}` (size 2), `u` has `≥ 2` neighbors (`v` plus `≥ 2` others!) and `v` has `≥ 2` neighbors (`u` plus `≥ 2` others!), so they share a neighbor `w` AND `G.Adj u v`!
      have hadj_uv : G.Adj u v := by
        by_contra hnot_uv
        have hsub : G.neighborFinset u ⊆ Finset.univ \ ({u, v} : Finset V) := by
          intro t ht
          have hadj_ut := (G.mem_neighborFinset _ _).mp ht
          rw [Finset.mem_sdiff]
          refine ⟨Finset.mem_univ t, ?_⟩
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
          exact ⟨(G.ne_of_adj hadj_ut).symm, fun htv ↦ hnot_uv (htv ▸ hadj_ut)⟩
        have hc1 := Finset.card_le_card hsub
        have hc2 : (Finset.univ \ ({u, v} : Finset V)).card = 2 := by
          have hs := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ ({u, v} : Finset V))
          rw [Finset.card_univ, Finset.card_pair (Ne.symm hv_not.1), hcard4] at hs
          omega
        rw [card_neighborFinset_eq_degree] at hc1
        omega
      have hex_w : ∃ w : V, w ∈ G.neighborFinset u ∩ G.neighborFinset v := by
        by_contra hemp
        push Not at hemp
        have hdisj_nb : Disjoint (G.neighborFinset u) (G.neighborFinset v) :=
          Finset.disjoint_left.mpr (fun w hwu hwv ↦ hemp w (Finset.mem_inter.mpr ⟨hwu, hwv⟩))
        have hle_u : (G.neighborFinset u ∪ G.neighborFinset v).card ≤ Fintype.card V :=
          Finset.card_le_univ _
        rw [Finset.card_union_of_disjoint hdisj_nb, card_neighborFinset_eq_degree,
          card_neighborFinset_eq_degree] at hle_u
        omega
      rcases hex_w with ⟨w, hw⟩
      rw [Finset.mem_inter, SimpleGraph.mem_neighborFinset, SimpleGraph.mem_neighborFinset] at hw
      exact no_tri u v w hadj_uv hw.2 hw.1
    -- Step 2.2: `IsTwoConn G` (1-cut reduction using IH on a component avoiding `r`).
    have h2G : IsTwoConn G := by
      refine ⟨hG_conn, fun b ↦ ?_⟩
      by_contra hb_cut
      set Ub := Finset.univ.erase b
      have hUb_ne : Ub.Nonempty := by
        apply Finset.card_pos.mp
        rw [Finset.card_erase_of_mem (Finset.mem_univ b), Finset.card_univ]
        omega
      have hnc_Ub : ¬ (G.induce (Ub : Set V)).Connected := by
        intro hconn
        apply hb_cut
        apply connected_induce_of_base hUb_ne.choose (Finset.mem_erase.mp hUb_ne.choose_spec).1
        intro a ha
        have haUb : a ∈ Ub := Finset.mem_erase.mpr ⟨ha, Finset.mem_univ a⟩
        obtain ⟨p, hp⟩ := (reachable_induce_iff hUb_ne.choose_spec haUb).mp
          (hconn.preconnected ⟨_, hUb_ne.choose_spec⟩ ⟨a, haUb⟩)
        exact (reachable_induce_iff _ ha).mpr ⟨p, fun w hw ↦ (Finset.mem_erase.mp (hp w hw)).1⟩
      obtain ⟨u1, hu1, u2, hu2, hdisj12⟩ :=
        not_connected_induce_exists_disjoint_compIn hUb_ne hnc_Ub
      -- At least one of `compIn G Ub u1` and `compIn G Ub u2` avoids `r`!
      have hex_no_r : ∃ u0 ∈ Ub, r ∉ compIn G Ub u0 ∧
          ∃ w_other ∈ Ub, w_other ∉ compIn G Ub u0 := by
        by_cases hr1 : r ∈ compIn G Ub u1
        · refine ⟨u2, hu2, Finset.disjoint_left.mp hdisj12 hr1, u1, hu1, ?_⟩
          exact Finset.disjoint_left.mp hdisj12 (self_mem_compIn hu1)
        · refine ⟨u1, hu1, hr1, u2, hu2, ?_⟩
          exact Finset.disjoint_right.mp hdisj12 (self_mem_compIn hu2)
      rcases hex_no_r with ⟨u0, hu0, hr_not_C0, w_other, hw_other_Ub, hw_not_C0⟩
      set C0 := compIn G Ub u0
      have hu0_C0 : u0 ∈ C0 := self_mem_compIn hu0
      set S0 := C0 ∪ ({b} : Finset V)
      have hb_not_C0 : b ∉ C0 := fun hm ↦ (Finset.mem_erase.mp (compIn_subset hm)).1 rfl
      have hdeg_u0 : 3 ≤ (G.induce (S0 : Set V)).degree
          ⟨u0, Finset.mem_coe.mpr (Finset.mem_union_left _ hu0_C0)⟩ := by
        rw [degree_induce_compIn_union hu0_C0]
        · exact hdeg u0 (fun h ↦ hr_not_C0 (h ▸ hu0_C0))
        · intro w hw
          simp only [Ub, Finset.mem_sdiff, Finset.mem_univ, Finset.mem_erase,
            and_true, true_and, not_not] at hw
          exact Finset.mem_singleton.mpr hw
      have hcard_S0 : 4 ≤ Fintype.card (S0 : Set V) := by
        have hlt := (G.induce (S0 : Set V)).degree_lt_card_verts
          ⟨u0, Finset.mem_coe.mpr (Finset.mem_union_left _ hu0_C0)⟩
        omega
      have hlt_S0 : Fintype.card (S0 : Set V) < N := by
        have hc_eq : Fintype.card (S0 : Set V) = S0.card := by
          convert Fintype.card_coe S0
          exact Finset.mem_coe
        have hlt_card : S0.card < Fintype.card V := by
          apply Finset.card_lt_card
          rw [Finset.ssubset_iff_of_subset (Finset.subset_univ _)]
          refine ⟨w_other, Finset.mem_univ _, ?_⟩
          simp [S0, hw_not_C0, (Finset.mem_erase.mp hw_other_Ub).1]
        omega
      -- `G.induce S0` is connected!
      have hconn_S0 : (G.induce (S0 : Set V)).Connected := by
        obtain ⟨p_ub⟩ := hG_conn u0 b
        obtain ⟨q', hq'C0, w_ex, hw_exC0, hadj_qw, _, _, _⟩ :=
          first_exit C0 hu0_C0 hb_not_C0 p_ub
        have hw_eq_b : w_ex = b := by
          by_contra hneb
          exact compIn_no_edge_out hq'C0 (Finset.mem_erase.mpr ⟨hneb, Finset.mem_univ _⟩)
            hw_exC0 hadj_qw
        rw [hw_eq_b] at hadj_qw
        have hbS0 : b ∈ (S0 : Set V) := by simp [S0]
        apply connected_induce_of_base b hbS0
        intro a haS0
        have ha_cases : a ∈ C0 ∨ a = b := by
          have hm : a ∈ S0 := Finset.mem_coe.mp haS0
          simp only [S0, Finset.mem_union, Finset.mem_singleton] at hm
          exact hm
        rcases ha_cases with haC0 | rfl
        · have hC0_conn := connected_induce_compIn (G := G) hu0
          obtain ⟨p_qa⟩ := hC0_conn.preconnected ⟨q', hq'C0⟩ ⟨a, haC0⟩
          have hq'S0 : q' ∈ (S0 : Set V) := Finset.mem_coe.mpr (Finset.mem_union_left _ hq'C0)
          have hadj_bq : (G.induce (S0 : Set V)).Adj ⟨b, hbS0⟩ ⟨q', hq'S0⟩ := hadj_qw.symm
          have hreach_qa : (G.induce (S0 : Set V)).Reachable ⟨q', hq'S0⟩ ⟨a, haS0⟩ :=
            (reachable_induce_iff hq'S0 haS0).mpr ⟨liftWalk p_qa, fun t ht ↦
              Finset.mem_coe.mpr (Finset.mem_union_left _
                (Finset.mem_coe.mp (support_liftWalk_subset p_qa t ht)))⟩
          exact hadj_bq.reachable.trans hreach_qa
        · exact Reachable.refl _
      have hdeg_S0 : ∀ v : {w : V // w ∈ (S0 : Set V)},
          v ≠ ⟨b, by simp [S0]⟩ → 3 ≤ (G.induce (S0 : Set V)).degree v := by
        intro v hvb
        have hvC0 : v.1 ∈ C0 := by
          have hm : v.1 ∈ S0 := v.2
          simp only [S0, Finset.mem_union, Finset.mem_singleton] at hm
          rcases hm with hm | h_eq
          · exact hm
          · exact (hvb (Subtype.ext h_eq)).elim
        have hv_eq : (⟨v.1, Finset.mem_coe.mpr (Finset.mem_union_left _ hvC0)⟩ :
            {w : V // w ∈ (S0 : Set V)}) = v := Subtype.ext rfl
        rw [← hv_eq, degree_induce_compIn_union hvC0]
        · exact hdeg v.1 (fun h ↦ hr_not_C0 (h ▸ hvC0))
        · intro w hw
          simp only [Ub, Finset.mem_sdiff, Finset.mem_univ, Finset.mem_erase,
            and_true, true_and, not_not] at hw
          exact Finset.mem_singleton.mpr hw
      have hcyc_S0 := ih _ hlt_S0 (G.induce (S0 : Set V)) ⟨b, by simp [S0]⟩
        rfl (by omega) hconn_S0 hdeg_S0
      exact hno_mod3 (HasMod3Cycle.of_embedding (Embedding.induce (S0 : Set V)) hcyc_S0)
    -- Step 2.4: `G` has no `4`-cycle (maximal `K_{2, t}` + `contractTwo` + `two_paths_mod3_z`).
    have no_c4 : ¬ ∃ a1 b1 a2 b2 : V,
        a1 ≠ a2 ∧ b1 ≠ b2 ∧ G.Adj a1 b1 ∧ G.Adj b1 a2 ∧ G.Adj a2 b2 ∧ G.Adj b2 a1 := by
      rintro ⟨a1, b1, a2, b2, ha12, hb12, hab11, hba12, hab22, hba21⟩
      classical
      let IsK2t : Finset V × Finset V → Prop := fun p ↦
        p.1.card = 2 ∧ 2 ≤ p.2.card ∧ Disjoint p.1 p.2 ∧
          ∀ s ∈ p.1, ∀ t ∈ p.2, G.Adj s t
      have hinit : IsK2t ({a1, a2}, {b1, b2}) := by
        refine ⟨Finset.card_pair ha12, by rw [Finset.card_pair hb12], ?_, ?_⟩
        · rw [Finset.disjoint_left]
          intro x hxS hxT
          simp only [Finset.mem_insert, Finset.mem_singleton] at hxS hxT
          rcases hxS with rfl | rfl <;> rcases hxT with h_eq | h_eq
          · exact G.ne_of_adj hab11 h_eq
          · exact G.ne_of_adj hba21 h_eq.symm
          · exact G.ne_of_adj hba12 h_eq.symm
          · exact G.ne_of_adj hab22 h_eq
        · intro s hs t ht
          simp only [Finset.mem_insert, Finset.mem_singleton] at hs ht
          rcases hs with rfl | rfl <;> rcases ht with rfl | rfl
          · exact hab11
          · exact hba21.symm
          · exact hba12.symm
          · exact hab22
      set FK := (Finset.univ : Finset (Finset V × Finset V)).filter IsK2t
      have hFK_ne : FK.Nonempty := ⟨({a1, a2}, {b1, b2}),
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hinit⟩⟩
      obtain ⟨⟨S, T⟩, hST_mem, hST_max⟩ :=
        Finset.exists_max_image FK (fun p ↦ p.2.card) hFK_ne
      have hST : IsK2t (S, T) := (Finset.mem_filter.mp hST_mem).2
      dsimp only [IsK2t] at hST
      rcases hST with ⟨hS_card, hT_card, hdisj_ST, hadj_ST⟩
      have hmax_T : ∀ S' T' : Finset V, IsK2t (S', T') → T'.card ≤ T.card :=
        fun S' T' h' ↦ hST_max (S', T') (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h'⟩)
      obtain ⟨s1, s2, hs12, hS_eq⟩ : ∃ s1 s2 : V, s1 ≠ s2 ∧ S = {s1, s2} := by
        rcases Finset.card_eq_two.mp hS_card with ⟨x, y, hxy, heq⟩
        exact ⟨x, y, hxy, heq⟩
      have hs1S : s1 ∈ S := by rw [hS_eq]; simp
      have hs2S : s2 ∈ S := by rw [hS_eq]; simp
      have hS_indep : ∀ x ∈ S, ∀ y ∈ S, ¬ G.Adj x y := by
        intro x hx y hy hxy
        obtain ⟨t0, ht0⟩ := Finset.card_pos.mp (by omega : 0 < T.card)
        exact no_tri x y t0 hxy (hadj_ST y hy t0 ht0) (hadj_ST x hx t0 ht0)
      have hT_indep : ∀ x ∈ T, ∀ y ∈ T, ¬ G.Adj x y := by
        intro x hx y hy hxy
        exact no_tri x y s1 hxy (hadj_ST s1 hs1S y hy).symm (hadj_ST s1 hs1S x hx).symm
      -- Helper to build `w - y1 - s1 - t3 - s2 - y2 - w` (`6`-cycle) from two paths `(4 + 2 = 6)`.
      have six_cycle_T : ∀ (w y1 y2 t3 : V),
          w ∉ S ∪ T → y1 ∈ T → y2 ∈ T → t3 ∈ T →
          y1 ≠ y2 → t3 ≠ y1 → t3 ≠ y2 →
          G.Adj w y1 → G.Adj w y2 → False := by
        intro w y1 y2 t3 hwST hy1T hy2T ht3T hy12 ht31 ht32 hwy1 hwy2
        apply hno_mod3
        have hw_ne_S : ∀ s ∈ S, w ≠ s := fun s hs h ↦ hwST (h ▸ Finset.mem_union_left _ hs)
        have hw_ne_T : ∀ t ∈ T, w ≠ t := fun t ht h ↦ hwST (h ▸ Finset.mem_union_right _ ht)
        have hST_ne : ∀ s ∈ S, ∀ t ∈ T, s ≠ t :=
          fun s hs t ht h ↦ Finset.disjoint_left.mp hdisj_ST hs (h ▸ ht)
        set P1 : G.Walk w s2 :=
          .cons hwy1 (.cons (hadj_ST s1 hs1S y1 hy1T).symm
            (.cons (hadj_ST s1 hs1S t3 ht3T) (.cons (hadj_ST s2 hs2S t3 ht3T).symm .nil)))
        set P2 : G.Walk w s2 := .cons hwy2 (.cons (hadj_ST s2 hs2S y2 hy2T).symm .nil)
        have hP2 : P2.IsPath := by
          apply Walk.IsPath.cons
            (Walk.IsPath.cons Walk.IsPath.nil (by simp [(hST_ne s2 hs2S y2 hy2T).symm]))
          simp only [Walk.support_cons, Walk.support_nil, List.mem_cons,
            List.not_mem_nil, or_false, not_or]
          exact ⟨hw_ne_T y2 hy2T, hw_ne_S s2 hs2S⟩
        have hP1 : P1.IsPath := by
          have hs_a : (Walk.cons (hadj_ST s2 hs2S t3 ht3T).symm .nil).IsPath :=
            Walk.IsPath.cons Walk.IsPath.nil (by simp [(hST_ne s2 hs2S t3 ht3T).symm])
          have hs_b : (Walk.cons (hadj_ST s1 hs1S t3 ht3T)
              (.cons (hadj_ST s2 hs2S t3 ht3T).symm .nil)).IsPath := by
            apply Walk.IsPath.cons hs_a
            simp only [Walk.support_cons, Walk.support_nil, List.mem_cons,
              List.not_mem_nil, or_false, not_or]
            exact ⟨hST_ne s1 hs1S t3 ht3T, hs12⟩
          have hs_c : (Walk.cons (hadj_ST s1 hs1S y1 hy1T).symm
              (.cons (hadj_ST s1 hs1S t3 ht3T)
                (.cons (hadj_ST s2 hs2S t3 ht3T).symm .nil))).IsPath := by
            apply Walk.IsPath.cons hs_b
            simp only [Walk.support_cons, Walk.support_nil, List.mem_cons,
              List.not_mem_nil, or_false, not_or]
            exact ⟨(hST_ne s1 hs1S y1 hy1T).symm, ht31.symm, (hST_ne s2 hs2S y1 hy1T).symm⟩
          apply Walk.IsPath.cons hs_c
          simp only [Walk.support_cons, Walk.support_nil, List.mem_cons,
            List.not_mem_nil, or_false, not_or]
          exact ⟨hw_ne_T y1 hy1T, hw_ne_S s1 hs1S, hw_ne_T t3 ht3T, hw_ne_S s2 hs2S⟩
        apply cycle_of_two_paths_mod3 (hw_ne_S s2 hs2S) hP1 hP2
        · intro v hv1 hv2
          simp only [P1, Walk.support_cons, Walk.support_nil, List.mem_cons,
            List.not_mem_nil, or_false] at hv1
          simp only [P2, Walk.support_cons, Walk.support_nil, List.mem_cons,
            List.not_mem_nil, or_false] at hv2
          rcases hv2 with hvw | hvy2 | hvs2
          · exact Or.inl hvw
          · exfalso
            rw [hvy2] at hv1
            rcases hv1 with h1 | h2 | h3 | h4 | h5
            · exact hw_ne_T y2 hy2T h1.symm
            · exact hy12 h2.symm
            · exact hST_ne s1 hs1S y2 hy2T h3.symm
            · exact ht32 h4.symm
            · exact hST_ne s2 hs2S y2 hy2T h5.symm
          · exact Or.inr hvs2
        · simp [P1, P2]
      -- Every `w ∉ S ∪ T` has `≤ 1` neighbor in `S ∪ T`!
      have hle1_ST : ∀ w : V, w ∉ S ∪ T → (G.neighborFinset w ∩ (S ∪ T)).card ≤ 1 := by
        intro w hwST
        rw [Finset.card_le_one]
        intro y1 hy1 y2 hy2
        by_contra hy12
        rw [Finset.mem_inter, SimpleGraph.mem_neighborFinset] at hy1 hy2
        rcases Finset.mem_union.mp hy1.2 with hy1S | hy1T <;>
          rcases Finset.mem_union.mp hy2.2 with hy2S | hy2T
        · -- Both `y1, y2 ∈ S`: `S = {y1, y2}`, so `(S, insert w T)` beats `(S, T)`!
          have hpair_S : ({y1, y2} : Finset V) = S := by
            apply Finset.eq_of_subset_of_card_le
            · intro z hz
              simp only [Finset.mem_insert, Finset.mem_singleton] at hz
              rcases hz with rfl | rfl <;> assumption
            · rw [hS_card, Finset.card_pair hy12]
          have hw_not_T : w ∉ T := fun hm ↦ hwST (Finset.mem_union_right _ hm)
          have hw_not_S : w ∉ S := fun hm ↦ hwST (Finset.mem_union_left _ hm)
          have hk' : IsK2t (S, insert w T) := by
            refine ⟨hS_card, by rw [Finset.card_insert_of_notMem hw_not_T]; omega,
              Finset.disjoint_insert_right.mpr ⟨hw_not_S, hdisj_ST⟩, ?_⟩
            intro s hs t ht
            rcases Finset.mem_insert.mp ht with rfl | htT
            · rw [← hpair_S, Finset.mem_insert, Finset.mem_singleton] at hs
              rcases hs with rfl | rfl
              · exact hy1.1.symm
              · exact hy2.1.symm
            · exact hadj_ST s hs t htT
          have hle := hmax_T S (insert w T) hk'
          rw [Finset.card_insert_of_notMem hw_not_T] at hle
          omega
        · exact no_tri w y1 y2 hy1.1 (hadj_ST y1 hy1S y2 hy2T) hy2.1
        · exact no_tri w y2 y1 hy2.1 (hadj_ST y2 hy2S y1 hy1T) hy1.1
        · -- Both `y1, y2 ∈ T`:
          by_cases hT3 : 3 ≤ T.card
          · obtain ⟨t3, ht3T, ht3_not⟩ := Finset.exists_mem_notMem_of_card_lt_card
              (s := {y1, y2}) (t := T) (by rw [Finset.card_pair hy12]; omega)
            simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ht3_not
            exact six_cycle_T w y1 y2 t3 hwST hy1T hy2T ht3T hy12
              ht3_not.1 ht3_not.2 hy1.1 hy2.1
          · have hT2 : T.card = 2 := by omega
            have hpair_T : ({y1, y2} : Finset V) = T := by
              apply Finset.eq_of_subset_of_card_le
              · intro z hz
                simp only [Finset.mem_insert, Finset.mem_singleton] at hz
                rcases hz with rfl | rfl <;> assumption
              · rw [hT2, Finset.card_pair hy12]
            have hw_not_S : w ∉ S := fun hm ↦ hwST (Finset.mem_union_left _ hm)
            have hw_not_T : w ∉ T := fun hm ↦ hwST (Finset.mem_union_right _ hm)
            have hk' : IsK2t (T, insert w S) := by
              refine ⟨hT2, by rw [Finset.card_insert_of_notMem hw_not_S, hS_card]; omega,
                Finset.disjoint_insert_right.mpr ⟨hw_not_T, hdisj_ST.symm⟩, ?_⟩
              intro t ht s hs
              rcases Finset.mem_insert.mp hs with rfl | hsS
              · rw [← hpair_T, Finset.mem_insert, Finset.mem_singleton] at ht
                rcases ht with rfl | rfl
                · exact hy1.1.symm
                · exact hy2.1.symm
              · exact (hadj_ST s hsS t ht).symm
            have hle := hmax_T T (insert w S) hk'
            rw [Finset.card_insert_of_notMem hw_not_S, hS_card, hT2] at hle
            omega
      -- Pick `b0 ∈ T` with `b0 ≠ r`; `b0` has degree `≥ 3`, so it has a neighbor `q0 ∉ S ∪ T`!
      obtain ⟨b0, hb0T, hb0r⟩ : ∃ b0 ∈ T, b0 ≠ r := by
        by_cases hrT : r ∈ T
        · exact Finset.exists_mem_ne (by omega : 1 < T.card) r
        · obtain ⟨b0, hb0T⟩ := Finset.card_pos.mp (by omega : 0 < T.card)
          exact ⟨b0, hb0T, fun h ↦ hrT (h ▸ hb0T)⟩
      have hex_q0 : ∃ q0 : V, q0 ∉ S ∪ T ∧ G.Adj b0 q0 := by
        by_contra hall
        push Not at hall
        have hsub : G.neighborFinset b0 ⊆ S := by
          intro z hz
          have hadj_bz := (G.mem_neighborFinset _ _).mp hz
          have hzST : z ∈ S ∪ T := by
            by_contra hnot
            exact hall z hnot hadj_bz
          rcases Finset.mem_union.mp hzST with hzS | hzT
          · exact hzS
          · exact (hT_indep b0 hb0T z hzT hadj_bz).elim
        have hc1 := Finset.card_le_card hsub
        rw [card_neighborFinset_eq_degree, hS_card] at hc1
        have := hdeg b0 hb0r
        omega
      rcases hex_q0 with ⟨q0, hq0_not_ST, hadj_b0_q0⟩
      set U_ST := Finset.univ \ (S ∪ T)
      have hq0U : q0 ∈ U_ST := Finset.mem_sdiff.mpr ⟨Finset.mem_univ q0, hq0_not_ST⟩
      set Q := compIn G U_ST q0
      have hq0Q : q0 ∈ Q := self_mem_compIn hq0U
      have hdisj_Q_ST : Disjoint Q (S ∪ T) := by
        rw [Finset.disjoint_left]
        intro x hxQ hxST
        exact (Finset.mem_sdiff.mp (compIn_subset hxQ)).2 hxST
      have hbdy_Q : ∀ q ∈ Q, ∀ w ∉ Q, G.Adj q w → w ∈ S ∪ T := by
        intro q hqQ w hwQ hadj_qw
        by_cases hwU : w ∈ U_ST
        · exact (compIn_no_edge_out hqQ hwU hwQ hadj_qw).elim
        · simp only [U_ST, Finset.mem_sdiff, Finset.mem_univ, true_and, not_not] at hwU
          exact hwU
      have hQ_card : 2 ≤ Q.card := by
        by_contra hlt2
        have hQ1 : Q.card = 1 := by
          have := Finset.card_pos.mpr ⟨q0, hq0Q⟩; omega
        obtain ⟨q_only, hq_eq⟩ := Finset.card_eq_one.mp hQ1
        have hq0_eq : q0 = q_only := Finset.mem_singleton.mp (hq_eq ▸ hq0Q)
        subst q_only
        have hsub : G.neighborFinset q0 ⊆ G.neighborFinset q0 ∩ (S ∪ T) := by
          intro w hw
          have hadj_qw := (G.mem_neighborFinset _ _).mp hw
          have hw_not_Q : w ∉ Q := by
            rw [hq_eq, Finset.mem_singleton]
            exact (G.ne_of_adj hadj_qw).symm
          exact Finset.mem_inter.mpr ⟨hw, hbdy_Q q0 hq0Q w hw_not_Q hadj_qw⟩
        have hc1 := Finset.card_le_card hsub
        rw [card_neighborFinset_eq_degree] at hc1
        have hc2 := hle1_ST q0 hq0_not_ST
        have hc3 := h2G.two_le_degree (by omega) q0
        omega
      set NQ := (S ∪ T).filter (fun y ↦ ∃ q ∈ Q, G.Adj q y)
      have hb0_NQ : b0 ∈ NQ := Finset.mem_filter.mpr
        ⟨Finset.mem_union_right _ hb0T, q0, hq0Q, hadj_b0_q0.symm⟩
      have hNQ_card : 2 ≤ NQ.card := by
        by_contra hlt2
        have hNQ_sub : NQ ⊆ {b0} := by
          intro y hy
          rw [Finset.mem_singleton]
          exact Finset.card_le_one.mp (by omega : NQ.card ≤ 1) y hy b0 hb0_NQ
        have hq0_ne_b0 : q0 ≠ b0 := (G.ne_of_adj hadj_b0_q0).symm
        have hs1_ne_b0 : s1 ≠ b0 :=
          fun h ↦ Finset.disjoint_left.mp hdisj_ST hs1S (h ▸ hb0T)
        have hs1_not_Q : s1 ∉ Q :=
          fun hm ↦ Finset.disjoint_left.mp hdisj_Q_ST hm (Finset.mem_union_left _ hs1S)
        obtain ⟨p, hp⟩ := (reachable_induce_iff (U := {t : V | t ≠ b0})
          hq0_ne_b0 hs1_ne_b0).mp ((h2G.2 b0) ⟨q0, hq0_ne_b0⟩ ⟨s1, hs1_ne_b0⟩)
        obtain ⟨q', hq'Q, w_ex, hw_exQ, hadj_qw, hw_supp, _⟩ :=
          first_exit Q hq0Q hs1_not_Q p
        have hw_NQ : w_ex ∈ NQ := Finset.mem_filter.mpr
          ⟨hbdy_Q q' hq'Q w_ex hw_exQ hadj_qw, q', hq'Q, hadj_qw⟩
        exact hp w_ex hw_supp (Finset.mem_singleton.mp (hNQ_sub hw_NQ))
      -- Split on whether `NQ` meets `S` or `NQ ⊆ T`!
      by_cases hNQ_S : ∃ s0 ∈ NQ, s0 ∈ S
      · -- Case A: `NQ` meets BOTH `S` (`s0`) and `T` (`b0`), contract `(S, T)`!
        rcases hNQ_S with ⟨s0, hs0_NQ, hs0S⟩
        rcases (Finset.mem_filter.mp hs0_NQ).2 with ⟨qs0, hqs0Q, hadj_qs0⟩
        have hdisj_QS : Disjoint Q S :=
          Finset.disjoint_of_subset_right Finset.subset_union_left hdisj_Q_ST
        have hdisj_QT : Disjoint Q T :=
          Finset.disjoint_of_subset_right Finset.subset_union_right hdisj_Q_ST
        set G2 := contractTwo G Q S T
        have h2G2 : IsTwoConn (addEdge G2 (.inr 0) (.inr 1)) :=
          isTwoConn_addEdge_contractTwo h2G hq0U hdisj_QS hbdy_Q
            ⟨qs0, hqs0Q, s0, hs0S, hadj_qs0⟩ ⟨q0, hq0Q, b0, hb0T, hadj_b0_q0.symm⟩
        have hcard_G2 : 4 ≤ Fintype.card ({v : V // v ∈ Q} ⊕ Fin 2) := by
          simp [Fintype.card_sum, Fintype.card_coe]; omega
        set zG2 : {v : V // v ∈ Q} ⊕ Fin 2 :=
          if hrQ : r ∈ Q then .inl ⟨r, hrQ⟩ else .inr 0
        have hdeg_G2 : ∀ x : {v : V // v ∈ Q} ⊕ Fin 2,
            x ≠ .inr 0 → x ≠ .inr 1 → x ≠ zG2 → 3 ≤ G2.degree x := by
          intro x hx0 hx1 hxz
          cases x with
          | inr j => fin_cases j; exact (hx0 rfl).elim; exact (hx1 rfl).elim
          | inl a =>
            have har : a.1 ≠ r := by
              intro h
              apply hxz
              dsimp only [zG2]
              rw [dif_pos (h ▸ a.2)]
              exact congrArg Sum.inl (Subtype.ext h)
            have ha_not_ST : a.1 ∉ S ∪ T := Finset.disjoint_left.mp hdisj_Q_ST a.2
            have hleS : (G.neighborFinset a.1 ∩ S).card ≤ 1 :=
              (Finset.card_le_card (Finset.inter_subset_inter_left Finset.subset_union_left)).trans
                (hle1_ST a.1 ha_not_ST)
            have hleT : (G.neighborFinset a.1 ∩ T).card ≤ 1 :=
              (Finset.card_le_card (Finset.inter_subset_inter_left Finset.subset_union_right)).trans
                (hle1_ST a.1 ha_not_ST)
            exact (hdeg a.1 har).trans (degree_le_contractTwo a (hbdy_Q a.1 a.2) hleS hleT)
        obtain ⟨c1, c2, hc1_path, hc2_path, hc_mod⟩ :=
          two_paths_mod3_z _ G2 (.inr 0) (.inr 1) zG2 le_rfl hcard_G2
            (by intro h; simp at h) h2G2 hdeg_G2
        obtain ⟨u1, hu1S, v1, hv1T, p1, hp1_path, hp1_len, hp1_supp⟩ :=
          lift_walk_contractTwo hdisj_QS hdisj_QT hdisj_ST c1 hc1_path
        obtain ⟨u2, hu2S, v2, hv2T, p2, hp2_path, hp2_len, hp2_supp⟩ :=
          lift_walk_contractTwo hdisj_QS hdisj_QT hdisj_ST c2 hc2_path
        -- Close `pi : G.Walk ui vi` (`ui ∈ S, vi ∈ T`) when `pi.length % 3 ∈ {0, 2}`!
        have close_ST : ∀ (ui vi : V) (hui : ui ∈ S) (hvi : vi ∈ T) (pi : G.Walk ui vi),
            pi.IsPath → (∀ t ∈ pi.support, t ∈ Q ∨ t = ui ∨ t = vi) →
            pi.length % 3 ≠ 1 → False := by
          intro ui vi hui hvi pi hpi_path hpi_supp hmod_ne1
          have hui_ne_vi : ui ≠ vi :=
            fun h ↦ Finset.disjoint_left.mp hdisj_ST hui (h ▸ hvi)
          by_cases hm2 : pi.length % 3 = 2
          · -- Close with direct edge `ui - vi` (`pi.length ≥ 2` since `pi.length % 3 = 2`)!
            obtain ⟨C, hC, hC_len, _⟩ :=
              cycle_of_path_and_edge hpi_path (by omega) (hadj_ST ui hui vi hvi)
            exact hno_mod3 ⟨ui, C, hC, Nat.dvd_of_mod_eq_zero (by rw [hC_len]; omega)⟩
          · -- `pi.length % 3 = 0`: close with 3-edge path `ui - v' - u' - vi` in `K_{S, T}`!
            have hm0 : pi.length % 3 = 0 := by omega
            obtain ⟨u', hu'S, hu'ne⟩ := Finset.exists_mem_ne (by omega : 1 < S.card) ui
            obtain ⟨v', hv'T, hv'ne⟩ := Finset.exists_mem_ne (by omega : 1 < T.card) vi
            have hST_ne : ∀ s ∈ S, ∀ t ∈ T, s ≠ t :=
              fun s hs t ht h ↦ Finset.disjoint_left.mp hdisj_ST hs (h ▸ ht)
            set q3 : G.Walk ui vi :=
              .cons (hadj_ST ui hui v' hv'T)
                (.cons (hadj_ST u' hu'S v' hv'T).symm (.cons (hadj_ST u' hu'S vi hvi) .nil))
            have hq3_path : q3.IsPath := by
              have h_a : (Walk.cons (hadj_ST u' hu'S vi hvi) .nil).IsPath :=
                Walk.IsPath.cons Walk.IsPath.nil (by simp [hST_ne u' hu'S vi hvi])
              have h_b : (Walk.cons (hadj_ST u' hu'S v' hv'T).symm
                  (.cons (hadj_ST u' hu'S vi hvi) .nil)).IsPath := by
                apply Walk.IsPath.cons h_a
                simp only [Walk.support_cons, Walk.support_nil, List.mem_cons,
                  List.not_mem_nil, or_false, not_or]
                exact ⟨(hST_ne u' hu'S v' hv'T).symm, hv'ne⟩
              apply Walk.IsPath.cons h_b
              simp only [Walk.support_cons, Walk.support_nil, List.mem_cons,
                List.not_mem_nil, or_false, not_or]
              exact ⟨hST_ne ui hui v' hv'T, hu'ne.symm, hui_ne_vi⟩
            apply hno_mod3 (cycle_of_two_paths_mod3 hui_ne_vi hpi_path hq3_path ?_ ?_)
            · intro t ht1 ht2
              simp only [q3, Walk.support_cons, Walk.support_nil, List.mem_cons,
                List.not_mem_nil, or_false] at ht2
              rcases hpi_supp t ht1 with htQ | rfl | rfl
              · exfalso
                rcases ht2 with rfl | rfl | rfl | rfl
                · exact Finset.disjoint_left.mp hdisj_QS htQ hui
                · exact Finset.disjoint_left.mp hdisj_QT htQ hv'T
                · exact Finset.disjoint_left.mp hdisj_QS htQ hu'S
                · exact Finset.disjoint_left.mp hdisj_QT htQ hvi
              · exact Or.inl rfl
              · exact Or.inr rfl
            · simp only [q3, Walk.length_cons, Walk.length_nil]
              omega
        by_cases hp1_ne1 : p1.length % 3 ≠ 1
        · exact close_ST u1 v1 hu1S hv1T p1 hp1_path hp1_supp hp1_ne1
        · have hp2_ne1 : p2.length % 3 ≠ 1 := by omega
          exact close_ST u2 v2 hu2S hv2T p2 hp2_path hp2_supp hp2_ne1
      · -- Case C: `NQ ⊆ T`!
        push Not at hNQ_S
        have hNQ_sub_T : NQ ⊆ T := by
          intro y hy
          rcases Finset.mem_union.mp (Finset.mem_filter.mp hy).1 with hyS | hyT
          · exact (hNQ_S y hy hyS).elim
          · exact hyT
        by_cases hT3 : 3 ≤ T.card
        · -- `3 ≤ T.card`: contract `({b0}, NQ.erase b0)` and close with length `2` or `4` in `K_{S, T}`!
          obtain ⟨b1_t, hb1_NQ, hb1_ne_b0⟩ := Finset.exists_mem_ne hNQ_card b0
          set X0 : Finset V := {b0}
          set X1 : Finset V := NQ.erase b0
          have hdisj_QT : Disjoint Q T :=
            Finset.disjoint_of_subset_right Finset.subset_union_right hdisj_Q_ST
          have hdisj_QX0 : Disjoint Q X0 :=
            Finset.disjoint_of_subset_right (by simp [X0, hb0T]) hdisj_QT
          have hdisj_QX1 : Disjoint Q X1 :=
            Finset.disjoint_of_subset_right
              ((Finset.erase_subset b0 NQ).trans hNQ_sub_T) hdisj_QT
          have hdisj_01 : Disjoint X0 X1 :=
            Finset.disjoint_singleton_left.mpr (Finset.notMem_erase b0 NQ)
          have hbdy_Q01 : ∀ q ∈ Q, ∀ w ∉ Q, G.Adj q w → w ∈ X0 ∪ X1 := by
            intro q hqQ w hwQ hadj_qw
            have hwNQ : w ∈ NQ :=
              Finset.mem_filter.mpr ⟨hbdy_Q q hqQ w hwQ hadj_qw, q, hqQ, hadj_qw⟩
            by_cases hwb0 : w = b0
            · rw [hwb0]; simp [X0]
            · exact Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨hwb0, hwNQ⟩)
          rcases (Finset.mem_filter.mp hb1_NQ).2 with ⟨qb1, hqb1Q, hadj_qb1⟩
          set G2 := contractTwo G Q X0 X1
          have h2G2 : IsTwoConn (addEdge G2 (.inr 0) (.inr 1)) :=
            isTwoConn_addEdge_contractTwo h2G hq0U hdisj_QX0 hbdy_Q01
              ⟨q0, hq0Q, b0, by simp [X0], hadj_b0_q0.symm⟩
              ⟨qb1, hqb1Q, b1_t, Finset.mem_erase.mpr ⟨hb1_ne_b0, hb1_NQ⟩, hadj_qb1⟩
          have hcard_G2 : 4 ≤ Fintype.card ({v : V // v ∈ Q} ⊕ Fin 2) := by
            simp [Fintype.card_sum, Fintype.card_coe]; omega
          set zG2 : {v : V // v ∈ Q} ⊕ Fin 2 :=
            if hrQ : r ∈ Q then .inl ⟨r, hrQ⟩ else .inr 0
          have hdeg_G2 : ∀ x : {v : V // v ∈ Q} ⊕ Fin 2,
              x ≠ .inr 0 → x ≠ .inr 1 → x ≠ zG2 → 3 ≤ G2.degree x := by
            intro x hx0 hx1 hxz
            cases x with
            | inr j => fin_cases j; exact (hx0 rfl).elim; exact (hx1 rfl).elim
            | inl a =>
              have har : a.1 ≠ r := by
                intro h
                apply hxz
                dsimp only [zG2]
                rw [dif_pos (h ▸ a.2)]
                exact congrArg Sum.inl (Subtype.ext h)
              have ha_not_ST : a.1 ∉ S ∪ T := Finset.disjoint_left.mp hdisj_Q_ST a.2
              have hsub0 : X0 ⊆ S ∪ T := by
                simp [X0, Finset.mem_union_right _ hb0T]
              have hsub1 : X1 ⊆ S ∪ T :=
                ((Finset.erase_subset b0 NQ).trans hNQ_sub_T).trans Finset.subset_union_right
              exact (hdeg a.1 har).trans (degree_le_contractTwo a (hbdy_Q01 a.1 a.2)
                ((Finset.card_le_card (Finset.inter_subset_inter_left hsub0)).trans
                  (hle1_ST a.1 ha_not_ST))
                ((Finset.card_le_card (Finset.inter_subset_inter_left hsub1)).trans
                  (hle1_ST a.1 ha_not_ST)))
          obtain ⟨c1, c2, hc1_path, hc2_path, hc_mod⟩ :=
            two_paths_mod3_z _ G2 (.inr 0) (.inr 1) zG2 le_rfl hcard_G2
              (by intro h; simp at h) h2G2 hdeg_G2
          obtain ⟨u0_1, hu0_1, t_1, ht1_X1, p1, hp1_path, hp1_len, hp1_supp⟩ :=
            lift_walk_contractTwo hdisj_QX0 hdisj_QX1 hdisj_01 c1 hc1_path
          obtain ⟨u0_2, hu0_2, t_2, ht2_X1, p2, hp2_path, hp2_len, hp2_supp⟩ :=
            lift_walk_contractTwo hdisj_QX0 hdisj_QX1 hdisj_01 c2 hc2_path
          rw [Finset.mem_singleton] at hu0_1 hu0_2
          subst u0_1; subst u0_2
          have close_TT : ∀ (ti : V) (hti_X1 : ti ∈ X1) (pi : G.Walk b0 ti),
              pi.IsPath → (∀ t ∈ pi.support, t ∈ Q ∨ t = b0 ∨ t = ti) →
              pi.length % 3 ≠ 0 → False := by
            intro ti hti_X1 pi hpi_path hpi_supp hmod_ne0
            have hti_ne_b0 : ti ≠ b0 := (Finset.mem_erase.mp hti_X1).1
            have hti_T : ti ∈ T := hNQ_sub_T (Finset.mem_of_mem_erase hti_X1)
            have hST_ne : ∀ s ∈ S, ∀ t ∈ T, s ≠ t :=
              fun s hs t ht h ↦ Finset.disjoint_left.mp hdisj_ST hs (h ▸ ht)
            have hdisj_QS : Disjoint Q S :=
              Finset.disjoint_of_subset_right Finset.subset_union_left hdisj_Q_ST
            by_cases hm1 : pi.length % 3 = 1
            · -- Close with 2-edge path `b0 - s1 - ti`!
              set q2 : G.Walk b0 ti :=
                .cons (hadj_ST s1 hs1S b0 hb0T).symm (.cons (hadj_ST s1 hs1S ti hti_T) .nil)
              have hq2_path : q2.IsPath := by
                apply Walk.IsPath.cons
                  (Walk.IsPath.cons Walk.IsPath.nil (by simp [hST_ne s1 hs1S ti hti_T]))
                simp only [Walk.support_cons, Walk.support_nil, List.mem_cons,
                  List.not_mem_nil, or_false, not_or]
                exact ⟨(hST_ne s1 hs1S b0 hb0T).symm, hti_ne_b0.symm⟩
              apply hno_mod3 (cycle_of_two_paths_mod3 hti_ne_b0.symm hpi_path hq2_path ?_ ?_)
              · intro t ht1 ht2
                simp only [q2, Walk.support_cons, Walk.support_nil, List.mem_cons,
                  List.not_mem_nil, or_false] at ht2
                rcases hpi_supp t ht1 with htQ | rfl | rfl
                · exfalso
                  rcases ht2 with rfl | rfl | rfl
                  · exact Finset.disjoint_left.mp hdisj_QT htQ hb0T
                  · exact Finset.disjoint_left.mp hdisj_QS htQ hs1S
                  · exact Finset.disjoint_left.mp hdisj_QT htQ hti_T
                · exact Or.inl rfl
                · exact Or.inr rfl
              · simp only [q2, Walk.length_cons, Walk.length_nil]
                omega
            · -- `pi.length % 3 = 2`: pick `t3 ∈ T \ {b0, ti}`, close with 4-edge path `b0 - s1 - t3 - s2 - ti`!
              obtain ⟨t3, ht3T, ht3_not⟩ := Finset.exists_mem_notMem_of_card_lt_card
                (s := {b0, ti}) (t := T) (by rw [Finset.card_pair hti_ne_b0.symm]; omega)
              simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ht3_not
              set q4 : G.Walk b0 ti :=
                .cons (hadj_ST s1 hs1S b0 hb0T).symm
                  (.cons (hadj_ST s1 hs1S t3 ht3T)
                    (.cons (hadj_ST s2 hs2S t3 ht3T).symm
                      (.cons (hadj_ST s2 hs2S ti hti_T) .nil)))
              have hq4_path : q4.IsPath := by
                have h_a : (Walk.cons (hadj_ST s2 hs2S ti hti_T) .nil).IsPath :=
                  Walk.IsPath.cons Walk.IsPath.nil (by simp [hST_ne s2 hs2S ti hti_T])
                have h_b : (Walk.cons (hadj_ST s2 hs2S t3 ht3T).symm
                    (.cons (hadj_ST s2 hs2S ti hti_T) .nil)).IsPath := by
                  apply Walk.IsPath.cons h_a
                  simp only [Walk.support_cons, Walk.support_nil, List.mem_cons,
                    List.not_mem_nil, or_false, not_or]
                  exact ⟨(hST_ne s2 hs2S t3 ht3T).symm, ht3_not.2⟩
                have h_c : (Walk.cons (hadj_ST s1 hs1S t3 ht3T)
                    (.cons (hadj_ST s2 hs2S t3 ht3T).symm
                      (.cons (hadj_ST s2 hs2S ti hti_T) .nil))).IsPath := by
                  apply Walk.IsPath.cons h_b
                  simp only [Walk.support_cons, Walk.support_nil, List.mem_cons,
                    List.not_mem_nil, or_false, not_or]
                  exact ⟨hST_ne s1 hs1S t3 ht3T, hs12, hST_ne s1 hs1S ti hti_T⟩
                apply Walk.IsPath.cons h_c
                simp only [Walk.support_cons, Walk.support_nil, List.mem_cons,
                  List.not_mem_nil, or_false, not_or]
                exact ⟨(hST_ne s1 hs1S b0 hb0T).symm, Ne.symm ht3_not.1,
                  (hST_ne s2 hs2S b0 hb0T).symm, hti_ne_b0.symm⟩
              apply hno_mod3 (cycle_of_two_paths_mod3 hti_ne_b0.symm hpi_path hq4_path ?_ ?_)
              · intro t ht1 ht2
                simp only [q4, Walk.support_cons, Walk.support_nil, List.mem_cons,
                  List.not_mem_nil, or_false] at ht2
                rcases hpi_supp t ht1 with htQ | rfl | rfl
                · exfalso
                  rcases ht2 with rfl | rfl | rfl | rfl | rfl
                  · exact Finset.disjoint_left.mp hdisj_QT htQ hb0T
                  · exact Finset.disjoint_left.mp hdisj_QS htQ hs1S
                  · exact Finset.disjoint_left.mp hdisj_QT htQ ht3T
                  · exact Finset.disjoint_left.mp hdisj_QS htQ hs2S
                  · exact Finset.disjoint_left.mp hdisj_QT htQ hti_T
                · exact Or.inl rfl
                · exact Or.inr rfl
              · simp only [q4, Walk.length_cons, Walk.length_nil]
                omega
          by_cases hp1_ne0 : p1.length % 3 ≠ 0
          · exact close_TT t_1 ht1_X1 p1 hp1_path hp1_supp hp1_ne0
          · have hp2_ne0 : p2.length % 3 ≠ 0 := by omega
            exact close_TT t_2 ht2_X1 p2 hp2_path hp2_supp hp2_ne0
        · -- `T.card = 2`: `T` is a 2-cut separating `Q` (`≥ 2`) from `compIn G (univ \ T) s_i` (`≥ 2`)!
          have hT2 : T.card = 2 := by omega
          rcases Finset.card_eq_two.mp hT2 with ⟨t1, t2, ht12, hT_eq⟩
          obtain ⟨si, hsiS, hsir⟩ : ∃ si ∈ S, si ≠ r := by
            by_cases hrS : r ∈ S
            · exact Finset.exists_mem_ne (by omega : 1 < S.card) r
            · exact ⟨s1, hs1S, fun h ↦ hrS (h ▸ hs1S)⟩
          -- `si` has degree `≥ 3`, `S` is independent, `T.card = 2`, so `si` has a neighbor `w_si ∉ S ∪ T`!
          have hex_wsi : ∃ wsi : V, wsi ∉ S ∪ T ∧ G.Adj si wsi := by
            by_contra hall
            push Not at hall
            have hsub : G.neighborFinset si ⊆ T := by
              intro z hz
              have hadj_sz := (G.mem_neighborFinset _ _).mp hz
              have hzST : z ∈ S ∪ T := by
                by_contra hnot
                exact hall z hnot hadj_sz
              rcases Finset.mem_union.mp hzST with hzS | hzT
              · exact (hS_indep si hsiS z hzS hadj_sz).elim
              · exact hzT
            have hc1 := Finset.card_le_card hsub
            rw [card_neighborFinset_eq_degree, hT2] at hc1
            have := hdeg si hsir
            omega
          rcases hex_wsi with ⟨wsi, hwsi_not_ST, hadj_si_wsi⟩
          set U_T := Finset.univ \ ({t1, t2} : Finset V)
          have hU_T_eq : U_T = Finset.univ \ T := by rw [hT_eq]
          have hq0_UT : q0 ∈ U_T := by
            rw [hU_T_eq]
            exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ q0,
              fun hm ↦ hq0_not_ST (Finset.mem_union_right _ hm)⟩
          have hsi_UT : si ∈ U_T := by
            rw [hU_T_eq]
            exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ si,
              Finset.disjoint_left.mp hdisj_ST hsiS⟩
          have hwsi_UT : wsi ∈ U_T := by
            rw [hU_T_eq]
            exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ wsi,
              fun hm ↦ hwsi_not_ST (Finset.mem_union_right _ hm)⟩
          -- Show `compIn G U_T q0 = Q`!
          have hQ_eq_UT : compIn G U_T q0 = Q := by
            apply Finset.Subset.antisymm
            · intro x hx
              rcases mem_compIn_iff.mp hx with ⟨_, p, hp⟩
              by_contra hxQ
              obtain ⟨q', hq'Q, w_ex, hw_exQ, hadj_qw, hw_supp, _⟩ :=
                first_exit Q hq0Q hxQ p
              have hw_NQ : w_ex ∈ NQ :=
                Finset.mem_filter.mpr ⟨hbdy_Q q' hq'Q w_ex hw_exQ hadj_qw, q', hq'Q, hadj_qw⟩
              have hw_T : w_ex ∈ T := hNQ_sub_T hw_NQ
              have hw_UT : w_ex ∈ U_T := hp w_ex hw_supp
              rw [hU_T_eq] at hw_UT
              exact (Finset.mem_sdiff.mp hw_UT).2 hw_T
            · intro x hx
              rcases mem_compIn_iff.mp hx with ⟨_, p, hp⟩
              rw [mem_compIn_iff]
              have hsub_U : U_ST ⊆ U_T := by
                rw [hU_T_eq]
                exact Finset.sdiff_subset_sdiff (Finset.Subset.refl _) Finset.subset_union_right
              exact ⟨hsub_U (compIn_subset hx), p, fun w hw ↦ hsub_U (hp w hw)⟩
          have hsi_not_Q : si ∉ compIn G U_T q0 := by
            rw [hQ_eq_UT]
            exact fun hm ↦ Finset.disjoint_left.mp hdisj_Q_ST hm (Finset.mem_union_left _ hsiS)
          have hdisj_Q_Qsi : Disjoint (compIn G U_T q0) (compIn G U_T si) := by
            rw [Finset.disjoint_left]
            intro x hx1 hx2
            rcases mem_compIn_iff.mp hx1 with ⟨_, p1, hp1⟩
            rcases mem_compIn_iff.mp hx2 with ⟨_, p2, hp2⟩
            apply hsi_not_Q
            rw [mem_compIn_iff]
            refine ⟨hsi_UT, p1.append p2.reverse, fun w hw ↦ ?_⟩
            rw [Walk.support_append] at hw
            rcases List.mem_append.mp hw with hw1 | hw2
            · exact hp1 w hw1
            · have hw2' := List.mem_of_mem_tail hw2
              rw [Walk.support_reverse, List.mem_reverse] at hw2'
              exact hp2 w hw2'
          have hcard_Qsi : 2 ≤ (compIn G U_T si).card := by
            have hsi_mem : si ∈ compIn G U_T si := self_mem_compIn hsi_UT
            have hwsi_mem : wsi ∈ compIn G U_T si := by
              rw [mem_compIn_iff]
              refine ⟨hwsi_UT, .cons hadj_si_wsi .nil, ?_⟩
              simp only [Walk.support_cons, Walk.support_nil, List.mem_cons,
                List.not_mem_nil, or_false]
              rintro w (rfl | rfl)
              · exact hsi_UT
              · exact hwsi_UT
            have hne_sw : si ≠ wsi := G.ne_of_adj hadj_si_wsi
            have hsub_pair : ({si, wsi} : Finset V) ⊆ compIn G U_T si := by
              intro z hz
              simp only [Finset.mem_insert, Finset.mem_singleton] at hz
              rcases hz with rfl | rfl <;> assumption
            have hc := Finset.card_le_card hsub_pair
            rw [Finset.card_pair hne_sw] at hc
            exact hc
          exact no_two_large_comps hno_mod3 h2G hdeg ht12 hq0_UT hsi_UT
            hdisj_Q_Qsi (by rw [hQ_eq_UT]; exact hQ_card) hcard_Qsi
    -- Consequence of `no_tri` and `no_c4`: every simple cycle in `G` has length `≥ 5`!
    have five_le_cycle : ∀ {w0 : V} {C : G.Walk w0 w0}, C.IsCycle → 5 ≤ C.length := by
      intro w0 C hC
      obtain ⟨hc, _, _, _⟩ := isCycle_to_cyclicSeq hC
      have hm3 : 3 ≤ C.length := hC.three_le_length
      have hne3 : C.length ≠ 3 := fun h3 ↦ hno_mod3 ⟨w0, C, hC, by rw [h3]⟩
      have hne4 : C.length ≠ 4 := by
        intro h4
        apply no_c4
        let c := fun i ↦ wVert C (i % C.length)
        have hc4 : c 4 = c 0 := by
          have h_eq4 : (4 : ℕ) = 0 + C.length := by omega
          dsimp only [c]
          rw [h_eq4]
          exact hc.per 0
        refine ⟨c 0, c 1, c 2, c 3,
          fun h ↦ by have := hc.inj (by omega) (by omega) h; omega,
          fun h ↦ by have := hc.inj (by omega) (by omega) h; omega,
          hc.adj 0, hc.adj 1, hc.adj 2, ?_⟩
        have h34 : G.Adj (c 3) (c 4) := hc.adj 3
        rwa [hc4] at h34
      omega
    -- Step 2.5: Choose an optimal cycle `C` in `G - r` and apply `cycle_tree_mod3`!
    classical
    -- First show `G - r` contains at least one cycle.
    have hex_cycle_no_r : ∃ (v0 : V) (C : G.Walk v0 v0), C.IsCycle ∧ r ∉ C.support := by
      set Sr : Set V := {v : V | v ≠ r}
      obtain ⟨u0, _, hu0r⟩ : ∃ u0 ∈ (Finset.univ : Finset V), u0 ≠ r :=
        Finset.exists_mem_ne (by simp; omega) r
      have : Nonempty {v : V // v ∈ Sr} := ⟨⟨u0, hu0r⟩⟩
      have hdeg_Sr : ∀ u : {v : V // v ∈ Sr}, 2 ≤ (G.induce Sr).degree u := by
        intro u
        have hu_deg : 3 ≤ G.degree u.1 := hdeg u.1 u.2
        rw [← card_neighborFinset_eq_degree] at hu_deg ⊢
        -- Every neighbor `w ≠ r` of `u.1` in `G` lifts to `(G.induce Sr).neighborFinset u`!
        have hsub : G.neighborFinset u.1 \ {r} ⊆
            ((G.induce Sr).neighborFinset u).image Subtype.val := by
          intro w hw
          rw [Finset.mem_sdiff, SimpleGraph.mem_neighborFinset, Finset.mem_singleton] at hw
          rw [Finset.mem_image]
          exact ⟨⟨w, hw.2⟩, (SimpleGraph.mem_neighborFinset _ _ _).mpr hw.1, rfl⟩
        have hc1 := Finset.card_le_card hsub
        have hc2 := Finset.card_image_le (f := Subtype.val) (s := (G.induce Sr).neighborFinset u)
        have hc3 : G.neighborFinset u.1 ⊆ insert r (G.neighborFinset u.1 \ {r}) := by
          intro w hw
          by_cases hwr : w = r
          · rw [hwr]; exact Finset.mem_insert_self r _
          · exact Finset.mem_insert_of_mem (Finset.mem_sdiff.mpr ⟨hw, Finset.notMem_singleton.mpr hwr⟩)
        have hc4 := (Finset.card_le_card hc3).trans (Finset.card_insert_le _ _)
        omega
      obtain ⟨v_sub, C_sub, hC_sub⟩ := exists_cycle_of_deg_ge_two (G.induce Sr) hdeg_Sr
      set C_lift := C_sub.map (Embedding.induce (G := G) Sr).toHom
      have hC_lift : C_lift.IsCycle := hC_sub.map (Embedding.induce (G := G) Sr).injective
      refine ⟨(Embedding.induce (G := G) Sr).toHom v_sub, C_lift, hC_lift, ?_⟩
      intro hr_mem
      dsimp only [C_lift] at hr_mem
      rw [Walk.support_map, List.mem_map] at hr_mem
      rcases hr_mem with ⟨x, _, hxr⟩
      exact x.2 hxr
    -- Score function: `R0.card * (M0 + 1) + (M0 - C.length)` where `M0 := Fintype.card V`.
    set M0 := Fintype.card V
    let scoreOf : ∀ {v0 : V}, G.Walk v0 v0 → ℕ := fun C ↦
      (compIn G (Finset.univ \ C.support.toFinset) r).card * (M0 + 1) + (M0 - C.length)
    have score_lt : ∀ {v0 : V} (C : G.Walk v0 v0), scoreOf C < (M0 + 1) * (M0 + 2) := by
      intro v0 C
      dsimp only [scoreOf]
      have hc1 : (compIn G (Finset.univ \ C.support.toFinset) r).card ≤ M0 :=
        Finset.card_le_univ _
      have hc2 : M0 - C.length ≤ M0 := Nat.sub_le _ _
      nlinarith
    set Scyc : Finset ℕ := (Finset.range ((M0 + 1) * (M0 + 2))).filter
      (fun k ↦ ∃ (v0 : V) (C : G.Walk v0 v0), C.IsCycle ∧ r ∉ C.support ∧ scoreOf C = k)
    have hScyc_ne : Scyc.Nonempty := by
      rcases hex_cycle_no_r with ⟨v0, C0, hC0, hr0⟩
      exact ⟨scoreOf C0, Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr (score_lt C0), v0, C0, hC0, hr0, rfl⟩⟩
    set k_max := Scyc.max' hScyc_ne
    have hk_mem : k_max ∈ Scyc := Scyc.max'_mem hScyc_ne
    simp only [Scyc, Finset.mem_filter, Finset.mem_range] at hk_mem
    rcases hk_mem with ⟨_, v0, C, hC, hr_not_C, hC_score⟩
    have score_le_max : ∀ {w0 : V} (C' : G.Walk w0 w0),
        C'.IsCycle → r ∉ C'.support → scoreOf C' ≤ scoreOf C := by
      intro w0 C' hC' hr'
      rw [hC_score]
      exact Scyc.le_max' (scoreOf C') (Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr (score_lt C'), w0, C', hC', hr', rfl⟩)
    -- Unpack cyclic sequence `c` of `C`.
    obtain ⟨hc, hC_supp, hVc_eq, hVc_card⟩ := isCycle_to_cyclicSeq hC
    set m := C.length
    set c : ℕ → V := fun i ↦ wVert C (i % m)
    set Vc := C.support.toFinset
    have hm5 : 5 ≤ m := five_le_cycle hC
    have hm_le_M0 : m ≤ M0 := by
      rw [← hVc_card]
      exact Finset.card_le_univ Vc
    have hm_mod3 : m % 3 ≠ 0 := fun hm0 ↦ hno_mod3 ⟨v0, C, hC, Nat.dvd_of_mod_eq_zero hm0⟩
    have hc_mem_Vc : ∀ i : ℕ, c i ∈ Vc := by
      intro i
      rw [List.mem_toFinset, hC_supp]
      exact ⟨i % m, Nat.mod_lt i (by omega), hc.mod_eq i⟩
    have hr_not_Vc : r ∉ Vc := by rwa [List.mem_toFinset]
    set U := Finset.univ \ Vc
    have hrU : r ∈ U := Finset.mem_sdiff.mpr ⟨Finset.mem_univ r, hr_not_Vc⟩
    set R0 := compIn G U r
    have hr_R0 : r ∈ R0 := self_mem_compIn hrU
    -- Step 2.5a: `C` is chordless!
    have hchord : ∀ i j : ℕ, i < j → j < m → G.Adj (c i) (c j) →
        j = i + 1 ∨ (i = 0 ∧ j = m - 1) := by
      intro i j hij hj hadj_ij
      by_contra hnot
      push Not at hnot
      have hlen_ge2 : 2 ≤ j - i := by omega
      have hlen_lt : j - i < m := by omega
      have hij_eq : i + (j - i) = j := by omega
      set a0 : G.Walk (c i) (c (i + (j - i))) := cArc hc i (j - i)
      have ha0_path : a0.IsPath := cArc_isPath hc i (by omega)
      set a : G.Walk (c i) (c j) := a0.copy rfl (congrArg c hij_eq)
      have ha_path : a.IsPath := (Walk.isPath_copy _ _ _).mpr ha0_path
      have ha_len : a.length = j - i := by rw [Walk.length_copy, cArc_length]
      obtain ⟨C1, hC1, hC1_len, hC1_sub⟩ :=
        cycle_of_path_and_edge ha_path (by omega) hadj_ij
      have hC1_Vc : C1.support.toFinset ⊆ Vc := by
        intro w hw
        rw [List.mem_toFinset] at hw
        have hwa := hC1_sub w hw
        rw [Walk.support_copy, mem_cArc_support] at hwa
        rcases hwa with ⟨t, _, rfl⟩
        exact hc_mem_Vc (i + t)
      have hr_not_C1 : r ∉ C1.support :=
        fun hm ↦ hr_not_Vc (hC1_Vc (List.mem_toFinset.mpr hm))
      have hR0_sub : R0 ⊆ compIn G (Finset.univ \ C1.support.toFinset) r := by
        intro w hw
        rcases mem_compIn_iff.mp hw with ⟨hwU, p, hp⟩
        have hsub_U : U ⊆ Finset.univ \ C1.support.toFinset :=
          Finset.sdiff_subset_sdiff (Finset.Subset.refl _) hC1_Vc
        exact mem_compIn_iff.mpr ⟨hsub_U hwU, p, fun t ht ↦ hsub_U (hp t ht)⟩
      have hR0_le : R0.card ≤ (compIn G (Finset.univ \ C1.support.toFinset) r).card :=
        Finset.card_le_card hR0_sub
      have hC1_lt : C1.length < m := by
        rw [hC1_len, ha_len]
        omega
      have hle_sc := score_le_max C1 hC1 hr_not_C1
      dsimp only [scoreOf] at hle_sc
      change (compIn G (Finset.univ \ C1.support.toFinset) r).card * (M0 + 1) + (M0 - C1.length) ≤
        R0.card * (M0 + 1) + (M0 - m) at hle_sc
      have hsub_lt : M0 - m < M0 - C1.length := by omega
      nlinarith
    -- Every `c i` (`i < m`) has a neighbor in `U = Finset.univ \ Vc`!
    have hex_nb_U : ∀ i : ℕ, i < m → ∃ w ∈ U, G.Adj (c i) w := by
      intro i hi
      have hnb_Vc_sub : G.neighborFinset (c i) ∩ Vc ⊆ {c (i + m - 1), c (i + 1)} := by
        intro w hw
        rw [Finset.mem_inter, SimpleGraph.mem_neighborFinset] at hw
        have hw_C : w ∈ C.support := List.mem_toFinset.mp hw.2
        rw [hC_supp] at hw_C
        rcases hw_C with ⟨j, hj, rfl⟩
        have hij_ne : i ≠ j := fun h ↦ G.ne_of_adj hw.1 (congrArg c h)
        by_cases hij : i < j
        · rcases hchord i j hij hj hw.1 with rfl | ⟨rfl, rfl⟩
          · simp
          · simp
        · have hji : j < i := by omega
          rcases hchord j i hji hi hw.1.symm with h_eq | ⟨rfl, rfl⟩
          · have h_im : i + m - 1 = j + m := by omega
            rw [h_im, hc.per]
            simp
          · have h_m : m - 1 + 1 = 0 + m := by omega
            rw [h_m, hc.per]
            simp
      have hc1 := (Finset.card_le_card hnb_Vc_sub).trans Finset.card_le_two
      have hci_ne_r : c i ≠ r := fun h ↦ hr_not_Vc (h ▸ hc_mem_Vc i)
      have hc2 : 3 ≤ (G.neighborFinset (c i)).card := by
        rw [card_neighborFinset_eq_degree]
        exact hdeg (c i) hci_ne_r
      obtain ⟨w, hw_nb, hw_not_inter⟩ := Finset.exists_mem_notMem_of_card_lt_card
        (s := G.neighborFinset (c i) ∩ Vc) (t := G.neighborFinset (c i)) (by omega)
      have hw_not_Vc : w ∉ Vc := fun hm ↦ hw_not_inter (Finset.mem_inter.mpr ⟨hw_nb, hm⟩)
      exact ⟨w, Finset.mem_sdiff.mpr ⟨Finset.mem_univ w, hw_not_Vc⟩,
        (G.mem_neighborFinset _ _).mp hw_nb⟩
    -- Step 2.5b: `U = R0` (so `G - C` is connected)!
    have hU_eq_R0 : U = R0 := by
      apply Finset.Subset.antisymm _ compIn_subset
      intro d0 hd0U
      by_contra hd0_not_R0
      set D := compIn G U d0
      have hd0D : d0 ∈ D := self_mem_compIn hd0U
      have hdisj_D_R0 : Disjoint D R0 := by
        rw [Finset.disjoint_left]
        intro x hxD hxR0
        rcases mem_compIn_iff.mp hxD with ⟨_, p1, hp1⟩
        rcases mem_compIn_iff.mp hxR0 with ⟨_, p2, hp2⟩
        apply hd0_not_R0
        rw [mem_compIn_iff]
        refine ⟨hd0U, p2.append p1.reverse, fun w hw ↦ ?_⟩
        rw [Walk.support_append] at hw
        rcases List.mem_append.mp hw with hw1 | hw2
        · exact hp2 w hw1
        · have hw2' := List.mem_of_mem_tail hw2
          rw [Walk.support_reverse, List.mem_reverse] at hw2'
          exact hp1 w hw2'
      have hr_not_D : r ∉ D := fun hm ↦ Finset.disjoint_left.mp hdisj_D_R0 hm hr_R0
      have hdisj_D_Vc : Disjoint D Vc := by
        rw [Finset.disjoint_left]
        intro x hxD hxVc
        exact (Finset.mem_sdiff.mp (compIn_subset hxD)).2 hxVc
      have hbdy_D : ∀ d ∈ D, ∀ w ∉ D, G.Adj d w → w ∈ Vc := by
        intro d hdD w hwD hadj_dw
        by_cases hwU : w ∈ U
        · exact (compIn_no_edge_out hdD hwU hwD hadj_dw).elim
        · simp only [U, Finset.mem_sdiff, Finset.mem_univ, true_and, not_not] at hwU
          exact hwU
      set ND := Vc.filter (fun w ↦ ∃ d ∈ D, G.Adj d w)
      -- Show `3 ≤ ND.card`!
      have hND_card3 : 3 ≤ ND.card := by
        by_cases hD2 : 2 ≤ D.card
        · -- First show `2 ≤ ND.card` by `h2G : IsTwoConn G`.
          have hND_ge2 : 2 ≤ ND.card := by
            by_contra hlt2
            by_cases hND0 : ND.card = 0
            · obtain ⟨p⟩ := hG_conn d0 (c 0)
              obtain ⟨q', hq'D, w_ex, hw_exD, hadj_qw, _, _, _⟩ :=
                first_exit D hd0D (Finset.disjoint_right.mp hdisj_D_Vc (hc_mem_Vc 0)) p
              have hw_ND : w_ex ∈ ND :=
                Finset.mem_filter.mpr ⟨hbdy_D q' hq'D w_ex hw_exD hadj_qw, q', hq'D, hadj_qw⟩
              rw [Finset.card_eq_zero.mp hND0] at hw_ND
              simp at hw_ND
            · have hND1 : ND.card = 1 := by omega
              obtain ⟨y0, hy0_eq⟩ := Finset.card_eq_one.mp hND1
              obtain ⟨d_pick, hd_pickD, hd_ne_y0⟩ : ∃ d_pick ∈ D, d_pick ≠ y0 :=
                Finset.exists_mem_ne (by omega : 1 < D.card) y0
              have hr_ne_y0 : r ≠ y0 := by
                intro h
                subst y0
                have hm : r ∈ ND := by rw [hy0_eq]; simp
                exact hr_not_Vc (Finset.mem_filter.mp hm).1
              obtain ⟨p, hp⟩ := (reachable_induce_iff (U := {t : V | t ≠ y0})
                hd_ne_y0 hr_ne_y0).mp ((h2G.2 y0) ⟨d_pick, hd_ne_y0⟩ ⟨r, hr_ne_y0⟩)
              obtain ⟨q', hq'D, w_ex, hw_exD, hadj_qw, hw_supp, _⟩ :=
                first_exit D hd_pickD hr_not_D p
              have hw_ND : w_ex ∈ ND :=
                Finset.mem_filter.mpr ⟨hbdy_D q' hq'D w_ex hw_exD hadj_qw, q', hq'D, hadj_qw⟩
              rw [hy0_eq, Finset.mem_singleton] at hw_ND
              exact hp w_ex hw_supp hw_ND
          by_contra hlt3
          have hND2 : ND.card = 2 := by omega
          rcases Finset.card_eq_two.mp hND2 with ⟨u1, u2, hu12, hND_eq⟩
          have hu1_Vc : u1 ∈ Vc := (Finset.mem_filter.mp (by rw [hND_eq]; simp : u1 ∈ ND)).1
          have hu2_Vc : u2 ∈ Vc := (Finset.mem_filter.mp (by rw [hND_eq]; simp : u2 ∈ ND)).1
          obtain ⟨i1, hi1, rfl⟩ := (hC_supp u1).mp (List.mem_toFinset.mp hu1_Vc)
          obtain ⟨i2, hi2, rfl⟩ := (hC_supp u2).mp (List.mem_toFinset.mp hu2_Vc)
          -- Order `{i1, i2}` as `ia < ib < m`!
          obtain ⟨ia, ib, hia_ib, hib_m, hND_pair⟩ :
              ∃ ia ib : ℕ, ia < ib ∧ ib < m ∧ ND = {c ia, c ib} := by
            have hij_ne : i1 ≠ i2 := fun h ↦ hu12 (congrArg c h)
            by_cases hlt : i1 < i2
            · exact ⟨i1, i2, hlt, hi2, hND_eq⟩
            · refine ⟨i2, i1, by omega, hi1, ?_⟩
              rw [hND_eq, Finset.pair_comm]
          have hcab_ne : c ia ≠ c ib := fun h ↦ (Nat.ne_of_lt hia_ib) (hc.inj (by omega) hib_m h)
          set U_ab := Finset.univ \ ({c ia, c ib} : Finset V)
          have hD_eq_Uab : compIn G U_ab d0 = D := by
            apply Finset.Subset.antisymm
            · intro x hx
              rcases mem_compIn_iff.mp hx with ⟨_, p, hp⟩
              by_contra hxD
              have hd0_Uab : d0 ∈ U_ab := by
                have hsub : U ⊆ U_ab :=
                  Finset.sdiff_subset_sdiff (Finset.Subset.refl _) (by
                    intro z hz; simp only [Finset.mem_insert, Finset.mem_singleton] at hz;
                    rcases hz with rfl | rfl <;> exact hc_mem_Vc _)
                exact hsub hd0U
              obtain ⟨q', hq'D, w_ex, hw_exD, hadj_qw, hw_supp, _⟩ :=
                first_exit D hd0D hxD p
              have hw_ND : w_ex ∈ ND :=
                Finset.mem_filter.mpr ⟨hbdy_D q' hq'D w_ex hw_exD hadj_qw, q', hq'D, hadj_qw⟩
              rw [hND_pair] at hw_ND
              exact (Finset.mem_sdiff.mp (hp w_ex hw_supp)).2 hw_ND
            · intro x hx
              rcases mem_compIn_iff.mp hx with ⟨_, p, hp⟩
              have hsub : U ⊆ U_ab :=
                Finset.sdiff_subset_sdiff (Finset.Subset.refl _) (by
                  intro z hz; simp only [Finset.mem_insert, Finset.mem_singleton] at hz;
                  rcases hz with rfl | rfl <;> exact hc_mem_Vc _)
              exact mem_compIn_iff.mpr ⟨hsub (compIn_subset hx), p, fun w hw ↦ hsub (hp w hw)⟩
          -- Find 2 adjacent cycle vertices in `Vc \ {c ia, c ib}`!
          have hex_adj_pair : ∃ y1 y2 : V, y1 ∈ Vc ∧ y1 ∈ U_ab ∧ y2 ∈ U_ab ∧ G.Adj y1 y2 := by
            by_cases hgap1 : ia + 2 < ib
            · refine ⟨c (ia + 1), c (ia + 2), hc_mem_Vc _, ?_, ?_, hc.adj (ia + 1)⟩
              · simp only [U_ab, Finset.mem_sdiff, Finset.mem_univ, Finset.mem_insert,
                  Finset.mem_singleton, true_and, not_or]
                exact ⟨fun h ↦ by have := hc.inj (by omega) (by omega) h; omega,
                  fun h ↦ by have := hc.inj (by omega) hib_m h; omega⟩
              · simp only [U_ab, Finset.mem_sdiff, Finset.mem_univ, Finset.mem_insert,
                  Finset.mem_singleton, true_and, not_or]
                exact ⟨fun h ↦ by have := hc.inj (by omega) (by omega) h; omega,
                  fun h ↦ by have := hc.inj (by omega) hib_m h; omega⟩
            · have hgap2 : ib + 2 < ia + m := by omega
              refine ⟨c (ib + 1), c (ib + 2), hc_mem_Vc _, ?_, ?_, hc.adj (ib + 1)⟩
              · simp only [U_ab, Finset.mem_sdiff, Finset.mem_univ, Finset.mem_insert,
                  Finset.mem_singleton, true_and, not_or]
                refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
                · have h' : c (ib + 1) = c (ia + m) := by rw [hc.per]; exact h
                  have := eq_of_mod_eq_of_lt_add (m := m) (a := ib + 1) (b := ia + m)
                    (by omega) (by omega) (hc.eq_iff.mp h')
                  omega
                · have := eq_of_mod_eq_of_lt_add (m := m) (a := ib) (b := ib + 1)
                    (by omega) (by omega) (hc.eq_iff.mp h.symm)
                  omega
              · simp only [U_ab, Finset.mem_sdiff, Finset.mem_univ, Finset.mem_insert,
                  Finset.mem_singleton, true_and, not_or]
                refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
                · have h' : c (ib + 2) = c (ia + m) := by rw [hc.per]; exact h
                  have := eq_of_mod_eq_of_lt_add (m := m) (a := ib + 2) (b := ia + m)
                    (by omega) (by omega) (hc.eq_iff.mp h')
                  omega
                · have := eq_of_mod_eq_of_lt_add (m := m) (a := ib) (b := ib + 2)
                    (by omega) (by omega) (hc.eq_iff.mp h.symm)
                  omega
          rcases hex_adj_pair with ⟨y1, y2, hy1_Vc, hy1_Uab, hy2_Uab, hadj_y12⟩
          have hd0_Uab : d0 ∈ U_ab := by
            have hsub : U ⊆ U_ab :=
              Finset.sdiff_subset_sdiff (Finset.Subset.refl _) (by
                intro z hz; simp only [Finset.mem_insert, Finset.mem_singleton] at hz;
                rcases hz with rfl | rfl <;> exact hc_mem_Vc _)
            exact hsub hd0U
          have hy1_not_D : y1 ∉ compIn G U_ab d0 := by
            rw [hD_eq_Uab]
            exact Finset.disjoint_right.mp hdisj_D_Vc hy1_Vc
          have hdisj_D_Qy : Disjoint (compIn G U_ab d0) (compIn G U_ab y1) := by
            rw [Finset.disjoint_left]
            intro x hx1 hx2
            rcases mem_compIn_iff.mp hx1 with ⟨_, p1, hp1⟩
            rcases mem_compIn_iff.mp hx2 with ⟨_, p2, hp2⟩
            apply hy1_not_D
            rw [mem_compIn_iff]
            refine ⟨hy1_Uab, p1.append p2.reverse, fun w hw ↦ ?_⟩
            rw [Walk.support_append] at hw
            rcases List.mem_append.mp hw with hw1 | hw2
            · exact hp1 w hw1
            · have hw2' := List.mem_of_mem_tail hw2
              rw [Walk.support_reverse, List.mem_reverse] at hw2'
              exact hp2 w hw2'
          have hcard_Qy : 2 ≤ (compIn G U_ab y1).card := by
            have hy1_m : y1 ∈ compIn G U_ab y1 := self_mem_compIn hy1_Uab
            have hy2_m : y2 ∈ compIn G U_ab y1 := by
              rw [mem_compIn_iff]
              refine ⟨hy2_Uab, .cons hadj_y12 .nil, ?_⟩
              simp only [Walk.support_cons, Walk.support_nil, List.mem_cons,
                List.not_mem_nil, or_false]
              rintro w (rfl | rfl)
              · exact hy1_Uab
              · exact hy2_Uab
            have hsub_p : ({y1, y2} : Finset V) ⊆ compIn G U_ab y1 := by
              intro z hz
              simp only [Finset.mem_insert, Finset.mem_singleton] at hz
              rcases hz with rfl | rfl <;> assumption
            have hc_p := Finset.card_le_card hsub_p
            rw [Finset.card_pair (G.ne_of_adj hadj_y12)] at hc_p
            exact hc_p
          exact no_two_large_comps hno_mod3 h2G hdeg hcab_ne hd0_Uab hy1_Uab
            hdisj_D_Qy (by rw [hD_eq_Uab]; exact hD2) hcard_Qy
        · -- `D.card = 1`: `D = {d0}`, `d0 ≠ r`, so `G.neighborFinset d0 ⊆ ND` gives `3 ≤ ND.card`!
          have hD1 : D.card = 1 := by
            have := Finset.card_pos.mpr ⟨d0, hd0D⟩; omega
          obtain ⟨d_only, hd_eq⟩ := Finset.card_eq_one.mp hD1
          have hd0_eq : d0 = d_only := Finset.mem_singleton.mp (hd_eq ▸ hd0D)
          subst d_only
          have hsub_nb : G.neighborFinset d0 ⊆ ND := by
            intro w hw
            have hadj_dw := (G.mem_neighborFinset _ _).mp hw
            have hw_not_D : w ∉ D := by
              rw [hd_eq, Finset.mem_singleton]
              exact (G.ne_of_adj hadj_dw).symm
            exact Finset.mem_filter.mpr ⟨hbdy_D d0 hd0D w hw_not_D hadj_dw, d0, hd0D, hadj_dw⟩
          have hc1 := Finset.card_le_card hsub_nb
          rw [card_neighborFinset_eq_degree] at hc1
          have hc2 := hdeg d0 (fun h ↦ hr_not_D (h ▸ hd0D))
          omega
      -- Now `3 ≤ ND.card`! Also `R0` has an exit neighbor `z ∈ Vc`!
      have hex_z : ∃ z ∈ Vc, ∃ r' ∈ R0, G.Adj r' z := by
        have hc0_not_R0 : c 0 ∉ R0 :=
          fun hm ↦ (Finset.mem_sdiff.mp (compIn_subset hm)).2 (hc_mem_Vc 0)
        obtain ⟨p⟩ := hG_conn r (c 0)
        obtain ⟨r', hr'R0, z, hz_not_R0, hadj_rz, _, _, _⟩ :=
          first_exit R0 hr_R0 hc0_not_R0 p
        have hz_Vc : z ∈ Vc := by
          by_contra hz_not_Vc
          exact compIn_no_edge_out hr'R0 (Finset.mem_sdiff.mpr ⟨Finset.mem_univ z, hz_not_Vc⟩)
            hz_not_R0 hadj_rz
        exact ⟨z, hz_Vc, r', hr'R0, hadj_rz⟩
      rcases hex_z with ⟨z, hz_Vc, r', hr'R0, hadj_r'z⟩
      obtain ⟨tz, htz_m, hctz⟩ := (hC_supp z).mp (List.mem_toFinset.mp hz_Vc)
      -- Pull `ND` back to indices in `Finset.range m` and pick `i0 < i1 < i2 < m`.
      set idxND := (Finset.range m).filter (fun i ↦ c i ∈ ND)
      have hND_sub_img : ND ⊆ idxND.image c := by
        intro w hw
        have hw_Vc : w ∈ Vc := (Finset.mem_filter.mp hw).1
        obtain ⟨i, hi, rfl⟩ := (hC_supp w).mp (List.mem_toFinset.mp hw_Vc)
        exact Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hi, hw⟩, rfl⟩
      have hidx_card : 3 ≤ idxND.card :=
        (hND_card3.trans (Finset.card_le_card hND_sub_img)).trans Finset.card_image_le
      obtain ⟨i0, i1, i2, hi0_m, hi1_m, hi2_m, hi01, hi12, hi2_lt⟩ :=
        sort_three_lt hidx_card (fun i hi ↦ Finset.mem_range.mp (Finset.mem_filter.mp hi).1)
      have hci0_ND : c i0 ∈ ND := (Finset.mem_filter.mp hi0_m).2
      have hci1_ND : c i1 ∈ ND := (Finset.mem_filter.mp hi1_m).2
      have hci2_ND : c i2 ∈ ND := (Finset.mem_filter.mp hi2_m).2
      -- Find an arc `A_arc : G.Walk xa xb` between two vertices `xa ≠ xb` of `ND` inside `Vc \ {z}`!
      have hex_arc : ∃ (xa xb : V), xa ∈ ND ∧ xb ∈ ND ∧ xa ≠ xb ∧
          ∃ A_arc : G.Walk xa xb, A_arc.IsPath ∧
            ∀ w ∈ A_arc.support, w ∈ Vc ∧ w ≠ z := by
        by_cases htz0 : tz ≤ i0
        · -- Use `A12` from `c i1` to `c i2`!
          have h12_eq : i1 + (i2 - i1) = i2 := by omega
          set a0 : G.Walk (c i1) (c (i1 + (i2 - i1))) := cArc hc i1 (i2 - i1)
          set A_arc : G.Walk (c i1) (c i2) := a0.copy rfl (congrArg c h12_eq)
          refine ⟨c i1, c i2, hci1_ND, hci2_ND,
            fun h ↦ (Nat.ne_of_lt hi12) (hc.inj (by omega) hi2_lt h),
            A_arc, (Walk.isPath_copy _ _ _).mpr (cArc_isPath hc i1 (by omega)), ?_⟩
          intro w hw
          rw [Walk.support_copy, mem_cArc_support] at hw
          rcases hw with ⟨t, ht, rfl⟩
          refine ⟨hc_mem_Vc _, fun h_eq ↦ ?_⟩
          rw [← hctz] at h_eq
          have := hc.inj (by omega) htz_m h_eq
          omega
        · by_cases htz1 : tz ≤ i1
          · -- `i0 < tz ≤ i1`: use `A20` from `c i2` to `c i0`!
            have h20_eq : c (i2 + (m + i0 - i2)) = c i0 := by
              have : i2 + (m + i0 - i2) = i0 + m := by omega
              rw [this, hc.per]
            set a0 : G.Walk (c i2) (c (i2 + (m + i0 - i2))) := cArc hc i2 (m + i0 - i2)
            set A_arc : G.Walk (c i2) (c i0) := a0.copy rfl h20_eq
            refine ⟨c i2, c i0, hci2_ND, hci0_ND,
              fun h ↦ (Nat.ne_of_lt (hi01.trans hi12)).symm (hc.inj hi2_lt (by omega) h),
              A_arc, (Walk.isPath_copy _ _ _).mpr (cArc_isPath hc i2 (by omega)), ?_⟩
            intro w hw
            rw [Walk.support_copy, mem_cArc_support] at hw
            rcases hw with ⟨t, ht, rfl⟩
            refine ⟨hc_mem_Vc _, fun h_eq ↦ ?_⟩
            rw [← hctz] at h_eq
            have := eq_of_mod_eq_of_lt_add (m := m) (a := tz) (b := i2 + t)
              (by omega) (by omega) (hc.eq_iff.mp h_eq.symm)
            omega
          · -- `i1 < tz < m`: use `A01` from `c i0` to `c i1`!
            have h01_eq : i0 + (i1 - i0) = i1 := by omega
            set a0 : G.Walk (c i0) (c (i0 + (i1 - i0))) := cArc hc i0 (i1 - i0)
            set A_arc : G.Walk (c i0) (c i1) := a0.copy rfl (congrArg c h01_eq)
            refine ⟨c i0, c i1, hci0_ND, hci1_ND,
              fun h ↦ (Nat.ne_of_lt hi01) (hc.inj (by omega) (by omega) h),
              A_arc, (Walk.isPath_copy _ _ _).mpr (cArc_isPath hc i0 (by omega)), ?_⟩
            intro w hw
            rw [Walk.support_copy, mem_cArc_support] at hw
            rcases hw with ⟨t, ht, rfl⟩
            refine ⟨hc_mem_Vc _, fun h_eq ↦ ?_⟩
            rw [← hctz] at h_eq
            have := hc.inj (by omega) htz_m h_eq
            omega
      rcases hex_arc with ⟨xa, xb, hxa_ND, hxb_ND, hxab, A_arc, hA_path, hA_supp⟩
      rcases (Finset.mem_filter.mp hxa_ND).2 with ⟨da, hdaD, hadj_da⟩
      rcases (Finset.mem_filter.mp hxb_ND).2 with ⟨db, hdbD, hadj_db⟩
      -- Connect `da` to `db` by a simple path inside `D`!
      have hD_conn := connected_induce_compIn (G := G) hd0U
      obtain ⟨pD_raw⟩ := hD_conn.preconnected ⟨da, hdaD⟩ ⟨db, hdbD⟩
      set pD_sub := pD_raw.toPath
      set pD : G.Walk da db := liftWalk pD_sub.1
      have hpD_path : pD.IsPath := isPath_liftWalk pD_sub.2
      have hpD_D : ∀ w ∈ pD.support, w ∈ D :=
        fun w hw ↦ Finset.mem_coe.mp (support_liftWalk_subset pD_sub.1 w hw)
      have hxb_not_pD : xb ∉ pD.support :=
        fun hm ↦ Finset.disjoint_left.mp hdisj_D_Vc (hpD_D xb hm) (Finset.mem_filter.mp hxb_ND).1
      have hpD_xb_path : (pD.append (.cons hadj_db .nil)).IsPath := by
        apply append_isPath hpD_path
          (Walk.IsPath.cons Walk.IsPath.nil (by simp [G.ne_of_adj hadj_db]))
        intro w hw1 hw2
        simp only [Walk.support_cons, Walk.support_nil, List.mem_cons,
          List.not_mem_nil, or_false] at hw2
        rcases hw2 with rfl | rfl
        · rfl
        · exact (hxb_not_pD hw1).elim
      have hxa_not_pDxb : xa ∉ (pD.append (.cons hadj_db .nil)).support := by
        intro hm
        rw [Walk.support_append] at hm
        simp only [Walk.support_cons, Walk.support_nil, List.tail_cons, List.mem_append,
          List.mem_singleton] at hm
        rcases hm with hm1 | h_eq
        · exact Finset.disjoint_left.mp hdisj_D_Vc (hpD_D xa hm1) (Finset.mem_filter.mp hxa_ND).1
        · exact hxab h_eq
      set qD : G.Walk xa xb := .cons hadj_da.symm (pD.append (.cons hadj_db .nil))
      have hqD_path : qD.IsPath := Walk.IsPath.cons hpD_xb_path hxa_not_pDxb
      have hqD_len : 2 ≤ qD.length := by
        simp [qD, Walk.length_append]
      -- Combine `A_arc` and `qD.reverse` into a simple cycle `C_new`!
      have hdisj_tails : A_arc.support.tail.Disjoint qD.reverse.support.tail := by
        rw [List.disjoint_left]
        intro w hwA hwQ
        have hndA := hA_path.support_nodup
        rw [support_eq_cons_tail A_arc, List.nodup_cons] at hndA
        have hndQ := hqD_path.reverse.support_nodup
        rw [support_eq_cons_tail qD.reverse, List.nodup_cons] at hndQ
        have hw_ne_xa : w ≠ xa := fun h ↦ hndA.1 (h ▸ hwA)
        have hw_ne_xb : w ≠ xb := fun h ↦ hndQ.1 (h ▸ hwQ)
        have hw_Vc : w ∈ Vc := (hA_supp w (List.mem_of_mem_tail hwA)).1
        have hw_qD : w ∈ qD.support := by
          have hm := List.mem_of_mem_tail hwQ
          rwa [Walk.support_reverse, List.mem_reverse] at hm
        simp only [qD, Walk.support_cons, Walk.support_append, Walk.support_nil, List.tail_cons,
          List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hw_qD
        rcases hw_qD with rfl | hw_pD | rfl
        · exact hw_ne_xa rfl
        · exact Finset.disjoint_left.mp hdisj_D_Vc (hpD_D w hw_pD) hw_Vc
        · exact hw_ne_xb rfl
      set C_new : G.Walk xa xa := A_arc.append qD.reverse
      have hC_new : C_new.IsCycle :=
        hA_path.isCycle_append hqD_path.reverse hdisj_tails
          (Or.inr (by rw [Walk.length_reverse]; omega))
      have hCnew_supp : ∀ w ∈ C_new.support, (w ∈ Vc ∧ w ≠ z) ∨ w ∈ D := by
        intro w hw
        rw [Walk.support_append] at hw
        rcases List.mem_append.mp hw with hw1 | hw2
        · exact Or.inl (hA_supp w hw1)
        · have hwQ := List.mem_of_mem_tail hw2
          rw [Walk.support_reverse, List.mem_reverse] at hwQ
          simp only [qD, Walk.support_cons, Walk.support_append, Walk.support_nil, List.tail_cons,
            List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hwQ
          rcases hwQ with hw_xa | hw_pD | hw_xb
          · rw [hw_xa]; exact Or.inl (hA_supp xa (Walk.start_mem_support A_arc))
          · exact Or.inr (hpD_D w hw_pD)
          · rw [hw_xb]; exact Or.inl (hA_supp xb (Walk.end_mem_support A_arc))
      have hr_not_Cnew : r ∉ C_new.support := by
        intro hm
        rcases hCnew_supp r hm with ⟨hrVc, _⟩ | hrD
        · exact hr_not_Vc hrVc
        · exact hr_not_D hrD
      set U_new := Finset.univ \ C_new.support.toFinset
      have hR0_Unew : R0 ⊆ U_new := by
        intro w hwR0
        rw [Finset.mem_sdiff]
        refine ⟨Finset.mem_univ w, fun hm ↦ ?_⟩
        rcases hCnew_supp w (List.mem_toFinset.mp hm) with ⟨hwVc, _⟩ | hwD
        · exact (Finset.mem_sdiff.mp (compIn_subset hwR0)).2 hwVc
        · exact Finset.disjoint_right.mp hdisj_D_R0 hwR0 hwD
      have hz_Unew : z ∈ U_new := by
        rw [Finset.mem_sdiff]
        refine ⟨Finset.mem_univ z, fun hm ↦ ?_⟩
        rcases hCnew_supp z (List.mem_toFinset.mp hm) with ⟨_, hznz⟩ | hzD
        · exact hznz rfl
        · exact Finset.disjoint_left.mp hdisj_D_Vc hzD hz_Vc
      have hins_sub : insert z R0 ⊆ compIn G U_new r := by
        intro w hw
        rcases Finset.mem_insert.mp hw with rfl | hwR0
        · rcases mem_compIn_iff.mp hr'R0 with ⟨_, pr', hpr'⟩
          have hr'_R0_walk := walk_in_U_stays_in_compIn hr_R0 pr' hpr'
          rw [mem_compIn_iff]
          refine ⟨hz_Unew, pr'.append (.cons hadj_r'z .nil), fun t ht ↦ ?_⟩
          rw [Walk.support_append] at ht
          simp only [Walk.support_cons, Walk.support_nil, List.tail_cons, List.mem_append,
            List.mem_singleton] at ht
          rcases ht with ht1 | rfl
          · exact hR0_Unew (hr'_R0_walk t ht1)
          · exact hz_Unew
        · rcases mem_compIn_iff.mp hwR0 with ⟨_, pw, hpw⟩
          have hpw_R0 := walk_in_U_stays_in_compIn hr_R0 pw hpw
          exact mem_compIn_iff.mpr ⟨hR0_Unew hwR0, pw, fun t ht ↦ hR0_Unew (hpw_R0 t ht)⟩
      have hz_not_R0 : z ∉ R0 :=
        fun hm ↦ (Finset.mem_sdiff.mp (compIn_subset hm)).2 hz_Vc
      have hcard_gt : R0.card + 1 ≤ (compIn G U_new r).card := by
        have hc := Finset.card_le_card hins_sub
        rwa [Finset.card_insert_of_notMem hz_not_R0] at hc
      have hle_sc := score_le_max C_new hC_new hr_not_Cnew
      dsimp only [scoreOf] at hle_sc
      change (compIn G U_new r).card * (M0 + 1) + (M0 - C_new.length) ≤
        R0.card * (M0 + 1) + (M0 - m) at hle_sc
      have hsub_le : M0 - m ≤ M0 := Nat.sub_le _ _
      nlinarith
    -- Step 2.5c: `(G.induce (U : Set V)).Connected` (`U = R0`), take spanning tree `T`, apply `cycle_tree_mod3`!
    have hU_conn : (G.induce (U : Set V)).Connected := by
      rw [hU_eq_R0]
      exact connected_induce_compIn (G := G) hrU
    obtain ⟨T, hT_le, hT_tree⟩ := hU_conn.exists_isTree_le
    have hTG : ∀ x y : {w : V // w ∈ (U : Set V)}, T.Adj x y → G.Adj x.1 y.1 :=
      fun x y hxy ↦ induce_adj_val (hT_le hxy)
    have hc_not_U : ∀ i : ℕ, c i ∉ U :=
      fun i hm ↦ (Finset.mem_sdiff.mp hm).2 (hc_mem_Vc i)
    let u_fn : ℕ → {w : V // w ∈ (U : Set V)} := fun i ↦
      if hi : i < m then
        ⟨(hex_nb_U i hi).choose, Finset.mem_coe.mpr (hex_nb_U i hi).choose_spec.1⟩
      else ⟨r, Finset.mem_coe.mpr hrU⟩
    have hu_adj : ∀ i : ℕ, i < m → G.Adj (c i) (u_fn i).1 := by
      intro i hi
      dsimp only [u_fn]
      rw [dif_pos hi]
      exact (hex_nb_U i hi).choose_spec.2
    exact hno_mod3 (cycle_tree_mod3 G hm5 hm_mod3 hc hc_not_U hT_tree hTG u_fn hu_adj)

end DeanThreeProof

theorem OMA.solution : type_of% @Arxiv.«2605.02731».dean_conjecture.variants.three := by
  intro V _ _ G _ hG
  cases isEmpty_or_nonempty V
  · simp at hG
  · rename_i hne
    obtain ⟨v0⟩ := hne
    rw [DeanThreeProof.hasMod3Cycle_iff_cycleLengths]
    set C0 := DeanThreeProof.compIn G Finset.univ v0
    have hv0_C0 : v0 ∈ C0 := DeanThreeProof.self_mem_compIn (Finset.mem_univ v0)
    have hdeg_C0 : ∀ u : {w : V // w ∈ (C0 : Set V)},
        3 ≤ (G.induce (C0 : Set V)).degree u := by
      intro u
      have hu_C0 : u.1 ∈ C0 := Finset.mem_coe.mp u.2
      have hdeg_eq : (G.induce (C0 : Set V)).degree u = G.degree u.1 := by
        rw [← SimpleGraph.card_neighborFinset_eq_degree,
          ← SimpleGraph.card_neighborFinset_eq_degree]
        apply Finset.card_bij (fun (w : {x : V // x ∈ (C0 : Set V)}) _ ↦ w.1)
        · intro w hw
          rw [SimpleGraph.mem_neighborFinset] at hw
          rw [SimpleGraph.mem_neighborFinset]
          exact hw
        · intro w1 _ w2 _ heq
          exact Subtype.ext heq
        · intro w hw
          rw [SimpleGraph.mem_neighborFinset] at hw
          have hw_C0 : w ∈ C0 := by
            by_contra hw_not
            exact DeanThreeProof.compIn_no_edge_out hu_C0 (Finset.mem_univ w) hw_not hw
          exact ⟨⟨w, Finset.mem_coe.mpr hw_C0⟩,
            (SimpleGraph.mem_neighborFinset _ _ _).mpr hw, rfl⟩
      rw [hdeg_eq]
      exact hG.trans (G.minDegree_le_degree u.1)
    have hcard_C0 : 4 ≤ Fintype.card (C0 : Set V) := by
      have hlt := (G.induce (C0 : Set V)).degree_lt_card_verts
        ⟨v0, Finset.mem_coe.mpr hv0_C0⟩
      have h3 := hdeg_C0 ⟨v0, Finset.mem_coe.mpr hv0_C0⟩
      omega
    have hconn_C0 : (G.induce (C0 : Set V)).Connected :=
      DeanThreeProof.connected_induce_compIn (G := G) (Finset.mem_univ v0)
    have hmod3_sub := DeanThreeProof.one_deficient _ (G.induce (C0 : Set V))
      ⟨v0, Finset.mem_coe.mpr hv0_C0⟩ rfl (by omega) hconn_C0 (fun u _ ↦ hdeg_C0 u)
    exact DeanThreeProof.HasMod3Cycle.of_embedding (SimpleGraph.Embedding.induce (C0 : Set V))
      hmod3_sub
