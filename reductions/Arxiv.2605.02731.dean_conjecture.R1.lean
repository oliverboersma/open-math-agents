import FormalConjectures.Arxiv.«2605.02731».DeanCycles

/-!
# Reduction of Dean's conjecture to rooted admissible paths and weak graphs

The separator argument adapts Section 4.1 of Luo, Ma and Zhao, arXiv:2601.13552.
The modulus-three proof is from Pedro Bessa and the authors of open-math-agents PR #4983
(dc5b1aec), following Chen and Saito. The modulus-four proof is from Michael Bisbjerg
and the authors of open-math-agents PR #4281 (819265c6).

The two-path Menger theorem and walk splitting lemmas are from Volkopat's Babai proof,
open-math-agents PR #4047 (6386e400). The odd-cycle extraction is from the formalization
of Li's obligatory triple systems classification by Chad Mazzola and the authors of
open-math-agents PR #6715 (428b4626).
-/


/-
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

private def HasMod3Cycle {V : Type*} (G : SimpleGraph V) : Prop :=
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

private def addEdge {W : Type*} (G : SimpleGraph W) (x y : W) : SimpleGraph W where
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

private instance instDecidableRelAddEdge {W : Type*} [DecidableEq W] (G : SimpleGraph W)
    [DecidableRel G.Adj] (x y : W) : DecidableRel (addEdge G x y).Adj :=
  fun a b ↦ inferInstanceAs (Decidable (G.Adj a b ∨ _))

lemma le_addEdge {W : Type*} (G : SimpleGraph W) (x y : W) : G ≤ addEdge G x y :=
  fun _ _ h ↦ Or.inl h

lemma addEdge_adj_self {W : Type*} (G : SimpleGraph W) {x y : W} (hxy : x ≠ y) :
    (addEdge G x y).Adj x y :=
  Or.inr ⟨hxy, Or.inl ⟨rfl, rfl⟩⟩

private def delEdge {W : Type*} (G : SimpleGraph W) (x y : W) : SimpleGraph W where
  Adj a b := G.Adj a b ∧ ¬((a = x ∧ b = y) ∨ (a = y ∧ b = x))
  symm := ⟨fun _ _ h ↦ ⟨h.1.symm, by tauto⟩⟩
  loopless := ⟨fun a h ↦ G.ne_of_adj h.1 rfl⟩

private instance instDecidableRelDelEdge {W : Type*} [DecidableEq W] (G : SimpleGraph W)
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

private def IsTwoConn {W : Type*} (G : SimpleGraph W) : Prop :=
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

private def liftWalk {W : Type*} {G : SimpleGraph W} {U : Set W} :
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

private def pushWalk {W : Type*} {G : SimpleGraph W} {U : Set W} :
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
private noncomputable def compIn {W : Type*} [Fintype W] [DecidableEq W] (G : SimpleGraph W)
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
private def contractOne {W : Type*} (G : SimpleGraph W) (A X : Finset W) :
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

private noncomputable instance instDecidableRelContractOne {W : Type*} (G : SimpleGraph W)
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
private def contractTwo {W : Type*} (G : SimpleGraph W) (Q X0 X1 : Finset W) :
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

private noncomputable instance instDecidableRelContractTwo {W : Type*} (G : SimpleGraph W)
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

private noncomputable def uPath {U : Type*} {T : SimpleGraph U} (hT : T.IsTree) (a b : U) : T.Walk a b :=
  (hT.existsUnique_path a b).choose

lemma uPath_isPath {U : Type*} {T : SimpleGraph U} (hT : T.IsTree) (a b : U) :
    (uPath hT a b).IsPath :=
  (hT.existsUnique_path a b).choose_spec.1

lemma eq_uPath_of_isPath {U : Type*} {T : SimpleGraph U} (hT : T.IsTree) {a b : U}
    {p : T.Walk a b} (hp : p.IsPath) : p = uPath hT a b :=
  (hT.existsUnique_path a b).choose_spec.2 p hp

private noncomputable def tDist {U : Type*} {T : SimpleGraph U} (hT : T.IsTree) (a b : U) : ℕ :=
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

private structure IsCyclicSeq {V : Type*} (G : SimpleGraph V) (m : ℕ) (c : ℕ → V) : Prop where
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

private def cArc {V : Type*} {G : SimpleGraph V} {m : ℕ} {c : ℕ → V} (hc : IsCyclicSeq G m c)
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

private def mapSubWalk {V : Type*} {G : SimpleGraph V} {H : Finset V}
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

private def wVert {V : Type*} {G : SimpleGraph V} : ∀ {u v : V}, G.Walk u v → ℕ → V
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

private theorem deanThree : type_of% @Arxiv.«2605.02731».dean_conjecture.variants.three := by
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

-- Problem: Dean's conjecture on cycles of length divisible by `k` — four
-- Upstream: formal-conjectures FormalConjectures/Arxiv/2605.02731/DeanCycles.lean:79 (declaration Arxiv.«2605.02731».dean_conjecture.variants.four)
-- Credit: @LordMike (the owner of the agent is credited as the solver)

/-
Team skeleton for Arxiv.2605.02731.dean_conjecture.variants.four
(min degree >= 4 implies a cycle of length divisible by 4).
Route: .oma/scratch/dean4/adv2/ROUTE.md (max cut, suppress degree-2 vertices,
weighted parity lemma, lift).  Each lemma below is assigned to one agent.
Do not change any definition or lemma statement; prove only your own lemma.
-/

namespace OMA.Dean4

open SimpleGraph Classical

variable {V : Type} [Fintype V] [DecidableEq V]

/-- Weight of a walk: sum of `wt` over its darts. -/
private noncomputable def walkWt {G : SimpleGraph V} {R : Type} [AddCommMonoid R] (wt : V → V → R)
    {u v : V} (p : G.Walk u v) : R :=
  (p.darts.map (fun d => wt d.fst d.snd)).sum

/- ## L1 + L2: maximum cut (agent L12) -/

/-- Number of neighbours of `v` on the other side of the cut `c`. -/
private noncomputable def opp (G : SimpleGraph V) (c : V → Bool) (v : V) : ℕ :=
  ((Finset.univ.filter (fun w => G.Adj v w)).filter (fun w => c w ≠ c v)).card

/-- Number of neighbours of `v` on the same side of the cut `c`. -/
private noncomputable def same (G : SimpleGraph V) (c : V → Bool) (v : V) : ℕ :=
  ((Finset.univ.filter (fun w => G.Adj v w)).filter (fun w => c w = c v)).card

/-- The bipartite subgraph of cut edges. -/
private def cutGraph (G : SimpleGraph V) (c : V → Bool) : SimpleGraph V where
  Adj v w := G.Adj v w ∧ c v ≠ c w
  symm := ⟨fun _ _ h => ⟨h.1.symm, fun e => h.2 e.symm⟩⟩
  loopless := ⟨fun _ h => h.1.ne rfl⟩

theorem opp_eq_sum (G : SimpleGraph V) (c : V → Bool) (v : V) :
    opp G c v = ∑ u, if G.Adj v u ∧ c u ≠ c v then 1 else 0 := by
  unfold opp
  rw [Finset.filter_filter, Finset.card_filter]

theorem same_eq_sum (G : SimpleGraph V) (c : V → Bool) (v : V) :
    same G c v = ∑ u, if G.Adj v u ∧ c u = c v then 1 else 0 := by
  unfold same
  rw [Finset.filter_filter, Finset.card_filter]

theorem sum_flip_aux {W : Type} [Fintype W] [DecidableEq W] (g g' : W → ℕ) (x : W)
    (h : ∀ u, u ≠ x → g' u = g u) :
    ∑ u, g' u + g x = ∑ u, g u + g' x := by
  rw [← Finset.add_sum_erase Finset.univ g' (Finset.mem_univ x),
    ← Finset.add_sum_erase Finset.univ g (Finset.mem_univ x)]
  have hs : ∑ u ∈ Finset.univ.erase x, g' u = ∑ u ∈ Finset.univ.erase x, g u :=
    Finset.sum_congr rfl (fun u hu => h u (Finset.ne_of_mem_erase hu))
  omega

/-- Total of the opposite-side degrees (twice the number of cut edges). -/
private noncomputable def tot (G : SimpleGraph V) (c : V → Bool) : ℕ := ∑ v, opp G c v

/-- Flipping the colour of `x` changes `opp` at a vertex `w ≠ x` as expected. -/
theorem opp_flip_vertex (G : SimpleGraph V) (c c' : V → Bool) (x w : V)
    (hc : ∀ u, u ≠ x → c' u = c u) (hw : w ≠ x) :
    opp G c' w + (if G.Adj w x ∧ c x ≠ c w then 1 else 0) =
      opp G c w + (if G.Adj w x ∧ c' x ≠ c w then 1 else 0) := by
  have hcw : c' w = c w := hc w hw
  have := sum_flip_aux (fun u => if G.Adj w u ∧ c u ≠ c w then 1 else 0)
    (fun u => if G.Adj w u ∧ c' u ≠ c' w then 1 else 0) x
    (fun u hu => by simp only [hc u hu, hcw])
  simp only [hcw] at this
  rw [opp_eq_sum, opp_eq_sum, hcw]
  omega

/-- Flipping the colour of `x` changes `same` at a vertex `w ≠ x` as expected. -/
theorem same_flip_vertex (G : SimpleGraph V) (c c' : V → Bool) (x w : V)
    (hc : ∀ u, u ≠ x → c' u = c u) (hw : w ≠ x) :
    same G c' w + (if G.Adj w x ∧ c x = c w then 1 else 0) =
      same G c w + (if G.Adj w x ∧ c' x = c w then 1 else 0) := by
  have hcw : c' w = c w := hc w hw
  have := sum_flip_aux (fun u => if G.Adj w u ∧ c u = c w then 1 else 0)
    (fun u => if G.Adj w u ∧ c' u = c' w then 1 else 0) x
    (fun u hu => by simp only [hc u hu, hcw])
  simp only [hcw] at this
  rw [same_eq_sum, same_eq_sum, hcw]
  omega

/-- Total effect of flipping the colour of `x`. -/
theorem tot_flip (G : SimpleGraph V) (c c' : V → Bool) (x : V)
    (hc : ∀ u, u ≠ x → c' u = c u) (hx : c' x = !c x) :
    tot G c' + 2 * opp G c x = tot G c + 2 * same G c x := by
  have hrow : opp G c' x = same G c x := by
    rw [opp_eq_sum, same_eq_sum]
    apply Finset.sum_congr rfl
    intro u _
    by_cases hu : u = x
    · subst hu; simp
    · rw [hc u hu, hx]
      by_cases hadj : G.Adj x u
      · cases c u <;> cases c x <;> simp [hadj]
      · simp [hadj]
  have hS : ∑ w ∈ Finset.univ.erase x, opp G c' w +
      ∑ w ∈ Finset.univ.erase x, (if G.Adj w x ∧ c x ≠ c w then 1 else 0) =
      ∑ w ∈ Finset.univ.erase x, opp G c w +
      ∑ w ∈ Finset.univ.erase x, (if G.Adj w x ∧ c' x ≠ c w then 1 else 0) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun w hw => by
      have := opp_flip_vertex G c c' x w hc (Finset.ne_of_mem_erase hw)
      omega)
  have e1 : ∑ w ∈ Finset.univ.erase x, (if G.Adj w x ∧ c x ≠ c w then 1 else 0) =
      opp G c x := by
    rw [Finset.sum_erase _ (by simp), opp_eq_sum]
    apply Finset.sum_congr rfl
    intro u _
    simp [G.adj_comm, eq_comm]
  have e2 : ∑ w ∈ Finset.univ.erase x, (if G.Adj w x ∧ c' x ≠ c w then 1 else 0) =
      same G c x := by
    rw [Finset.sum_erase _ (by simp), same_eq_sum]
    apply Finset.sum_congr rfl
    intro u _
    rw [G.adj_comm, hx]
    cases c u <;> cases c x <;> simp
  have hT' : tot G c' = opp G c' x + ∑ w ∈ Finset.univ.erase x, opp G c' w := by
    unfold tot
    exact (Finset.add_sum_erase _ _ (Finset.mem_univ x)).symm
  have hT : tot G c = opp G c x + ∑ w ∈ Finset.univ.erase x, opp G c w := by
    unfold tot
    exact (Finset.add_sum_erase _ _ (Finset.mem_univ x)).symm
  omega

/-- If `c` maximises `tot`, then `same v <= opp v` for every `v`. -/
theorem max_same_le (G : SimpleGraph V) (c : V → Bool)
    (hmax : ∀ d : V → Bool, tot G d ≤ tot G c) (v : V) :
    same G c v ≤ opp G c v := by
  have hx : (Function.update c v (!c v)) v = !c v := Function.update_self _ _ _
  have h := tot_flip G c (Function.update c v (!c v)) v
    (fun u hu => Function.update_of_ne hu _ _) hx
  have := hmax (Function.update c v (!c v))
  omega

/-- If `c` maximises `tot`, then the neighbour condition (M2) holds. -/
theorem max_nbr (G : SimpleGraph V) (c : V → Bool)
    (hmax : ∀ d : V → Bool, tot G d ≤ tot G c) (v w : V)
    (hv : same G c v = opp G c v) (hadj : G.Adj v w) (hwc : c w ≠ c v) :
    same G c w + 2 ≤ opp G c w := by
  have hx : (Function.update c v (!c v)) v = !c v := Function.update_self _ _ _
  have hc : ∀ u, u ≠ v → Function.update c v (!c v) u = c u :=
    fun u hu => Function.update_of_ne hu _ _
  have h := tot_flip G c (Function.update c v (!c v)) v hc hx
  have hT : tot G (Function.update c v (!c v)) = tot G c := by omega
  have hmax' : ∀ d : V → Bool, tot G d ≤ tot G (Function.update c v (!c v)) := by
    intro d
    rw [hT]
    exact hmax d
  have hM1 := max_same_le G (Function.update c v (!c v)) hmax' w
  have hw : w ≠ v := hadj.ne.symm
  have ho := opp_flip_vertex G c (Function.update c v (!c v)) v w hc hw
  have hs := same_flip_vertex G c (Function.update c v (!c v)) v w hc hw
  have hcw : c w = !c v := by
    cases h1 : c v <;> cases h2 : c w <;> simp_all
  have hne : c v ≠ c w := by
    rw [hcw]
    cases c v <;> simp
  have i1 : (if G.Adj w v ∧ c v ≠ c w then 1 else 0) = 1 := if_pos ⟨hadj.symm, hne⟩
  have i2 : (if G.Adj w v ∧ (Function.update c v (!c v)) v ≠ c w then 1 else 0) = 0 :=
    if_neg (fun h => h.2 (by rw [hx, hcw]))
  have i3 : (if G.Adj w v ∧ c v = c w then 1 else 0) = 0 := if_neg (fun h => hne h.2)
  have i4 : (if G.Adj w v ∧ (Function.update c v (!c v)) v = c w then 1 else 0) = 1 :=
    if_pos ⟨hadj.symm, by rw [hx, hcw]⟩
  rw [i1, i2] at ho
  rw [i3, i4] at hs
  omega

/-- L1: a locally optimal (maximum) cut. -/
theorem L1_maxcut (G : SimpleGraph V) :
    ∃ c : V → Bool, (∀ v, same G c v ≤ opp G c v) ∧
      (∀ v w, same G c v = opp G c v → G.Adj v w → c w ≠ c v →
        same G c w + 2 ≤ opp G c w) := by
  obtain ⟨c, -, hmax⟩ := Finset.exists_max_image (Finset.univ : Finset (V → Bool)) (tot G)
    ⟨fun _ => true, Finset.mem_univ _⟩
  have hmax' : ∀ d : V → Bool, tot G d ≤ tot G c := fun d => hmax d (Finset.mem_univ d)
  exact ⟨c, fun v => max_same_le G c hmax' v,
    fun v w hv hadj hwc => max_nbr G c hmax' v w hv hadj hwc⟩

/-- L2: degrees in the cut graph; the only place where `4 ≤ minDegree` is used. -/
theorem L2_cut_degrees (G : SimpleGraph V) [DecidableRel G.Adj] (hG : 4 ≤ G.minDegree)
    (c : V → Bool) (h1 : ∀ v, same G c v ≤ opp G c v)
    (h2 : ∀ v w, same G c v = opp G c v → G.Adj v w → c w ≠ c v →
        same G c w + 2 ≤ opp G c w) :
    (∀ v, 2 ≤ (cutGraph G c).degree v) ∧
      (∀ y w, (cutGraph G c).degree y = 2 → (cutGraph G c).Adj y w →
        3 ≤ (cutGraph G c).degree w) := by
  have hdeg : ∀ v, (cutGraph G c).degree v = opp G c v := by
    intro v
    rw [← SimpleGraph.card_neighborFinset_eq_degree]
    unfold opp
    congr 1
    ext w
    rw [SimpleGraph.mem_neighborFinset]
    simp [cutGraph, ne_comm]
  have hsum : ∀ v, same G c v + opp G c v = G.degree v := by
    intro v
    have key := Finset.card_filter_add_card_filter_not (s := Finset.univ.filter (fun w => G.Adj v w))
      (fun w => c w = c v)
    rw [← SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.neighborFinset_eq_filter]
    unfold same opp
    simp only [Finset.filter_filter, ne_eq]
    convert key using 2
    all_goals (congr 1; ext a; simp)
  have hdeg4 : ∀ v, 4 ≤ G.degree v := fun v => le_trans hG (G.minDegree_le_degree v)
  refine ⟨fun v => ?_, fun y w hy hadj => ?_⟩
  · rw [hdeg v]
    have := hsum v
    have := hdeg4 v
    have := h1 v
    omega
  · have hadj' : G.Adj y w ∧ c y ≠ c w := hadj
    rw [hdeg] at hy
    rw [hdeg w]
    have hsy : same G c y = opp G c y := by
      have := hsum y
      have := hdeg4 y
      have := h1 y
      omega
    have hw := h2 y w hsy hadj'.1 (fun e => hadj'.2 e.symm)
    have := hsum w
    have := hdeg4 w
    omega

/- ## The suppressed graph K -/

/-- Join good vertices that are adjacent in `H` or share a bad `H`-neighbour. -/
private def supp (H : SimpleGraph V) (good : V → Prop) : SimpleGraph V where
  Adj v w := v ≠ w ∧ good v ∧ good w ∧ (H.Adj v w ∨ ∃ y, ¬ good y ∧ H.Adj v y ∧ H.Adj y w)
  symm := ⟨by
    rintro v w ⟨hne, hv, hw, h⟩
    refine ⟨hne.symm, hw, hv, ?_⟩
    rcases h with h | ⟨y, hy, h1, h2⟩
    · exact Or.inl h.symm
    · exact Or.inr ⟨y, hy, h2.symm, h1.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- Edge weight: 1 for an edge of `H`, 2 for a suppressed path of length 2. -/
private noncomputable def wt1 (H : SimpleGraph V) (v w : V) : ℕ := if H.Adj v w then 1 else 2

/-- L3 (agent L3): good vertices keep degree at least 3 in the suppressed graph,
given no 4-cycle in `H`. -/
theorem L3_supp_degree (H : SimpleGraph V) (c : V → Bool)
    (hc : ∀ v w, H.Adj v w → c v ≠ c w)
    (h2 : ∀ v, 2 ≤ H.degree v)
    (hbad : ∀ y w, H.degree y = 2 → H.Adj y w → 3 ≤ H.degree w)
    (hno4 : ∀ a b c' d, H.Adj a b → H.Adj b c' → H.Adj c' d → H.Adj d a →
        a ≠ c' → b ≠ d → False) :
    ∀ v, 3 ≤ H.degree v → 3 ≤ (supp H (fun x => 3 ≤ H.degree x)).degree v := by
  intro v hv
  have hb3 : ∀ a b d : Bool, a ≠ b → a ≠ d → b ≠ d → False := by decide
  have rep : ∀ y, H.Adj v y → ∃ z, z ≠ v ∧ 3 ≤ H.degree z ∧
      (supp H (fun x => 3 ≤ H.degree x)).Adj v z ∧
      (z = y ∨ (¬ 3 ≤ H.degree y ∧ H.Adj y z)) := by
    intro y hy
    by_cases hg : 3 ≤ H.degree y
    · refine ⟨y, hy.ne.symm, hg, ?_, Or.inl rfl⟩
      show v ≠ y ∧ 3 ≤ H.degree v ∧ 3 ≤ H.degree y ∧
        (H.Adj v y ∨ ∃ x, ¬ 3 ≤ H.degree x ∧ H.Adj v x ∧ H.Adj x y)
      exact ⟨hy.ne, hv, hg, Or.inl hy⟩
    · have hd : H.degree y = 2 := by
        have := h2 y
        omega
      have hcard : 1 < (H.neighborFinset y).card := by
        rw [SimpleGraph.card_neighborFinset_eq_degree, hd]; norm_num
      obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.1 hcard
      rw [SimpleGraph.mem_neighborFinset] at ha hb
      have hw : ∃ w, H.Adj y w ∧ w ≠ v := by
        by_cases hav : a = v
        · exact ⟨b, hb, fun h => hab (hav.trans h.symm)⟩
        · exact ⟨a, ha, hav⟩
      obtain ⟨w, hyw, hwv⟩ := hw
      have hwg : 3 ≤ H.degree w := hbad y w hd hyw
      refine ⟨w, hwv, hwg, ?_, Or.inr ⟨hg, hyw⟩⟩
      exact ⟨hwv.symm, hv, hwg, Or.inr ⟨y, hg, hy, hyw⟩⟩
  have key : ∀ y1 y2 z1 z2 : V, H.Adj v y1 → H.Adj v y2 → y1 ≠ y2 → z1 ≠ v → z2 ≠ v →
      (z1 = y1 ∨ (¬ 3 ≤ H.degree y1 ∧ H.Adj y1 z1)) →
      (z2 = y2 ∨ (¬ 3 ≤ H.degree y2 ∧ H.Adj y2 z2)) → z1 ≠ z2 := by
    intro y1 y2 z1 z2 k1 k2 hne hz1 hz2 r1 r2 heq
    rcases r1 with e1 | ⟨-, a1⟩ <;> rcases r2 with e2 | ⟨-, a2⟩
    · exact hne (e1.symm.trans (heq.trans e2))
    · have hz : z2 = y1 := heq.symm.trans e1
      rw [hz] at a2
      exact hb3 (c v) (c y1) (c y2) (hc v y1 k1) (hc v y2 k2) (hc y1 y2 a2.symm)
    · have hz : z1 = y2 := heq.trans e2
      rw [hz] at a1
      exact hb3 (c v) (c y1) (c y2) (hc v y1 k1) (hc v y2 k2) (hc y1 y2 a1)
    · have hcd : H.Adj z1 y2 := by rw [heq]; exact a2.symm
      exact hno4 v y1 z1 y2 k1 a1 hcd k2.symm hz1.symm hne
  have hcard : 2 < (H.neighborFinset v).card := by
    rw [SimpleGraph.card_neighborFinset_eq_degree]; omega
  obtain ⟨y1, h1, y2, h2m, y3, h3, n12, n13, n23⟩ := Finset.two_lt_card.1 hcard
  rw [SimpleGraph.mem_neighborFinset] at h1 h2m h3
  obtain ⟨z1, hz1v, -, hK1, r1⟩ := rep y1 h1
  obtain ⟨z2, hz2v, -, hK2, r2⟩ := rep y2 h2m
  obtain ⟨z3, hz3v, -, hK3, r3⟩ := rep y3 h3
  have k12 := key y1 y2 z1 z2 h1 h2m n12 hz1v hz2v r1 r2
  have k13 := key y1 y3 z1 z3 h1 h3 n13 hz1v hz3v r1 r3
  have k23 := key y2 y3 z2 z3 h2m h3 n23 hz2v hz3v r2 r3
  have hsub : 2 < ((supp H (fun x => 3 ≤ H.degree x)).neighborFinset v).card := by
    apply Finset.two_lt_card.2
    refine ⟨z1, ?_, z2, ?_, z3, ?_, k12, k13, k23⟩ <;>
      rw [SimpleGraph.mem_neighborFinset] <;> assumption
  rw [SimpleGraph.card_neighborFinset_eq_degree] at hsub
  omega

/- ## L4: Theorem W (agent L4) -/

theorem walkWt_nil' {K : SimpleGraph V} (wt : V → V → ZMod 4) (a : V) :
    walkWt wt (Walk.nil : K.Walk a a) = 0 := by
  simp [walkWt]

theorem walkWt_cons' {K : SimpleGraph V} (wt : V → V → ZMod 4) {a b c : V} (h : K.Adj a b)
    (p : K.Walk b c) : walkWt wt (Walk.cons h p) = wt a b + walkWt wt p := by
  simp [walkWt]

theorem walkWt_append' {K : SimpleGraph V} (wt : V → V → ZMod 4) {a b c : V} (p : K.Walk a b)
    (q : K.Walk b c) : walkWt wt (p.append q) = walkWt wt p + walkWt wt q := by
  simp [walkWt, Walk.darts_append]

theorem walkWt_reverse' {K : SimpleGraph V} (wt : V → V → ZMod 4)
    (hsym : ∀ x y, wt x y = wt y x) {a b : V} (p : K.Walk a b) :
    walkWt wt p.reverse = walkWt wt p := by
  induction p with
  | nil => simp [walkWt]
  | @cons a' b' c' h p ih =>
    rw [Walk.reverse_cons, walkWt_append', ih, walkWt_cons', walkWt_cons', walkWt_nil']
    linear_combination hsym b' a'

theorem path_join {K : SimpleGraph V} {a c d b : V} (p : K.Walk a c) (h : K.Adj c d)
    (q : K.Walk d b) (hp : p.IsPath) (hq : q.IsPath) (hd : ∀ w ∈ p.support, w ∉ q.support) :
    (p.append (Walk.cons h q)).IsPath := by
  rw [Walk.isPath_def, Walk.support_append, Walk.support_cons, List.tail_cons]
  exact List.Nodup.append hp.support_nodup hq.support_nodup (fun w h1 h2 => hd w h1 h2)

theorem path_split {K : SimpleGraph V} {a c d b : V} (p : K.Walk a c) (h : K.Adj c d)
    (q : K.Walk d b) (hP : (p.append (Walk.cons h q)).IsPath) :
    p.IsPath ∧ q.IsPath ∧ ∀ w ∈ p.support, w ∉ q.support := by
  rw [Walk.isPath_def, Walk.support_append, Walk.support_cons, List.tail_cons,
    List.nodup_append] at hP
  exact ⟨(Walk.isPath_def _).2 hP.1, (Walk.isPath_def _).2 hP.2.1,
    fun w h1 h2 => hP.2.2 w h1 w h2 rfl⟩

theorem path_ne {K : SimpleGraph V} {a b : V} (p : K.Walk a b) (hp : p.IsPath)
    (hl : 0 < p.length) : a ≠ b := by
  cases p with
  | nil => simp at hl
  | cons h q =>
    rw [Walk.cons_isPath_iff] at hp
    intro e
    subst e
    exact hp.2 q.end_mem_support

theorem pos_of_ne {K : SimpleGraph V} {a b : V} (p : K.Walk a b) (h : a ≠ b) :
    0 < p.length :=
  Nat.pos_of_ne_zero fun h0 => h (Walk.eq_of_length_eq_zero h0)

theorem cyc {K : SimpleGraph V} {a b : V} (p : K.Walk b a) (h : K.Adj a b) (hp : p.IsPath)
    (hl : 2 ≤ p.length) : (Walk.cons h p).IsCycle := by
  rw [Walk.cons_isCycle_iff]
  refine ⟨hp, fun he => ?_⟩
  cases p with
  | nil => simp at hl
  | cons h' p' =>
    rw [Walk.cons_isPath_iff] at hp
    rw [Walk.edges_cons, List.mem_cons] at he
    rcases he with he | he
    · rcases Sym2.eq_iff.1 he with ⟨h1, _⟩ | ⟨h1, _⟩
      · exact absurd h1 h.ne
      subst h1
      cases p' with
      | nil => simp at hl
      | cons h'' p'' =>
        rw [Walk.cons_isPath_iff] at hp
        exact hp.1.2 p''.end_mem_support
    · exact hp.2 (Walk.snd_mem_support_of_mem_edges p' he)

theorem fan {K : SimpleGraph V} (wt : V → V → ZMod 4) (hsym : ∀ x y, wt x y = wt y x)
    (hall : ∀ (v : V) (p : K.Walk v v), p.IsCycle → walkWt wt p = 2)
    {x c y w : V} (R1 : K.Walk x c) (hcy : K.Adj c y) (R2 : K.Walk y w)
    (hxy : K.Adj x y) (hxw : K.Adj x w) (h1 : R1.IsPath) (h2 : R2.IsPath)
    (hd : ∀ a ∈ R1.support, a ∉ R2.support) (l1 : 0 < R1.length) (l2 : 0 < R2.length) :
    2 * wt x y = 2 := by
  have e1 := hall _ _ (cyc (R1.append (Walk.cons hcy Walk.nil)) hxy.symm
    (path_join R1 hcy Walk.nil h1 Walk.IsPath.nil
      (fun a ha hb => hd a ha (by
        simp at hb
        subst hb
        exact R2.start_mem_support)))
    (by simp [Walk.length_append]; omega))
  have e2 := hall _ _ (cyc (R1.append (Walk.cons hcy R2)) hxw.symm
    (path_join R1 hcy R2 h1 h2 hd) (by simp [Walk.length_append]; omega))
  have e3 := hall _ _ (cyc (Walk.cons hxy R2) hxw.symm
    ((Walk.cons_isPath_iff _ _).2 ⟨h2, hd x R1.start_mem_support⟩) (by simp; omega))
  simp only [walkWt_cons', walkWt_append', walkWt_nil'] at e1 e2 e3
  linear_combination e1 + e3 - e2 - hsym y x

theorem theta {K : SimpleGraph V} (wt : V → V → ZMod 4) (hsym : ∀ x y, wt x y = wt y x)
    (hall : ∀ (v : V) (p : K.Walk v v), p.IsCycle → walkWt wt p = 2)
    {x u z t1 t2 : V} (S1 : K.Walk x u) (T : K.Walk z t1) (Q : K.Walk t1 t2)
    (huz : K.Adj u z) (hxz : K.Adj x z) (hx1 : K.Adj x t1) (hu2 : K.Adj u t2)
    (hS : S1.IsPath) (lS : 0 < S1.length) (hTQ : (T.append Q).IsPath) (lT : 0 < T.length)
    (hd : ∀ w ∈ S1.support, w ∉ (T.append Q).support) : False := by
  have hT : T.IsPath := hTQ.of_append_left
  have hQ : Q.IsPath := hTQ.of_append_right
  have hdT : ∀ w ∈ S1.support, w ∉ T.support := fun w hw h =>
    hd w hw ((Walk.mem_support_append_iff _ _).2 (Or.inl h))
  have hdQ : ∀ w ∈ S1.support, w ∉ Q.support := fun w hw h =>
    hd w hw ((Walk.mem_support_append_iff _ _).2 (Or.inr h))
  have hzQ : z ∉ Q.support := by
    intro hz
    have hn := hTQ.support_nodup
    rw [Walk.support_append] at hn
    have hzt : z ≠ t1 := path_ne T hT lT
    have hz' : z ∈ Q.support.tail := by
      rw [← Walk.cons_tail_support Q] at hz
      rcases List.mem_cons.1 hz with h | h
      · exact absurd h hzt
      · exact h
    exact (List.nodup_append.1 hn).2.2 z T.start_mem_support z hz' rfl
  have hxu : x ≠ u := path_ne S1 hS lS
  have hSr : S1.reverse.IsPath := (Walk.isPath_reverse_iff _).2 hS
  have f1 := fan wt hsym hall S1 huz T hxz hx1 hS hT hdT lS lT
  have f2 := fan wt hsym hall S1.reverse hxz (T.append Q) huz hu2 hSr hTQ
    (fun w hw => hd w (by simpa using hw)) (by simpa using lS)
    (by simp [Walk.length_append]; omega)
  have c1 := hall _ _ (cyc (S1.append (Walk.cons huz Walk.nil)) hxz.symm
    (path_join S1 huz Walk.nil hS Walk.IsPath.nil
      (fun a ha hb => hdT a ha (by
        simp at hb
        subst hb
        exact T.start_mem_support)))
    (by simp [Walk.length_append]; omega))
  have c7 := hall _ _ (cyc (Q.append (Walk.cons hu2.symm S1.reverse)) hx1
    (path_join Q hu2.symm S1.reverse hQ hSr
      (fun a ha hb => hdQ a (by simpa using hb) ha))
    (by simp [Walk.length_append]; omega))
  have hp6 : (Walk.cons huz (Walk.cons hxz.symm Walk.nil)).IsPath := by
    rw [Walk.cons_isPath_iff, Walk.cons_isPath_iff]
    refine ⟨⟨Walk.IsPath.nil, ?_⟩, ?_⟩
    · simpa using hxz.ne'
    · simpa using ⟨huz.ne, hxu.symm⟩
  have c6 := hall _ _ (cyc
    (Q.append (Walk.cons hu2.symm (Walk.cons huz (Walk.cons hxz.symm Walk.nil)))) hx1
    (path_join Q hu2.symm _ hQ hp6 (fun a ha hb => by
      simp at hb
      rcases hb with rfl | rfl | rfl
      · exact hdQ _ S1.end_mem_support ha
      · exact hzQ ha
      · exact hdQ _ S1.start_mem_support ha))
    (by simp [Walk.length_append]))
  simp only [walkWt_cons', walkWt_append', walkWt_nil', walkWt_reverse' wt hsym]
    at f1 f2 c1 c6 c7
  have h24 : (2 : ZMod 4) = 4 := by
    linear_combination f1 + f2 - (c6 - c7 + c1) + 2 * hsym z x
  exact absurd h24 (by decide)

/-- A configuration: a longest path `S1 . (u z) . D` from `x` with a chord `x z`,
where `S1` has `n` edges. -/
private def IsCfg (K : SimpleGraph V) (n : ℕ) : Prop :=
  ∃ (x u z y : V) (S1 : K.Walk x u) (D : K.Walk z y) (huz : K.Adj u z),
    K.Adj x z ∧ 0 < S1.length ∧ (S1.append (Walk.cons huz D)).IsPath ∧
    (∀ (a b : V) (q : K.Walk a b), q.IsPath → q.length ≤ S1.length + D.length + 1) ∧
    S1.length = n

theorem exists_concat {K : SimpleGraph V} {a b : V} (p : K.Walk a b) (hl : 0 < p.length) :
    ∃ (c : V) (q : K.Walk a c) (h : K.Adj c b), p = q.append (Walk.cons h Walk.nil) := by
  cases p with
  | nil => simp at hl
  | cons h p' =>
    obtain ⟨c, q, h', e⟩ := Walk.exists_cons_eq_concat h p'
    exact ⟨c, q, h', by rw [e, Walk.concat_eq_append]⟩

theorem key {K : SimpleGraph V} {x v u z y : V} (h : K.Adj x v) (S' : K.Walk v u)
    (D : K.Walk z y) (huz : K.Adj u z)
    (hP : ((Walk.cons h S').append (Walk.cons huz D)).IsPath)
    (hmax : ∀ (a b : V) (q : K.Walk a b), q.IsPath →
      q.length ≤ (Walk.cons h S').length + D.length + 1)
    (hmin : ∀ n, n < (Walk.cons h S').length → ¬ IsCfg K n) :
    ∀ w, K.Adj x w → w ∈ S'.support → w = v := by
  intro w hxw hw
  by_contra hwv
  obtain ⟨A, B, spec⟩ : ∃ (A : K.Walk v w) (B : K.Walk w u), A.append B = S' :=
    ⟨_, _, S'.take_spec hw⟩
  subst spec
  obtain ⟨c, q, hcw, eA⟩ := exists_concat A (pos_of_ne A (Ne.symm hwv))
  subst eA
  refine hmin (q.length + 1) ?_ ⟨x, c, w, y, Walk.cons h q, B.append (Walk.cons huz D), hcw,
    hxw, by simp, ?_, ?_, by simp⟩
  · simp [Walk.length_append]
  · have e : (Walk.cons h q).append (Walk.cons hcw (B.append (Walk.cons huz D))) =
        (Walk.cons h ((q.append (Walk.cons hcw Walk.nil)).append B)).append
          (Walk.cons huz D) := by
      simp only [Walk.cons_append, ← Walk.append_assoc, Walk.nil_append]
    rw [e]
    exact hP
  · intro a b p hp
    have := hmax a b p hp
    simp [Walk.length_append] at this ⊢
    omega

theorem far_nbr {K : SimpleGraph V} (hdeg : ∀ v, 0 < K.degree v → 3 ≤ K.degree v)
    {x u z y : V} (S1 : K.Walk x u) (D : K.Walk z y) (huz : K.Adj u z) (hxz : K.Adj x z)
    (lS : 0 < S1.length) (hP : (S1.append (Walk.cons huz D)).IsPath)
    (hmax : ∀ (a b : V) (q : K.Walk a b), q.IsPath → q.length ≤ S1.length + D.length + 1)
    (hmin : ∀ n, n < S1.length → ¬ IsCfg K n) :
    ∃ t, K.Adj x t ∧ t ∈ D.support ∧ t ≠ z := by
  by_contra hno
  push Not at hno
  have hon : ∀ w, K.Adj x w → w ∈ S1.support ∨ w ∈ D.support := by
    intro w hxw
    by_contra hc
    push Not at hc
    have hPw : (Walk.cons hxw.symm (S1.append (Walk.cons huz D))).IsPath := by
      rw [Walk.cons_isPath_iff]
      refine ⟨hP, ?_⟩
      rw [Walk.mem_support_append_iff]
      rintro (h1 | h1)
      · exact hc.1 h1
      · rw [Walk.support_cons, List.mem_cons] at h1
        rcases h1 with rfl | h1
        · exact hc.1 S1.end_mem_support
        · exact hc.2 h1
    have := hmax _ _ _ hPw
    simp [Walk.length_append] at this
  have huniq : ∀ w w', K.Adj x w → K.Adj x w' → w ∈ S1.support → w' ∈ S1.support →
      w = w' := by
    cases S1 with
    | nil => simp at lS
    | cons h S' =>
      have k := key h S' D huz hP hmax hmin
      intro w w' hw hw' m m'
      rw [Walk.support_cons, List.mem_cons] at m m'
      rcases m with rfl | m
      · exact absurd hw (K.irrefl)
      rcases m' with rfl | m'
      · exact absurd hw' (K.irrefl)
      exact (k w hw m).trans (k w' hw' m').symm
  have h3 : 3 ≤ K.degree x := hdeg x ((K.degree_pos_iff_exists_adj x).2 ⟨z, hxz⟩)
  rw [← K.card_neighborFinset_eq_degree] at h3
  obtain ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩ := Finset.two_lt_card_iff.1 h3
  rw [mem_neighborFinset] at ha hb hc
  have cl : ∀ w, K.Adj x w → w ∈ S1.support ∨ w = z := fun w hw =>
    (hon w hw).imp id (hno w hw)
  rcases cl a ha with pa | pa <;> rcases cl b hb with pb | pb <;> rcases cl c hc with pc | pc
  all_goals first
    | exact hab (huniq a b ha hb pa pb)
    | exact hac (huniq a c ha hc pa pc)
    | exact hbc (huniq b c hb hc pb pc)
    | exact hab (pa.trans pb.symm)
    | exact hac (pa.trans pc.symm)
    | exact hbc (pb.trans pc.symm)

theorem exists_cfg {K : SimpleGraph V} (hdeg : ∀ v, 0 < K.degree v → 3 ≤ K.degree v)
    (hedge : ∃ v w, K.Adj v w) : ∃ n, IsCfg K n := by
  obtain ⟨v0, w0, h0⟩ := hedge
  have hex : ∃ N, (∃ (a b : V) (q : K.Walk a b), q.IsPath ∧ q.length = N) ∧
      ∀ (a b : V) (q : K.Walk a b), q.IsPath → q.length ≤ N := by
    refine ⟨Nat.findGreatest (fun n => ∃ (a b : V) (q : K.Walk a b), q.IsPath ∧ q.length = n)
      (Fintype.card V), ?_, ?_⟩
    · exact Nat.findGreatest_spec (P := fun n => ∃ (a b : V) (q : K.Walk a b),
        q.IsPath ∧ q.length = n) (Nat.zero_le _) ⟨v0, v0, Walk.nil, Walk.IsPath.nil, rfl⟩
    · intro a b q hq
      exact Nat.le_findGreatest (P := fun n => ∃ (a b : V) (q : K.Walk a b),
        q.IsPath ∧ q.length = n) hq.length_lt.le ⟨a, b, q, hq, rfl⟩
  obtain ⟨N, ⟨a, b, P, hPp, hPl⟩, hle⟩ := hex
  have hN : 1 ≤ N := by
    have := hle _ _ (Walk.cons h0 Walk.nil) (by
      rw [Walk.cons_isPath_iff]
      exact ⟨Walk.IsPath.nil, by simpa using h0.ne⟩)
    simpa using this
  cases P with
  | nil =>
    simp at hPl
    omega
  | @cons _ v1 _ h P' =>
    have hon : ∀ w, K.Adj a w → w ∈ P'.support := by
      intro w hw
      by_contra hc
      have hpw : (Walk.cons hw.symm (Walk.cons h P')).IsPath := by
        rw [Walk.cons_isPath_iff]
        refine ⟨hPp, ?_⟩
        rw [Walk.support_cons, List.mem_cons]
        rintro (e | e)
        · exact hw.ne e.symm
        · exact hc e
      have := hle _ _ _ hpw
      simp at this hPl
      omega
    have h3 : 3 ≤ K.degree a := hdeg a ((K.degree_pos_iff_exists_adj a).2 ⟨_, h⟩)
    rw [← K.card_neighborFinset_eq_degree] at h3
    obtain ⟨z, hz, hzv⟩ : ∃ z, K.Adj a z ∧ z ≠ v1 := by
      obtain ⟨p, q, r, hp, hq, hr, hpq, hpr, hqr⟩ := Finset.two_lt_card_iff.1 h3
      rw [mem_neighborFinset] at hp hq
      by_cases e : p = v1
      · exact ⟨q, hq, fun e' => hpq (e.trans e'.symm)⟩
      · exact ⟨p, hp, e⟩
    obtain ⟨A, D, spec⟩ : ∃ (A : K.Walk v1 z) (D : K.Walk z b), A.append D = P' :=
      ⟨_, _, P'.take_spec (hon z hz)⟩
    subst spec
    obtain ⟨c, q, hcz, eA⟩ := exists_concat A (pos_of_ne A (Ne.symm hzv))
    subst eA
    refine ⟨q.length + 1, a, c, z, b, Walk.cons h q, D, hcz, hz, by simp, ?_, ?_, by simp⟩
    · have e : (Walk.cons h q).append (Walk.cons hcz D) =
          Walk.cons h ((q.append (Walk.cons hcz Walk.nil)).append D) := by
        simp only [Walk.cons_append, ← Walk.append_assoc, Walk.nil_append]
      rw [e]
      exact hPp
    · intro a' b' p hp
      have := hle a' b' p hp
      simp [Walk.length_append] at hPl ⊢
      omega

/-- L4: in a graph with an edge whose non-isolated vertices have degree at least 3,
some cycle has weight different from 2 modulo 4. -/
theorem L4_thmW (K : SimpleGraph V) (wt : V → V → ZMod 4) (hsym : ∀ x y, wt x y = wt y x)
    (hdeg : ∀ v, 0 < K.degree v → 3 ≤ K.degree v) (hedge : ∃ v w, K.Adj v w) :
    ∃ (v : V) (p : K.Walk v v), p.IsCycle ∧ walkWt wt p ≠ 2 := by
  by_contra hcon
  have hall : ∀ (v : V) (p : K.Walk v v), p.IsCycle → walkWt wt p = 2 := by
    intro v p hp
    by_contra h
    exact hcon ⟨v, p, hp, h⟩
  have hex := exists_cfg hdeg hedge
  obtain ⟨x, u, z, y, S1, D, huz, hxz, lS, hP, hmax, hn⟩ := Nat.find_spec hex
  have hmin : ∀ n, n < S1.length → ¬ IsCfg K n := fun n hlt =>
    Nat.find_min hex (hn ▸ hlt)
  obtain ⟨hS, hD, hd⟩ := path_split S1 huz D hP
  have hSr : S1.reverse.IsPath := (Walk.isPath_reverse_iff _).2 hS
  have hP' : (S1.reverse.append (Walk.cons hxz D)).IsPath :=
    path_join _ _ _ hSr hD (fun w hw => hd w (by simpa using hw))
  obtain ⟨t1, hx1, m1, n1⟩ := far_nbr hdeg S1 D huz hxz lS hP hmax hmin
  obtain ⟨t2, hu2, m2, n2⟩ := far_nbr hdeg S1.reverse D hxz huz (by simpa using lS) hP'
    (by simpa using hmax) (by simpa using hmin)
  obtain ⟨T, R, spec⟩ : ∃ (T : K.Walk z t1) (R : K.Walk t1 y), T.append R = D :=
    ⟨_, _, D.take_spec m1⟩
  have lT : 0 < T.length := pos_of_ne T (Ne.symm n1)
  subst spec
  rw [Walk.mem_support_append_iff] at m2
  rcases m2 with m2 | m2
  · obtain ⟨T', Q', spec'⟩ : ∃ (T' : K.Walk z t2) (Q' : K.Walk t2 t1), T'.append Q' = T :=
      ⟨_, _, T.take_spec m2⟩
    subst spec'
    exact theta wt hsym hall S1.reverse T' Q' hxz huz hu2 hx1 hSr (by simpa using lS)
      hD.of_append_left (pos_of_ne T' (Ne.symm n2))
      (fun w hw h => hd w (by simpa using hw)
        ((Walk.mem_support_append_iff _ _).2 (Or.inl h)))
  · obtain ⟨Q, R', spec'⟩ : ∃ (Q : K.Walk t1 t2) (R' : K.Walk t2 y), Q.append R' = R :=
      ⟨_, _, R.take_spec m2⟩
    subst spec'
    have hTQ : (T.append Q).IsPath := by
      rw [Walk.append_assoc] at hD
      exact hD.of_append_left
    exact theta wt hsym hall S1 T Q huz hxz hx1 hu2 hS lS hTQ lT
      (fun w hw h => hd w hw (by
        rw [Walk.append_assoc]
        exact (Walk.mem_support_append_iff _ _).2 (Or.inl h)))

/- ## L5: lifting cycles (agent L5) -/

omit [Fintype V] [DecidableEq V] in
/-- The weight of `cons h p` is the weight of the first dart plus the weight of `p`. -/
theorem walkWt_cons {G : SimpleGraph V} {R : Type} [AddCommMonoid R] (wt : V → V → R)
    {u v w : V} (h : G.Adj u v) (p : G.Walk v w) :
    walkWt wt (Walk.cons h p) = wt u v + walkWt wt p := by
  simp [walkWt]

omit [Fintype V] [DecidableEq V] in
/-- A walk of the suppressed graph that starts at a good vertex visits only good vertices. -/
theorem good_of_mem_support (H : SimpleGraph V) (good : V → Prop) :
    ∀ {u t : V} (p : (supp H good).Walk u t), good u → ∀ x ∈ p.support, good x := by
  intro u t p
  induction p with
  | nil =>
    intro hu x hx
    rw [Walk.support_nil, List.mem_singleton] at hx
    rw [hx]
    exact hu
  | cons h p ih =>
    intro hu x hx
    rw [Walk.support_cons, List.mem_cons] at hx
    rcases hx with hx | hx
    · rw [hx]
      exact hu
    · exact ih h.2.2.1 x hx

omit [Fintype V] [DecidableEq V] in
/-- A path of the suppressed graph lifts to a path of `H` whose length is its weight.
Each vertex of the lift is a vertex of the path or a bad midpoint of one of its edges.
Each edge of the lift is an edge of the path or has a bad endpoint. -/
theorem lift_path (H : SimpleGraph V) (good : V → Prop)
    (htwo : ∀ y, ¬ good y → ∀ a b c', H.Adj y a → H.Adj y b → H.Adj y c' →
        a = b ∨ a = c' ∨ b = c') :
    ∀ {u t : V} (p : (supp H good).Walk u t), p.IsPath →
      ∃ q : H.Walk u t, q.IsPath ∧ q.length = walkWt (wt1 H) p ∧
        (∀ x ∈ q.support, x ∈ p.support ∨
          (¬ good x ∧ ∃ a b, s(a, b) ∈ p.edges ∧ H.Adj x a ∧ H.Adj x b)) ∧
        (∀ e ∈ q.edges, e ∈ p.edges ∨ ∃ x ∈ e, ¬ good x) := by
  intro u t p
  induction p with
  | nil =>
    intro _
    exact ⟨Walk.nil, Walk.IsPath.nil, by simp [walkWt], by simp, by simp⟩
  | @cons u u' t h p ih =>
    intro hp
    rw [Walk.cons_isPath_iff] at hp
    obtain ⟨q, hq, hlen, hi, hii⟩ := ih hp.1
    have hu : good u := h.2.1
    have hu' : good u' := h.2.2.1
    have huq : u ∉ q.support := by
      intro hx
      rcases hi u hx with h1 | h1
      · exact hp.2 h1
      · exact h1.1 hu
    have hi' : ∀ x ∈ q.support, x ∈ (Walk.cons h p).support ∨
        (¬ good x ∧ ∃ a b, s(a, b) ∈ (Walk.cons h p).edges ∧ H.Adj x a ∧ H.Adj x b) := by
      intro x hx
      rcases hi x hx with h1 | ⟨h1, a, b, hab, h2, h3⟩
      · left
        rw [Walk.support_cons]
        exact List.mem_cons_of_mem _ h1
      · right
        refine ⟨h1, a, b, ?_, h2, h3⟩
        rw [Walk.edges_cons]
        exact List.mem_cons_of_mem _ hab
    have hii' : ∀ e ∈ q.edges, e ∈ (Walk.cons h p).edges ∨ ∃ x ∈ e, ¬ good x := by
      intro e he
      rcases hii e he with h1 | h1
      · left
        rw [Walk.edges_cons]
        exact List.mem_cons_of_mem _ h1
      · exact Or.inr h1
    by_cases hadj : H.Adj u u'
    · refine ⟨Walk.cons hadj q, ?_, ?_, ?_, ?_⟩
      · rw [Walk.cons_isPath_iff]
        exact ⟨hq, huq⟩
      · rw [Walk.length_cons, walkWt_cons, hlen, wt1, if_pos hadj, add_comm]
      · intro x hx
        rw [Walk.support_cons, List.mem_cons] at hx
        rcases hx with hx | hx
        · left
          rw [hx, Walk.support_cons]
          exact List.mem_cons_self
        · exact hi' x hx
      · intro e he
        rw [Walk.edges_cons, List.mem_cons] at he
        rcases he with he | he
        · left
          rw [he, Walk.edges_cons]
          exact List.mem_cons_self
        · exact hii' e he
    · obtain ⟨y, hy, huy, hyu'⟩ : ∃ y, ¬ good y ∧ H.Adj u y ∧ H.Adj y u' := by
        rcases h.2.2.2 with h1 | h1
        · exact absurd h1 hadj
        · exact h1
      have hyq : y ∉ q.support := by
        intro hx
        rcases hi y hx with h1 | ⟨_, a, b, hab, h2, h3⟩
        · exact hy (good_of_mem_support H good p hu' y h1)
        · have hne : a ≠ b := (p.adj_of_mem_edges hab).ne
          rcases htwo y hy a b u h2 h3 huy.symm with h4 | h4 | h4
          · exact hne h4
          · exact hp.2 (h4 ▸ p.fst_mem_support_of_mem_edges hab)
          · exact hp.2 (h4 ▸ p.snd_mem_support_of_mem_edges hab)
      refine ⟨Walk.cons huy (Walk.cons hyu' q), ?_, ?_, ?_, ?_⟩
      · rw [Walk.cons_isPath_iff, Walk.cons_isPath_iff, Walk.support_cons, List.mem_cons]
        refine ⟨⟨hq, hyq⟩, ?_⟩
        rintro (h1 | h1)
        · exact huy.ne h1
        · exact huq h1
      · rw [Walk.length_cons, Walk.length_cons, walkWt_cons, hlen, wt1, if_neg hadj]
        omega
      · intro x hx
        rw [Walk.support_cons, Walk.support_cons, List.mem_cons, List.mem_cons] at hx
        rcases hx with hx | hx | hx
        · left
          rw [hx, Walk.support_cons]
          exact List.mem_cons_self
        · right
          rw [hx]
          refine ⟨hy, u, u', ?_, huy.symm, hyu'⟩
          rw [Walk.edges_cons]
          exact List.mem_cons_self
        · exact hi' x hx
      · intro e he
        rw [Walk.edges_cons, Walk.edges_cons, List.mem_cons, List.mem_cons] at he
        rcases he with he | he | he
        · right
          rw [he]
          exact ⟨y, Sym2.mem_mk_right u y, hy⟩
        · right
          rw [he]
          exact ⟨y, Sym2.mem_mk_left y u', hy⟩
        · exact hii' e he

/-- L5: a cycle of the suppressed graph lifts to a cycle of `H` whose length is its weight. -/
theorem L5_lift (H : SimpleGraph V) (good : V → Prop)
    (htwo : ∀ y, ¬ good y → ∀ a b c', H.Adj y a → H.Adj y b → H.Adj y c' →
        a = b ∨ a = c' ∨ b = c') :
    ∀ (v : V) (C : (supp H good).Walk v v), C.IsCycle →
      ∃ (u : V) (D : H.Walk u u), D.IsCycle ∧ D.length = walkWt (wt1 H) C := by
  intro v C hC
  cases C with
  | nil => exact absurd rfl hC.ne_nil
  | @cons _ u' _ h p =>
    rw [Walk.cons_isCycle_iff] at hC
    obtain ⟨q, hq, hlen, hi, hii⟩ := lift_path H good htwo p hC.1
    have hv : good v := h.2.1
    have hu' : good u' := h.2.2.1
    by_cases hadj : H.Adj v u'
    · refine ⟨v, Walk.cons hadj q, ?_, ?_⟩
      · rw [Walk.cons_isCycle_iff]
        refine ⟨hq, fun he => ?_⟩
        rcases hii _ he with h1 | ⟨x, hx, hxg⟩
        · exact hC.2 h1
        · rw [Sym2.mem_iff] at hx
          rcases hx with hx | hx
          · exact hxg (hx ▸ hv)
          · exact hxg (hx ▸ hu')
      · rw [Walk.length_cons, walkWt_cons, hlen, wt1, if_pos hadj, add_comm]
    · obtain ⟨y, hy, hvy, hyu'⟩ : ∃ y, ¬ good y ∧ H.Adj v y ∧ H.Adj y u' := by
        rcases h.2.2.2 with h1 | h1
        · exact absurd h1 hadj
        · exact h1
      have hvu : v ≠ u' := h.1
      have hyq : y ∉ q.support := by
        intro hx
        rcases hi y hx with h1 | ⟨_, a, b, hab, h2, h3⟩
        · exact hy (good_of_mem_support H good p hu' y h1)
        · have hne : a ≠ b := (p.adj_of_mem_edges hab).ne
          apply hC.2
          rcases htwo y hy a b v h2 h3 hvy.symm with h4 | h4 | h4
          · exact absurd h4 hne
          · rcases htwo y hy a b u' h2 h3 hyu' with h5 | h5 | h5
            · exact absurd h5 hne
            · exact absurd (h4.symm.trans h5) hvu
            · have e : s(v, u') = s(a, b) := by rw [h4, h5]
              rw [e]
              exact hab
          · rcases htwo y hy a b u' h2 h3 hyu' with h5 | h5 | h5
            · exact absurd h5 hne
            · have e : s(v, u') = s(a, b) := by rw [h4, h5, Sym2.eq_swap]
              rw [e]
              exact hab
            · exact absurd (h4.symm.trans h5) hvu
      refine ⟨v, Walk.cons hvy (Walk.cons hyu' q), ?_, ?_⟩
      · rw [Walk.cons_isCycle_iff, Walk.cons_isPath_iff, Walk.edges_cons, List.mem_cons]
        refine ⟨⟨hq, hyq⟩, ?_⟩
        rintro (h1 | h1)
        · rw [Sym2.eq_iff] at h1
          rcases h1 with ⟨h1, _⟩ | ⟨h1, _⟩
          · exact hvy.ne h1
          · exact hvu h1
        · exact hyq (q.snd_mem_support_of_mem_edges h1)
      · rw [Walk.length_cons, Walk.length_cons, walkWt_cons, hlen, wt1, if_neg hadj]
        omega

/- ## Assembly helpers (proved) -/

theorem len_mem_cycleLengths {H G : SimpleGraph V} (hle : H ≤ G) {u : V} (D : H.Walk u u)
    (hD : D.IsCycle) : D.length ∈ G.cycleLengths := by
  show ∃ (a : V) (w : G.Walk a a), w.IsCycle ∧ w.length = D.length
  exact ⟨u, D.mapLe hle, hD.mapLe hle, by simp⟩

theorem walkWt_natCast {G : SimpleGraph V} (f : V → V → ℕ) {u v : V} (p : G.Walk u v) :
    walkWt (fun a b => ((f a b : ℕ) : ZMod 4)) p = ((walkWt f p : ℕ) : ZMod 4) := by
  unfold walkWt
  rw [Nat.cast_list_sum, List.map_map]
  rfl

theorem walk_parity_of_cut {H : SimpleGraph V} (c : V → Bool)
    (hc : ∀ v w, H.Adj v w → c v ≠ c w) {u v : V} (p : H.Walk u v) :
    (p.length % 2 = 0 ∧ c u = c v) ∨ (p.length % 2 = 1 ∧ c u ≠ c v) := by
  induction p with
  | nil => left; simp
  | @cons a x b h p ih =>
    have hax : c a ≠ c x := hc a x h
    rw [SimpleGraph.Walk.length_cons]
    rcases ih with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · right
      refine ⟨by omega, ?_⟩
      rw [← h2]
      exact hax
    · left
      refine ⟨by omega, ?_⟩
      revert hax h2
      cases c a <;> cases c x <;> cases c b <;> simp

theorem core_false {G H : SimpleGraph V} (c : V → Bool) (hle : H ≤ G)
    (hc : ∀ v w, H.Adj v w → c v ≠ c w) (h2 : ∀ v, 2 ≤ H.degree v)
    (hbad : ∀ y w, H.degree y = 2 → H.Adj y w → 3 ≤ H.degree w)
    (hV : Nonempty V) (hNC : ∀ m ∈ G.cycleLengths, ¬ 4 ∣ m) : False := by
  have hno4 : ∀ a b c' d, H.Adj a b → H.Adj b c' → H.Adj c' d → H.Adj d a →
      a ≠ c' → b ≠ d → False := by
    intro a b c' d hab hbc hcd hda hac hbd
    have hpc : (SimpleGraph.Walk.cons hab (SimpleGraph.Walk.cons hbc
        (SimpleGraph.Walk.cons hcd (SimpleGraph.Walk.cons hda SimpleGraph.Walk.nil)))).IsCycle := by
      rw [SimpleGraph.Walk.cons_isCycle_iff]
      simp [SimpleGraph.Walk.isPath_def, SimpleGraph.Walk.edges, Sym2.eq_iff,
        hab.ne, hbc.ne, hcd.ne, hda.ne, hac, hbd, hac.symm, hbd.symm, hda.ne.symm,
        hab.ne.symm, hbc.ne.symm, hcd.ne.symm]
    exact hNC _ (len_mem_cycleLengths hle _ hpc) (by simp)
  obtain ⟨v0⟩ := hV
  have hgood : ∃ g, 3 ≤ H.degree g := by
    by_cases hv : 3 ≤ H.degree v0
    · exact ⟨v0, hv⟩
    · have hd : H.degree v0 = 2 := by have := h2 v0; omega
      have hpos : 0 < H.degree v0 := by omega
      obtain ⟨w, hw⟩ := (SimpleGraph.degree_pos_iff_exists_adj H v0).1 hpos
      exact ⟨w, hbad v0 w hd hw⟩
  set K := OMA.Dean4.supp H (fun x => 3 ≤ H.degree x) with hK
  have hK3 : ∀ v, 3 ≤ H.degree v → 3 ≤ K.degree v :=
    L3_supp_degree H c hc h2 hbad hno4
  have hdegK : ∀ v, 0 < K.degree v → 3 ≤ K.degree v := by
    intro v hv
    obtain ⟨w, hw⟩ := (SimpleGraph.degree_pos_iff_exists_adj K v).1 hv
    obtain ⟨-, hgv, -, -⟩ := hw
    exact hK3 v hgv
  have hedge : ∃ v w, K.Adj v w := by
    obtain ⟨g, hg⟩ := hgood
    have hpos : 0 < K.degree g := by have := hK3 g hg; omega
    obtain ⟨w, hw⟩ := (SimpleGraph.degree_pos_iff_exists_adj K g).1 hpos
    exact ⟨g, w, hw⟩
  have hsym : ∀ x y, ((wt1 H x y : ℕ) : ZMod 4) = ((wt1 H y x : ℕ) : ZMod 4) := by
    intro x y
    unfold wt1
    rw [H.adj_comm]
  obtain ⟨v, p, hpc, hne⟩ := L4_thmW K (fun x y => ((wt1 H x y : ℕ) : ZMod 4)) hsym hdegK hedge
  have htwo : ∀ y, ¬ (fun x => 3 ≤ H.degree x) y → ∀ a b c', H.Adj y a → H.Adj y b →
      H.Adj y c' → a = b ∨ a = c' ∨ b = c' := by
    intro y hy a b c' ha hb hc'
    by_contra hcon'
    push_neg at hcon'
    have hsub : ({a, b, c'} : Finset V) ⊆ H.neighborFinset y := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rw [SimpleGraph.mem_neighborFinset]
      rcases hx with rfl | rfl | rfl <;> assumption
    have hcard := Finset.card_le_card hsub
    rw [SimpleGraph.card_neighborFinset_eq_degree] at hcard
    have h3 : 2 < ({a, b, c'} : Finset V).card :=
      Finset.two_lt_card.2 ⟨a, by simp, b, by simp, c', by simp, hcon'.1, hcon'.2.1, hcon'.2.2⟩
    have hy' : ¬ 3 ≤ H.degree y := hy
    omega
  obtain ⟨u, D, hD, hlen⟩ := L5_lift H (fun x => 3 ≤ H.degree x) htwo v p hpc
  have hpar := walk_parity_of_cut c hc D
  have hev : D.length % 2 = 0 := by
    rcases hpar with h | h
    · exact h.1
    · exact absurd rfl h.2
  have hcast : ((D.length : ℕ) : ZMod 4) = walkWt (fun x y => ((wt1 H x y : ℕ) : ZMod 4)) p := by
    rw [hlen]
    exact (walkWt_natCast (wt1 H) p).symm
  have hn2 : ((D.length : ℕ) : ZMod 4) ≠ 2 := by
    rw [hcast]
    exact hne
  have h4 : 4 ∣ D.length := by
    rcases (by omega : D.length % 4 = 0 ∨ D.length % 4 = 2) with h | h
    · exact Nat.dvd_of_mod_eq_zero h
    · exfalso
      apply hn2
      have e : ((D.length % 4 : ℕ) : ZMod 4) = ((2 : ℕ) : ZMod 4) := by rw [h]
      rw [ZMod.natCast_mod] at e
      rw [e]
      decide
  exact hNC _ (len_mem_cycleLengths hle D hD) h4

end OMA.Dean4

open OMA.Dean4 in
private theorem deanFour : type_of% @Arxiv.«2605.02731».dean_conjecture.variants.four := by
  intro V _ _ G _ hG
  by_contra hcon
  have hNC : ∀ m ∈ G.cycleLengths, ¬ 4 ∣ m := fun m hm hd => hcon ⟨m, hm, hd⟩
  have hV : Nonempty V := by
    rcases isEmpty_or_nonempty V with hE | hN
    · exfalso
      haveI : Subsingleton V := ⟨fun a => isEmptyElim a⟩
      have h0 : G.minDegree = 0 := SimpleGraph.minDegree_of_subsingleton G
      omega
    · exact hN
  obtain ⟨c, h1, h2⟩ := L1_maxcut G
  obtain ⟨hd2, hbad⟩ := L2_cut_degrees G hG c h1 h2
  exact core_false c (fun v w h => (show G.Adj v w ∧ c v ≠ c w from h).1)
    (fun v w h => (show G.Adj v w ∧ c v ≠ c w from h).2) hd2 hbad hV hNC


/- An induced 2-connected core with a bounded degree boundary. -/

namespace DeanLink

open SimpleGraph

variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

private def walkVerts {u v : V} (p : G.Walk u v) : Finset V :=
  p.support.toFinset

lemma mem_walkVerts {u v w : V} {p : G.Walk u v} : w ∈ walkVerts G p ↔ w ∈ p.support :=
  List.mem_toFinset

private def ReachAvoiding (S : Finset V) (u v : V) : Prop :=
  ∃ p : G.Walk u v, ∀ w ∈ p.support, w ∉ S

private def IsSeparating (S : Finset V) : Prop :=
  ∃ u v : V, u ∉ S ∧ v ∉ S ∧ ¬ ReachAvoiding G S u v

/-- A separating set S separates a nonempty subset X ⊆ V \ S from V \ (X ∪ S). -/
lemma isSeparating_of_closed_subset {S X : Finset V}
    (hXne : X.Nonempty) (hXdisj : Disjoint X S)
    (hYne : (Finset.univ \ (X ∪ S)).Nonempty)
    (hclosed : ∀ a ∈ X, ∀ b : V, G.Adj a b → b ∈ X ∪ S) :
    IsSeparating G S := by
  obtain ⟨u, huX⟩ := hXne
  obtain ⟨v, hvY⟩ := hYne
  simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_union, true_and, not_or] at hvY
  refine ⟨u, v, Finset.disjoint_left.mp hXdisj huX, hvY.2, fun ⟨p, hp⟩ => ?_⟩
  have hstay : ∀ {a b : V} (q : G.Walk a b), a ∈ X → (∀ w ∈ q.support, w ∉ S) → b ∈ X := by
    intro a b q
    induction q with
    | nil => intro ha _; exact ha
    | @cons a c b hac r ih =>
      intro ha hq
      have hcS : c ∉ S := hq c (by simp)
      have hcXS := hclosed a ha c hac
      have hcX : c ∈ X := (Finset.mem_union.mp hcXS).resolve_right hcS
      exact ih hcX (fun w hw => hq w (by simp [hw]))
  exact hvY.1 (hstay p huX hp)


/-- Shortest path avoiding S between two disjoint Finsets X and Y: interior is disjoint from X ∪ Y. -/
lemma exists_minimal_path_between {S X Y : Finset V}
    (hXY : Disjoint X Y) (hXS : Disjoint X S) (hYS : Disjoint Y S)
    (hex : ∃ a ∈ X, ∃ b ∈ Y, ReachAvoiding G S a b) :
    ∃ (a b : V) (p : G.Walk a b),
      a ∈ X ∧ b ∈ Y ∧ p.IsPath ∧ 1 ≤ p.length ∧
      (∀ w ∈ p.support, w ∉ S) ∧
      (∀ w ∈ p.support, w ≠ a → w ≠ b → w ∉ X ∧ w ∉ Y) := by
  classical
  have hex_len : ∃ l : ℕ, ∃ (a b : V) (p : G.Walk a b),
      a ∈ X ∧ b ∈ Y ∧ (∀ w ∈ p.support, w ∉ S) ∧ p.length = l := by
    obtain ⟨a, ha, b, hb, p, hp⟩ := hex
    exact ⟨p.length, a, b, p, ha, hb, hp, rfl⟩
  let m := Nat.find hex_len
  obtain ⟨a, b, p, haX, hbY, hpS, hplen⟩ := Nat.find_spec hex_len
  have hmin : ∀ (a' b' : V) (q : G.Walk a' b'), a' ∈ X → b' ∈ Y → (∀ w ∈ q.support, w ∉ S) → m ≤ q.length :=
    fun a' b' q ha' hb' hqS => Nat.find_min' hex_len ⟨a', b', q, ha', hb', hqS, rfl⟩
  have hab : a ≠ b := fun h => Finset.disjoint_left.mp hXY haX (h ▸ hbY)
  let q := p.bypass
  have hqS : ∀ w ∈ q.support, w ∉ S := fun w hw => hpS w (Walk.support_bypass_subset p hw)
  have hqlen : q.length = m := by
    have hle : q.length ≤ p.length := p.length_bypass_le
    have hge : m ≤ q.length := hmin a b q haX hbY hqS
    omega
  have hpos : 1 ≤ q.length := by
    cases hq : q with
    | nil => exact absurd rfl hab
    | cons _ _ => simp
  have hint : ∀ w ∈ q.support, w ≠ a → w ≠ b → w ∉ X ∧ w ∉ Y := by
    intro w hw hwa hwb
    constructor
    · intro hwX
      let r := q.dropUntil w hw
      have hr_lt : r.length < q.length := Walk.length_dropUntil_lt_length hw hwa
      have hrS : ∀ z ∈ r.support, z ∉ S := fun z hz => hqS z (Walk.support_dropUntil_subset q hw hz)
      have := hmin w b r hwX hbY hrS
      omega
    · intro hwY
      let r := q.takeUntil w hw
      have hr_lt : r.length < q.length := Walk.length_takeUntil_lt_length hw hwb
      have hrS : ∀ z ∈ r.support, z ∉ S := fun z hz => hqS z (Walk.support_takeUntil_subset q hw hz)
      have := hmin a w r haX hwY hrS
      omega
  exact ⟨a, b, q, haX, hbY, p.bypass_isPath, hpos, hqS, hint⟩

/-- Trim a path from a ∈ A to b ∈ B (with A, B disjoint) to a subpath whose interior is disjoint from A ∪ B. -/
lemma trim_path_between {A B : Finset V} (hAB : Disjoint A B)
    {a b : V} (p : G.Walk a b) (ha : a ∈ A) (hb : b ∈ B) :
    ∃ (a' b' : V) (q : G.Walk a' b'),
      a' ∈ A ∧ b' ∈ B ∧ q.IsPath ∧ 1 ≤ q.length ∧
      walkVerts G q ⊆ walkVerts G p ∧
      (∀ w ∈ q.support, w ≠ a' → w ≠ b' → w ∉ A ∧ w ∉ B) := by
  classical
  let S : Finset V := Finset.univ \ walkVerts G p
  have h1 : ∃ x ∈ A ∩ walkVerts G p, ∃ y ∈ B ∩ walkVerts G p, ReachAvoiding G S x y :=
    ⟨a, Finset.mem_inter.mpr ⟨ha, (mem_walkVerts G).mpr (Walk.start_mem_support p)⟩,
     b, Finset.mem_inter.mpr ⟨hb, (mem_walkVerts G).mpr (Walk.end_mem_support p)⟩,
     p, fun w hw hS => (Finset.mem_sdiff.mp hS).2 ((mem_walkVerts G).mpr hw)⟩
  obtain ⟨a', b', q, ha', hb', hq_path, hq_pos, hqS, hq_int⟩ :=
    exists_minimal_path_between G
      (hAB.mono Finset.inter_subset_left Finset.inter_subset_left)
      (Finset.disjoint_left.mpr fun z hz hS => (Finset.mem_sdiff.mp hS).2 (Finset.mem_inter.mp hz).2)
      (Finset.disjoint_left.mpr fun z hz hS => (Finset.mem_sdiff.mp hS).2 (Finset.mem_inter.mp hz).2)
      h1
  have hsub : walkVerts G q ⊆ walkVerts G p := fun z hz => by
    by_contra hnot
    exact hqS z ((mem_walkVerts G).mp hz) (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hnot⟩)
  refine ⟨a', b', q, (Finset.mem_inter.mp ha').1, (Finset.mem_inter.mp hb').1, hq_path, hq_pos, hsub, ?_⟩
  intro w hw hwa hwb
  have hwP : w ∈ walkVerts G p := hsub ((mem_walkVerts G).mpr hw)
  have hi := hq_int w hw hwa hwb
  exact ⟨fun hA => hi.1 (Finset.mem_inter.mpr ⟨hA, hwP⟩), fun hB => hi.2 (Finset.mem_inter.mpr ⟨hB, hwP⟩)⟩

/-- Helper: trace a functional, injective directed relation on a finite type from a source (no in-edge)
until a sink (no out-edge). -/
lemma trace_functional_rel {α : Type} [Fintype α] [DecidableEq α] [Inhabited α]
    (E : α → α → Prop) [DecidableRel E]
    (hout_uniq : ∀ x y1 y2, E x y1 → E x y2 → y1 = y2)
    (hin_uniq : ∀ x1 x2 y, E x1 y → E x2 y → x1 = x2)
    (s : α) (hno_in : ∀ x, ¬ E x s) :
    ∃ L : List α, L ≠ [] ∧ L.Nodup ∧ L.head! = s ∧
      (∀ i (hi : i + 1 < L.length), E L[i] L[i + 1]) ∧
      (∀ y, ¬ E L.getLast! y) := by
  classical
  -- Build maximal prefix of length ≤ Fintype.card α by induction on remaining budget
  have hbuild : ∀ (k : ℕ) (L : List α),
      L ≠ [] → L.Nodup → L.head! = s →
      (∀ i (hi : i + 1 < L.length), E L[i] L[i + 1]) →
      Fintype.card α - L.length ≤ k →
      ∃ L' : List α, L' ≠ [] ∧ L'.Nodup ∧ L'.head! = s ∧
        (∀ i (hi : i + 1 < L'.length), E L'[i] L'[i + 1]) ∧
        (∀ y, ¬ E L'.getLast! y) := by
    intro k
    induction k with
    | zero =>
      intro L hLne hLnd hLh hLadj hrem
      refine ⟨L, hLne, hLnd, hLh, hLadj, fun y hy => ?_⟩
      -- Since L.length = Fintype.card α and L.Nodup, y ∈ L!
      have hy_mem : y ∈ L := by
        have hlen : L.toFinset.card = Fintype.card α := by
          rw [List.toFinset_card_of_nodup hLnd]
          have hle := (List.toFinset_card_of_nodup hLnd) ▸ Finset.card_le_univ L.toFinset
          omega
        have huniv : L.toFinset = Finset.univ := Finset.eq_univ_of_card _ hlen
        exact List.mem_toFinset.mp (huniv ▸ Finset.mem_univ y)
      obtain ⟨idx, hidx, hyeq⟩ := List.mem_iff_getElem.mp hy_mem
      cases idx with
      | zero =>
        have hys : y = s := by
          have h0 : L[0]'(List.length_pos_of_ne_nil hLne) = L.head! := by
            cases L with | nil => exact absurd rfl hLne | cons _ _ => rfl
          exact hyeq.symm.trans (h0.trans hLh)
        exact hno_in _ (hys ▸ hy)
      | succ j =>
        have hprev : E L[j] y := hyeq ▸ hLadj j hidx
        have hlast_eq : L.getLast! = L[L.length - 1]'(by cases L with | nil => exact absurd rfl hLne | cons _ _ => simp) := by
          have hpos : 0 < L.length := List.length_pos_of_ne_nil hLne
          rw [List.getLast!_eq_getLast?_getD, List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)]; rfl
        have heq_idx : L[j]'(by omega) = L[L.length - 1]'(by omega) := hin_uniq _ _ y hprev (hlast_eq ▸ hy)
        have := (List.Nodup.getElem_inj_iff hLnd).mp heq_idx
        omega
    | succ k ih =>
      intro L hLne hLnd hLh hLadj hrem
      by_cases hex : ∃ y, E L.getLast! y
      · obtain ⟨y, hy⟩ := hex
        have hy_not_mem : y ∉ L := by
          intro hmem
          obtain ⟨idx, hidx, hyeq⟩ := List.mem_iff_getElem.mp hmem
          cases idx with
          | zero =>
            have hys : y = s := by
              have h0 : L[0]'(List.length_pos_of_ne_nil hLne) = L.head! := by
                cases L with | nil => exact absurd rfl hLne | cons _ _ => rfl
              exact hyeq.symm.trans (h0.trans hLh)
            exact hno_in _ (hys ▸ hy)
          | succ j =>
            have hprev : E L[j] y := hyeq ▸ hLadj j hidx
            have hlast_eq : L.getLast! = L[L.length - 1]'(by cases L with | nil => exact absurd rfl hLne | cons _ _ => simp) := by
              have hpos : 0 < L.length := List.length_pos_of_ne_nil hLne
              rw [List.getLast!_eq_getLast?_getD, List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)]; rfl
            have heq_idx : L[j]'(by omega) = L[L.length - 1]'(by omega) := hin_uniq _ _ y hprev (hlast_eq ▸ hy)
            have := (List.Nodup.getElem_inj_iff hLnd).mp heq_idx
            omega
        let L1 := L ++ [y]
        have hL1ne : L1 ≠ [] := by simp [L1]
        have hL1nd : L1.Nodup := List.nodup_append.mpr ⟨hLnd, List.nodup_singleton y, fun a ha b hb => by
          rw [List.mem_singleton] at hb; subst hb; intro h; exact hy_not_mem (h ▸ ha)⟩
        have hL1h : L1.head! = s := by
          cases hL : L with
          | nil => exact absurd hL hLne
          | cons a as => simp [L1, hL, ← hLh]
        have hL1adj : ∀ i (hi : i + 1 < L1.length), E L1[i] L1[i + 1] := by
          intro i hi
          have hlen1 : L1.length = L.length + 1 := by simp [L1]
          by_cases hlt : i + 1 < L.length
          · simp only [L1, List.getElem_append_left (by omega : i < L.length), List.getElem_append_left hlt]
            exact hLadj i hlt
          · have hieq : i = L.length - 1 := by omega
            have hlast_eq : L.getLast! = L[L.length - 1]'(by cases L with | nil => exact absurd rfl hLne | cons _ _ => simp) := by
              have hpos : 0 < L.length := List.length_pos_of_ne_nil hLne
              rw [List.getLast!_eq_getLast?_getD, List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)]; rfl
            have he1 : L1[i] = L.getLast! := by
              rw [hlast_eq]; simp only [L1, List.getElem_append_left (by omega : i < L.length)]; congr 1
            have he2 : L1[i + 1] = y := by
              simp only [L1, List.getElem_append_right (by omega : L.length ≤ i + 1)]
              have : i + 1 - L.length = 0 := by omega
              simp [this]
            rw [he1, he2]; exact hy
        have hrem1 : Fintype.card α - L1.length ≤ k := by simp [L1]; omega
        exact ih L1 hL1ne hL1nd hL1h hL1adj hrem1
      · push Not at hex
        exact ⟨L, hLne, hLnd, hLh, hLadj, hex⟩
  exact hbuild (Fintype.card α) [s] (List.cons_ne_nil _ _) (List.nodup_singleton s) rfl
    (fun i hi => by simp at hi) (by omega)

/-- Two traces of an injective relation from distinct sources (each with no in-edge) are disjoint! -/
lemma trace_disjoint {α : Type} [Inhabited α] (E : α → α → Prop)
    (hin_uniq : ∀ x1 x2 y, E x1 y → E x2 y → x1 = x2)
    {s1 s2 : α} (hs12 : s1 ≠ s2)
    (hno1 : ∀ x, ¬ E x s1) (hno2 : ∀ x, ¬ E x s2)
    {L1 L2 : List α} (h1ne : L1 ≠ []) (h2ne : L2 ≠ [])
    (h1h : L1.head! = s1) (h2h : L2.head! = s2)
    (h1adj : ∀ i (hi : i + 1 < L1.length), E L1[i] L1[i + 1])
    (h2adj : ∀ i (hi : i + 1 < L2.length), E L2[i] L2[i + 1]) :
    L1.Disjoint L2 := by
  rw [List.disjoint_left]
  intro z hz1 hz2
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hz1
  obtain ⟨j, hj, heq⟩ := List.mem_iff_getElem.mp hz2
  have haux : ∀ n i j (hi : i < L1.length) (hj : j < L2.length), i + j = n → L1[i] ≠ L2[j] := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro i j hi hj hsum heq'
      cases i with
      | zero =>
        cases j with
        | zero =>
          have h10 : L1[0] = s1 := by rw [← h1h]; cases L1 with | nil => exact absurd rfl h1ne | cons _ _ => rfl
          have h20 : L2[0] = s2 := by rw [← h2h]; cases L2 with | nil => exact absurd rfl h2ne | cons _ _ => rfl
          rw [h10, h20] at heq'; exact hs12 heq'
        | succ j' =>
          have h10 : L1[0] = s1 := by rw [← h1h]; cases L1 with | nil => exact absurd rfl h1ne | cons _ _ => rfl
          have hE := h2adj j' hj
          rw [← heq', h10] at hE
          exact hno1 L2[j'] hE
      | succ i' =>
        cases j with
        | zero =>
          have h20 : L2[0] = s2 := by rw [← h2h]; cases L2 with | nil => exact absurd rfl h2ne | cons _ _ => rfl
          have hE := h1adj i' hi
          rw [heq', h20] at hE
          exact hno2 L1[i'] hE
        | succ j' =>
          have hprev := hin_uniq L1[i'] L2[j'] L1[i' + 1] (h1adj i' hi) (heq' ▸ h2adj j' hj)
          exact ih (i' + j') (by omega) i' j' (by omega) (by omega) rfl hprev
  exact haux (i + j) i j hi hj rfl heq.symm

/-- Convert a valid D-trace from (a, false) to (b, true) into a simple path G.Walk a b whose support
vertices are the first components of the trace! -/
lemma walk_of_D_trace [Inhabited V] {a b : V} (L : List (V × Bool))
    (hLne : L ≠ []) (hLnd : L.Nodup)
    (hLh : L.head! = (a, false)) (hLl : L.getLast! = (b, true))
    (hLadj : ∀ i (hi : i + 1 < L.length),
      ((L[i].2 = false ∧ L[i + 1].2 = true ∧ L[i].1 = L[i + 1].1) ∨
       (L[i].2 = true ∧ L[i + 1].2 = false ∧ G.Adj L[i].1 L[i + 1].1))) :
    ∃ p : G.Walk a b, p.IsPath ∧ ∀ w ∈ p.support, (w, false) ∈ L ∧ (w, true) ∈ L := by
  -- Induction on L.length
  have hbuild : ∀ (m : ℕ) (L : List (V × Bool)) (a : V),
      L.length = m → L ≠ [] → L.Nodup → L.head! = (a, false) → L.getLast! = (b, true) →
      (∀ i (hi : i + 1 < L.length),
        ((L[i].2 = false ∧ L[i + 1].2 = true ∧ L[i].1 = L[i + 1].1) ∨
         (L[i].2 = true ∧ L[i + 1].2 = false ∧ G.Adj L[i].1 L[i + 1].1))) →
      ∃ p : G.Walk a b, p.IsPath ∧ ∀ w ∈ p.support, (w, false) ∈ L ∧ (w, true) ∈ L := by
    intro m
    induction m using Nat.strongRecOn with
    | ind m ih =>
      intro L a hLm hLne hLnd hLh hLl hLadj
      cases L with
      | nil => exact absurd rfl hLne
      | cons x1 xs =>
        change x1 = (a, false) at hLh
        subst hLh
        cases xs with
        | nil =>
          change (a, false) = (b, true) at hLl
          exact absurd (congrArg Prod.snd hLl) Bool.false_ne_true
        | cons x2 xs' =>
          have h01 := hLadj 0 (by simp)
          simp only [List.getElem_cons_zero, List.getElem_cons_succ] at h01
          rcases h01 with ⟨_, hx2t, hx2eq⟩ | ⟨hft, _, _⟩
          · have hx2 : x2 = (a, true) := Prod.ext hx2eq.symm hx2t
            subst hx2
            cases xs' with
            | nil =>
              change (a, true) = (b, true) at hLl
              have hab : a = b := congrArg Prod.fst hLl
              subst hab
              exact ⟨Walk.nil, Walk.IsPath.nil, fun w hw => by
                simp only [Walk.support_nil, List.mem_singleton] at hw; subst hw; simp⟩
            | cons x3 xs'' =>
              have h12 := hLadj 1 (by simp)
              simp only [List.getElem_cons_succ, List.getElem_cons_zero] at h12
              rcases h12 with ⟨hft, _, _⟩ | ⟨_, hx3f, hadj⟩
              · exact absurd hft Bool.false_ne_true.symm
              · have hx3 : x3 = (x3.1, false) := Prod.ext rfl hx3f
                let L' := x3 :: xs''
                have hL'nd : L'.Nodup := ((List.nodup_cons.mp hLnd).2 |> List.nodup_cons.mp).2
                have hL'h : L'.head! = (x3.1, false) := by simp [L', ← hx3]
                have hL'l : L'.getLast! = (b, true) := by exact hLl
                have hL'adj : ∀ i (hi : i + 1 < L'.length),
                    ((L'[i].2 = false ∧ L'[i + 1].2 = true ∧ L'[i].1 = L'[i + 1].1) ∨
                     (L'[i].2 = true ∧ L'[i + 1].2 = false ∧ G.Adj L'[i].1 L'[i + 1].1)) := fun i hi =>
                  hLadj (i + 2) (by simp [L'] at hi ⊢; omega)
                obtain ⟨q, hq_path, hq_mem⟩ := ih L'.length (by simp [L'] at hLm ⊢; omega) L' x3.1 rfl
                  (List.cons_ne_nil _ _) hL'nd hL'h hL'l hL'adj
                have ha_not_q : a ∉ q.support := fun h => by
                  have ha_in_L' : (a, false) ∈ L' := (hq_mem a h).1
                  have hnot := (List.nodup_cons.mp hLnd).1
                  exact hnot (List.mem_cons_of_mem _ ha_in_L')
                refine ⟨Walk.cons hadj q, Walk.IsPath.cons hq_path ha_not_q, fun w hw => ?_⟩
                simp only [Walk.support_cons, List.mem_cons] at hw
                rcases hw with rfl | hwq
                · exact ⟨by simp, by simp⟩
                · have hm := hq_mem w hwq
                  exact ⟨List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hm.1),
                         List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hm.2)⟩
          · exact absurd hft Bool.false_ne_true
  exact hbuild L.length L a rfl hLne hLnd hLh hLl hLadj

set_option maxHeartbeats 1200000 in
/-- 2-Path Menger Lemma: in a 2-connected graph, between any two disjoint sets A, B of size ≥ 2,
there exist two vertex-disjoint simple paths from A to B whose interiors are disjoint from A ∪ B. -/
lemma two_disjoint_paths_of_no_cut_vertex
    (hconn : G.Connected) (h2conn : ∀ x : V, ¬ IsSeparating G {x})
    {A B : Finset V} (hAB : Disjoint A B) (hA2 : 2 ≤ A.card) (hB2 : 2 ≤ B.card) :
    ∃ (a1 a2 b1 b2 : V) (p1 : G.Walk a1 b1) (p2 : G.Walk a2 b2),
      a1 ∈ A ∧ a2 ∈ A ∧ a1 ≠ a2 ∧ b1 ∈ B ∧ b2 ∈ B ∧ b1 ≠ b2 ∧
      p1.IsPath ∧ p2.IsPath ∧ 1 ≤ p1.length ∧ 1 ≤ p2.length ∧
      Disjoint (walkVerts G p1) (walkVerts G p2) ∧
      (∀ w ∈ p1.support, w ≠ a1 → w ≠ b1 → w ∉ A ∧ w ∉ B) ∧
      (∀ w ∈ p2.support, w ≠ a2 → w ≠ b2 → w ∉ A ∧ w ∉ B) := by
  classical
  -- Step 1: Find one minimal path P from v0 ∈ A to vr ∈ B
  obtain ⟨a0, ha0⟩ := Finset.card_pos.mp (by omega : 0 < A.card)
  letI : Inhabited V := ⟨a0⟩
  obtain ⟨b0, hb0⟩ := Finset.card_pos.mp (by omega : 0 < B.card)
  obtain ⟨v0, vr, P, hv0A, hvrB, hP_path, hP_pos, _, hP_int⟩ :=
    exists_minimal_path_between G hAB (Finset.disjoint_empty_right A) (Finset.disjoint_empty_right B)
      ⟨a0, ha0, b0, hb0, by obtain ⟨w⟩ := hconn a0 b0; exact ⟨w, fun _ _ => by simp⟩⟩
  set r := P.length
  let vp (i : ℕ) : V := P.getVert i
  have hvp0 : vp 0 = v0 := Walk.getVert_zero P
  have hvpr : vp r = vr := Walk.getVert_length P
  have hvp_inj : ∀ i j : ℕ, i ≤ r → j ≤ r → vp i = vp j → i = j := by
    intro i j hi hj heq
    have hnd := hP_path.support_nodup
    have hlen : P.support.length = r + 1 := P.length_support
    have hi' : i < P.support.length := by omega
    have hj' : j < P.support.length := by omega
    have hgi : P.support[i]'hi' = vp i := (Walk.getVert_eq_support_getElem P hi).symm
    have hgj : P.support[j]'hj' = vp j := (Walk.getVert_eq_support_getElem P hj).symm
    exact (List.Nodup.getElem_inj_iff hnd).mp (by rw [hgi, hgj]; exact heq)
  have hvp_adj : ∀ i : ℕ, i < r → G.Adj (vp i) (vp (i + 1)) := fun i hi =>
    P.adj_getVert_succ hi
  -- Step 2: Uniform vertex-split flow network on V × Bool
  -- Flow P runs (vp 0, false) → (vp 0, true) → (vp 1, false) → ... → (vp r, false) → (vp r, true)
  let D (x y : V × Bool) : Prop :=
    (x.2 = false ∧ y.2 = true ∧ x.1 = y.1) ∨ (x.2 = true ∧ y.2 = false ∧ G.Adj x.1 y.1)
  let F (x y : V × Bool) : Prop :=
    (∃ i : ℕ, i < r ∧ x = (vp i, true) ∧ y = (vp (i + 1), false)) ∨
    (∃ i : ℕ, i ≤ r ∧ x = (vp i, false) ∧ y = (vp i, true))
  have hF_sub_D : ∀ x y, F x y → D x y := by
    rintro x y (⟨i, hi, rfl, rfl⟩ | ⟨i, _, rfl, rfl⟩)
    · exact Or.inr ⟨rfl, rfl, hvp_adj i hi⟩
    · exact Or.inl ⟨rfl, rfl, rfl⟩
  let R (x y : V × Bool) : Prop := (D x y ∧ ¬ F x y) ∨ F y x
  let ReachR (x y : V × Bool) : Prop := Relation.ReflTransGen R x y
  let Src : Finset (V × Bool) := (A.erase v0).image (fun a => (a, false))
  let Snk : Finset (V × Bool) := (B.erase vr).image (fun b => (b, true))
  have hA_not_P : ∀ a ∈ A, a ≠ v0 → ∀ i ≤ r, a ≠ vp i := by
    intro a haA hane i hi heq; subst heq
    by_cases hi0 : i = 0
    · subst hi0; exact hane hvp0
    · by_cases hir : i = r
      · subst hir; exact Finset.disjoint_left.mp hAB (hvpr ▸ haA) hvrB
      · have hne0 : vp i ≠ v0 := fun h => hi0 (hvp_inj i 0 hi (Nat.zero_le r) (h.trans hvp0.symm))
        have hner : vp i ≠ vr := fun h => hir (hvp_inj i r hi le_rfl (h.trans hvpr.symm))
        exact (hP_int (vp i) (P.getVert_mem_support i) hne0 hner).1 haA
  have hB_not_P : ∀ b ∈ B, b ≠ vr → ∀ i ≤ r, b ≠ vp i := by
    intro b hbB hbne i hi heq; subst heq
    by_cases hi0 : i = 0
    · subst hi0; exact Finset.disjoint_left.mp hAB hv0A (hvp0 ▸ hbB)
    · by_cases hir : i = r
      · subst hir; exact hbne hvpr
      · have hne0 : vp i ≠ v0 := fun h => hi0 (hvp_inj i 0 hi (Nat.zero_le r) (h.trans hvp0.symm))
        have hner : vp i ≠ vr := fun h => hir (hvp_inj i r hi le_rfl (h.trans hvpr.symm))
        exact (hP_int (vp i) (P.getVert_mem_support i) hne0 hner).2 hbB
  -- Step 3: Prove there exists an augmenting path in R from Src to Snk
  have hex_aug : ∃ s ∈ Src, ∃ t ∈ Snk, ReachR s t := by
    by_contra hno; push Not at hno
    let X : Finset (V × Bool) := Finset.univ.filter (fun z => ∃ s ∈ Src, ReachR s z)
    have hX_closed : ∀ x ∈ X, ∀ y : V × Bool, R x y → y ∈ X := by
      intro x hx y hxy
      simp only [X, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      obtain ⟨s, hs, hr⟩ := hx; exact ⟨s, hs, Relation.ReflTransGen.tail hr hxy⟩
    have hSrc_sub : Src ⊆ X := fun s hs => by
      simp only [X, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨s, hs, Relation.ReflTransGen.refl⟩
    have hSnk_disj : Disjoint Snk X := Finset.disjoint_left.mpr fun t ht htX => by
      simp only [X, Finset.mem_filter, Finset.mem_univ, true_and] at htX
      obtain ⟨s, hs, hr⟩ := htX; exact hno s hs t ht hr
    have hP_back_fwd : ∀ i < r, (vp (i + 1), false) ∈ X → (vp i, true) ∈ X := fun i hi h =>
      hX_closed _ h _ (Or.inr (Or.inl ⟨i, hi, rfl, rfl⟩))
    have hP_back_int : ∀ i ≤ r, (vp i, true) ∈ X → (vp i, false) ∈ X := fun i hi h =>
      hX_closed _ h _ (Or.inr (Or.inr ⟨i, hi, rfl, rfl⟩))
    have hnonP_step : ∀ u : V, (∀ i ≤ r, u ≠ vp i) → (u, false) ∈ X → (u, true) ∈ X := by
      intro u hni hu
      refine hX_closed _ hu _ (Or.inl ⟨Or.inl ⟨rfl, rfl, rfl⟩, ?_⟩)
      rintro (⟨_, _, h1, _⟩ | ⟨i, hi, h1, _⟩)
      · exact Bool.false_ne_true (congrArg Prod.snd h1)
      · exact hni i hi (congrArg Prod.fst h1)
    let XV : Finset V := Finset.univ.filter (fun u => (u, true) ∈ X)
    obtain ⟨a2, ha2A, ha2ne⟩ : ∃ a2 ∈ A, a2 ≠ v0 := Finset.exists_mem_ne (by omega : 1 < A.card) v0
    obtain ⟨b2, hb2B, hb2ne⟩ : ∃ b2 ∈ B, b2 ≠ vr := Finset.exists_mem_ne (by omega : 1 < B.card) vr
    have ha2_XV : a2 ∈ XV := by
      simp only [XV, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hnonP_step a2 (hA_not_P a2 ha2A ha2ne)
        (hSrc_sub (Finset.mem_image.mpr ⟨a2, Finset.mem_erase.mpr ⟨ha2ne, ha2A⟩, rfl⟩))
    have hb2_not_XV : b2 ∉ XV := by
      simp only [XV, Finset.mem_filter, Finset.mem_univ, true_and]
      exact Finset.disjoint_left.mp hSnk_disj (Finset.mem_image.mpr ⟨b2, Finset.mem_erase.mpr ⟨hb2ne, hb2B⟩, rfl⟩)
    -- Every edge u ~ w with u ∈ XV, w ∉ XV crosses along P!
    have hedge_cross : ∀ u w : V, u ∈ XV → w ∉ XV → G.Adj u w →
        (∃ i < r, u = vp i ∧ w = vp (i + 1) ∧ (vp i, true) ∈ X ∧ (vp (i + 1), false) ∉ X) ∨
        (∃ j ≤ r, w = vp j ∧ (vp j, false) ∈ X ∧ (vp j, true) ∉ X) := by
      intro u w hu hw huw
      simp only [XV, Finset.mem_filter, Finset.mem_univ, true_and] at hu hw
      by_cases hFuw : F (u, true) (w, false)
      · rcases hFuw with ⟨i, hi, h1, h2⟩ | ⟨_, _, h1, _⟩
        · have hu_eq : u = vp i := congrArg Prod.fst h1
          have hw_eq : w = vp (i + 1) := congrArg Prod.fst h2
          by_cases hwf : (vp (i + 1), false) ∈ X
          · right; exact ⟨i + 1, by omega, hw_eq, hwf, hw_eq ▸ hw⟩
          · left; exact ⟨i, hi, hu_eq, hw_eq, hu_eq ▸ hu, hwf⟩
        · exact absurd (congrArg Prod.snd h1) Bool.false_ne_true.symm
      · have hwf : (w, false) ∈ X := hX_closed _ hu _ (Or.inl ⟨Or.inr ⟨rfl, rfl, huw⟩, hFuw⟩)
        right
        by_contra hno_j; push Not at hno_j
        exact hw (hnonP_step w (fun j hj heq => (heq ▸ hw) (hno_j j hj heq (heq ▸ hwf))) hwf)
    -- Prefix property: if (vp 0, false) ∉ X, then NO node of P is in X → XV has no edges out → contradicts hconn!
    by_cases hv0f : (vp 0, false) ∈ X
    · -- Let k be the largest index ≤ r with (vp k, false) ∈ X
      let Sidx := (Finset.range (r + 1)).filter (fun i => (vp i, false) ∈ X)
      have hSne : Sidx.Nonempty := ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.succ_pos r), hv0f⟩⟩
      set k := Sidx.max' hSne
      have hk_mem : k ∈ Sidx := Finset.max'_mem Sidx hSne
      simp only [Sidx, Finset.mem_filter, Finset.mem_range] at hk_mem
      have hkr : k ≤ r := by omega
      have hkf : (vp k, false) ∈ X := hk_mem.2
      have hk_max : ∀ j, k < j → j ≤ r → (vp j, false) ∉ X := fun j hkj hjr hjX => by
        have := Finset.le_max' Sidx j (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hjX⟩); omega
      -- Then {vp k} separates a2 from b2!
      have hsep : IsSeparating G {vp k} := by
        refine isSeparating_of_closed_subset G
          ⟨a2, Finset.mem_erase.mpr ⟨hA_not_P a2 ha2A ha2ne k hkr, ha2_XV⟩⟩
          (Finset.disjoint_singleton_right.mpr (Finset.notMem_erase (vp k) XV))
          ⟨b2, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, by
            simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, not_or]
            exact ⟨fun h => hb2_not_XV h.2, hB_not_P b2 hb2B hb2ne k hkr⟩⟩⟩ ?_
        intro u hu w huw
        obtain ⟨huk, huXV⟩ := Finset.mem_erase.mp hu
        by_cases hwXV : w ∈ XV
        · by_cases hwk : w = vp k
          · exact Finset.mem_union_right _ (Finset.mem_singleton.mpr hwk)
          · exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hwk, hwXV⟩)
        · rw [Finset.mem_union]; right; rw [Finset.mem_singleton]
          rcases hedge_cross u w huXV hwXV huw with ⟨i, hir, rfl, rfl, hiX, hi1X⟩ | ⟨j, hjr, rfl, hjfX, hjtX⟩
          · -- (vp i, true) ∈ X ∧ (vp (i+1), false) ∉ X → i = k (so u = vp k, contradicting huk!)
            exfalso
            have hif : (vp i, false) ∈ X := hP_back_int i (le_of_lt hir) hiX
            have hik : i ≤ k := by by_contra hgt; exact hk_max i (by omega) (le_of_lt hir) hif
            by_cases hieq : i = k
            · exact huk (congrArg vp hieq)
            · -- i < k and (vp k, false) ∈ X → by backward induction (vp (i+1), false) ∈ X!
              apply hi1X
              have hback : ∀ d : ℕ, i + 1 + d ≤ k → (vp (i + 1 + d), false) ∈ X → (vp (i + 1), false) ∈ X := by
                intro d
                induction d with
                | zero => intro _ hX; simpa using hX
                | succ d ih =>
                  intro hle hX
                  have h1 : (vp (i + 1 + d), true) ∈ X := hP_back_fwd (i + 1 + d) (by omega) hX
                  have h2 : (vp (i + 1 + d), false) ∈ X := hP_back_int (i + 1 + d) (by omega) h1
                  exact ih (by omega) h2
              exact hback (k - (i + 1)) (by omega) (by rw [show i + 1 + (k - (i + 1)) = k by omega]; exact hkf)
          · -- (vp j, false) ∈ X ∧ (vp j, true) ∉ X → j = k!
            have hjk : j ≤ k := by by_contra hgt; exact hk_max j (by omega) hjr hjfX
            by_cases hjeq : j = k
            · rw [hjeq]
            · -- j < k and (vp k, false) ∈ X → (vp j, true) ∈ X by backward induction!
              exfalso; apply hjtX
              have hback : ∀ d : ℕ, j + 1 + d ≤ k → (vp (j + 1 + d), false) ∈ X → (vp j, true) ∈ X := by
                intro d
                induction d with
                | zero => intro _ hX; exact hP_back_fwd j (by omega) (by simpa using hX)
                | succ d ih =>
                  intro hle hX
                  have h1 : (vp (j + 1 + d), true) ∈ X := hP_back_fwd (j + 1 + d) (by omega) hX
                  have h2 : (vp (j + 1 + d), false) ∈ X := hP_back_int (j + 1 + d) (by omega) h1
                  exact ih (by omega) h2
              exact hback (k - (j + 1)) (by omega) (by rw [show j + 1 + (k - (j + 1)) = k by omega]; exact hkf)
      exact h2conn (vp k) hsep
    · -- (vp 0, false) ∉ X → no node of P is in X → XV has no edges out!
      have hno_P : ∀ i ≤ r, (vp i, false) ∉ X ∧ (vp i, true) ∉ X := by
        intro i hi
        induction i with
        | zero => exact ⟨hv0f, fun h => hv0f (hP_back_int 0 (Nat.zero_le r) h)⟩
        | succ i ih =>
          have ih' := ih (by omega)
          have h1 : (vp (i + 1), false) ∉ X := fun h => ih'.2 (hP_back_fwd i (by omega) h)
          have h2 : (vp (i + 1), true) ∉ X := fun h => h1 (hP_back_int (i + 1) hi h)
          exact ⟨h1, h2⟩
      obtain ⟨w⟩ := hconn a2 b2
      have hstay : ∀ {u v : V} (q : G.Walk u v), u ∈ XV → v ∈ XV := by
        intro u v q
        induction q with
        | nil => exact id
        | @cons u x v hux _ ih =>
          intro hu
          by_cases hx : x ∈ XV
          · exact ih hx
          · exfalso
            rcases hedge_cross u x hu hx hux with ⟨i, hi, _, _, hiX, _⟩ | ⟨j, hjr, _, hjfX, _⟩
            · exact (hno_P i (le_of_lt hi)).2 hiX
            · exact (hno_P j hjr).1 hjfX
      exact hb2_not_XV (hstay w ha2_XV)
  -- Step 4: Take a shortest augmenting path Q in R from Src to Snk
  have hex_list : ∃ n : ℕ, ∃ L : List (V × Bool),
      L.length = n ∧ L ≠ [] ∧ L.head! ∈ Src ∧ L.getLast! ∈ Snk ∧
      (∀ i (hi : i + 1 < L.length), R L[i] L[i + 1]) := by
    obtain ⟨s, hs, t, ht, hreach⟩ := hex_aug
    have hbuild : ∀ {x y : V × Bool}, ReachR x y →
        ∃ L : List (V × Bool), L ≠ [] ∧ L.head! = x ∧ L.getLast! = y ∧
          ∀ i (hi : i + 1 < L.length), R L[i] L[i + 1] := by
      intro x y hr
      induction hr using Relation.ReflTransGen.head_induction_on with
      | refl => exact ⟨[y], List.cons_ne_nil _ _, rfl, rfl, fun i hi => by simp at hi⟩
      | @head a b hab _ ih =>
        obtain ⟨L, hLne, hLh, hLl, hLadj⟩ := ih
        refine ⟨a :: L, List.cons_ne_nil _ _, rfl, ?_, ?_⟩
        · cases L with | nil => exact absurd rfl hLne | cons c cs => exact hLl
        · intro i hi
          cases i with
          | zero =>
            cases L with
            | nil => exact absurd rfl hLne
            | cons c cs => simp only [List.head!_cons] at hLh; simpa [hLh] using hab
          | succ i => exact hLadj i (by simpa using hi)
    obtain ⟨L, hne, hh, hl, hadj⟩ := hbuild hreach
    exact ⟨L.length, L, rfl, hne, hh ▸ hs, hl ▸ ht, hadj⟩
  let qlen := Nat.find hex_list
  obtain ⟨Q, hQlen, hQne, hQhead, hQlast, hQadj⟩ := Nat.find_spec hex_list
  have hQmin : ∀ L : List (V × Bool), L ≠ [] → L.head! ∈ Src → L.getLast! ∈ Snk →
      (∀ i (hi : i + 1 < L.length), R L[i] L[i + 1]) → qlen ≤ L.length :=
    fun L hne hh hl hadj => Nat.find_min' hex_list ⟨L, rfl, hne, hh, hl, hadj⟩
  have hQnodup : Q.Nodup := by
    rw [List.nodup_iff_injective_getElem]
    intro ⟨i, hi⟩ ⟨j, hj⟩ heq
    simp only [Fin.mk.injEq]
    by_contra hne
    wlog hlt : i < j generalizing i j
    · exact this j hj i hi heq.symm (Ne.symm hne) (by omega)
    let Q' := Q.take (i + 1) ++ Q.drop (j + 1)
    have hQ'len : Q'.length < qlen := by
      have hlt' : Q'.length < Q.length := by
        simp only [Q', List.length_append, List.length_take, List.length_drop]; omega
      omega
    have hQ'ne : Q' ≠ [] := by
      have hpos : 0 < Q'.length := by simp only [Q', List.length_append, List.length_take, List.length_drop]; omega
      intro h; rw [h] at hpos; simp at hpos
    have hQ'head : Q'.head! ∈ Src := by
      have : Q'.head! = Q.head! := by
        cases hQ : Q with | nil => exact absurd hQ hQne | cons x xs => simp [Q', hQ]
      rw [this]; exact hQhead
    have hQ'last : Q'.getLast! ∈ Snk := by
      have : Q'.getLast! = Q.getLast! := by
        by_cases hjlast : j + 1 < Q.length
        · have hne_d : Q.drop (j + 1) ≠ [] := by intro h; have := congrArg List.length h; simp at this; omega
          rw [show Q'.getLast! = (Q.drop (j + 1)).getLast! from by
            simp only [Q', List.getLast!_eq_getLast?_getD, List.getLast?_append_of_ne_nil _ hne_d]]
          rw [List.getLast!_eq_getLast?_getD, List.getLast!_eq_getLast?_getD, List.getLast?_drop, if_neg (by omega)]
        · have hj_eq : j = Q.length - 1 := by omega
          have hd_nil : Q.drop (j + 1) = [] := List.drop_eq_nil_of_le (by omega)
          have hQ'_eq : Q' = Q.take (i + 1) := by simp [Q', hd_nil]
          rw [hQ'_eq, List.getLast!_eq_getLast?_getD, List.getLast!_eq_getLast?_getD]
          have h1 : (Q.take (i + 1)).getLast? = some (Q[i]'hi) := by
            rw [List.getLast?_eq_getElem?, List.length_take, Nat.min_eq_left (by omega), Nat.add_sub_cancel,
              List.getElem?_take_of_lt (by omega : i < i + 1), List.getElem?_eq_getElem hi]
          have h2 : Q.getLast? = some (Q[j]'hj) := by
            rw [List.getLast?_eq_getElem?, ← hj_eq, List.getElem?_eq_getElem hj]
          have heq' : Q[i]'hi = Q[j]'hj := heq
          rw [h1, h2, heq']
      rw [this]; exact hQlast
    have hQ'adj : ∀ k (hk : k + 1 < Q'.length), R Q'[k] Q'[k + 1] := by
      intro k hk
      have hlen_t : (Q.take (i + 1)).length = i + 1 := List.length_take_of_le (by omega)
      by_cases hk1 : k + 1 < i + 1
      · have he1 : Q'[k] = Q[k]'(by omega) := by
          simp only [Q', List.getElem_append_left (by omega : k < (Q.take (i + 1)).length), List.getElem_take]
        have he2 : Q'[k + 1] = Q[k + 1]'(by omega) := by
          simp only [Q', List.getElem_append_left (by omega : k + 1 < (Q.take (i + 1)).length), List.getElem_take]
        rw [he1, he2]; exact hQadj k (by omega)
      · by_cases hk2 : k = i
        · subst k
          have he1 : Q'[i]'(Nat.lt_of_succ_lt hk) = Q[i]'hi := by
            simp only [Q', List.getElem_append_left (by omega : i < (Q.take (i + 1)).length), List.getElem_take]
          have he2 : Q'[i + 1]'hk = Q[j + 1]'(by simp [Q', hlen_t] at hk; omega) := by
            simp only [Q', List.getElem_append_right (by omega : (Q.take (i + 1)).length ≤ i + 1), hlen_t, Nat.sub_self, List.getElem_drop, Nat.add_zero]
          have heq' : Q[i]'hi = Q[j]'hj := heq
          rw [he1, he2, heq']; exact hQadj j (by simp [Q', hlen_t] at hk; omega)
        · have he1 : Q'[k] = Q[j + 1 + (k - (i + 1))]'(by simp [Q', hlen_t] at hk; omega) := by
            simp only [Q', List.getElem_append_right (by omega : (Q.take (i + 1)).length ≤ k), hlen_t, List.getElem_drop]
          have he2 : Q'[k + 1] = Q[j + 1 + (k - (i + 1)) + 1]'(by simp [Q', hlen_t] at hk; omega) := by
            simp only [Q', List.getElem_append_right (by omega : (Q.take (i + 1)).length ≤ k + 1), hlen_t, List.getElem_drop]
            congr 1; omega
          rw [he1, he2]; exact hQadj (j + 1 + (k - (i + 1))) (by simp [Q', hlen_t] at hk; omega)
    have := hQmin Q' hQ'ne hQ'head hQ'last hQ'adj
    omega
  obtain ⟨a2, ha2_mem, ha2_eq⟩ := Finset.mem_image.mp hQhead
  obtain ⟨ha2_ne, ha2A⟩ := Finset.mem_erase.mp ha2_mem
  obtain ⟨b2, hb2_mem, hb2_eq⟩ := Finset.mem_image.mp hQlast
  obtain ⟨hb2_ne, hb2B⟩ := Finset.mem_erase.mp hb2_mem
  have hQ_zero : Q[0]'(List.length_pos_of_ne_nil hQne) = (a2, false) := by
    have h0 : Q[0]'(List.length_pos_of_ne_nil hQne) = Q.head! := by
      cases Q with | nil => exact absurd rfl hQne | cons _ _ => rfl
    exact h0.trans ha2_eq.symm
  have hQ_last_elem : Q[Q.length - 1]'(by have := List.length_pos_of_ne_nil hQne; omega) = (b2, true) := by
    have hpos := List.length_pos_of_ne_nil hQne
    have hl : Q.getLast! = Q[Q.length - 1]'(by omega) := by
      rw [List.getLast!_eq_getLast?_getD, List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)]; rfl
    exact hl.symm.trans hb2_eq.symm
  -- Step 5: Symmetric difference F' of F and Q's arcs
  let Qarc (x y : V × Bool) : Prop :=
    ∃ k : ℕ, ∃ hk : k + 1 < Q.length, Q[k] = x ∧ Q[k + 1] = y
  let F' (x y : V × Bool) : Prop := (F x y ∧ ¬ Qarc y x) ∨ (Qarc x y ∧ ¬ F y x)
  have hF'_sub_D : ∀ x y, F' x y → D x y := by
    rintro x y (⟨hFxy, _⟩ | ⟨⟨k, hk, rfl, rfl⟩, hnotF⟩)
    · exact hF_sub_D x y hFxy
    · rcases hQadj k hk with ⟨hD, _⟩ | hFyx
      · exact hD
      · exact absurd hFyx hnotF
  have hQarc_out_uniq : ∀ x y1 y2, Qarc x y1 → Qarc x y2 → y1 = y2 := by
    rintro x y1 y2 ⟨k1, hk1, h1x, rfl⟩ ⟨k2, hk2, h2x, rfl⟩
    have : k1 = k2 := (List.Nodup.getElem_inj_iff hQnodup).mp (h1x.trans h2x.symm)
    subst this; rfl
  have hQarc_in_uniq : ∀ x1 x2 y, Qarc x1 y → Qarc x2 y → x1 = x2 := by
    rintro x1 x2 y ⟨k1, hk1, rfl, h1y⟩ ⟨k2, hk2, rfl, h2y⟩
    have : k1 + 1 = k2 + 1 := (List.Nodup.getElem_inj_iff hQnodup).mp (h1y.trans h2y.symm)
    have : k1 = k2 := by omega
    subst this; rfl
  have hF_out_uniq : ∀ x y1 y2, F x y1 → F x y2 → y1 = y2 := by
    rintro x y1 y2 (⟨i1, hi1, rfl, rfl⟩ | ⟨i1, hi1, rfl, rfl⟩) (⟨i2, hi2, h2, rfl⟩ | ⟨i2, hi2, h2, rfl⟩)
    · have := hvp_inj i1 i2 (le_of_lt hi1) (le_of_lt hi2) (congrArg Prod.fst h2); subst this; rfl
    · exact absurd (congrArg Prod.snd h2) Bool.false_ne_true.symm
    · exact absurd (congrArg Prod.snd h2) Bool.false_ne_true
    · have := hvp_inj i1 i2 hi1 hi2 (congrArg Prod.fst h2); subst this; rfl
  have hF_in_uniq : ∀ x1 x2 y, F x1 y → F x2 y → x1 = x2 := by
    rintro x1 x2 y (⟨i1, hi1, rfl, rfl⟩ | ⟨i1, hi1, rfl, rfl⟩) (⟨i2, hi2, rfl, h2⟩ | ⟨i2, hi2, rfl, h2⟩)
    · have := hvp_inj (i1 + 1) (i2 + 1) (by omega) (by omega) (congrArg Prod.fst h2)
      have : i1 = i2 := by omega
      subst this; rfl
    · exact absurd (congrArg Prod.snd h2) Bool.false_ne_true
    · exact absurd (congrArg Prod.snd h2) Bool.false_ne_true.symm
    · have := hvp_inj i1 i2 hi1 hi2 (congrArg Prod.fst h2); subst this; rfl
  -- Key cancellation: if F x y1 and Qarc x y2 (with ¬ F y2 x), then Qarc y1 x!
  have hF_Qarc_out_cancel : ∀ x y1 y2, F x y1 → Qarc x y2 → ¬ F y2 x → Qarc y1 x := by
    intro x y1 y2 hF1 hQ2 hnotF2
    obtain ⟨k, hk, hkx, hky2⟩ := hQ2
    have hk_pos : 0 < k := by
      by_contra h0
      have hk0 : k = 0 := by omega
      subst hk0
      have hx_a2 : x = (a2, false) := hkx.symm.trans hQ_zero
      subst hx_a2
      rcases hF1 with ⟨_, _, h1, _⟩ | ⟨i, hi, h1, _⟩
      · exact Bool.false_ne_true (congrArg Prod.snd h1)
      · exact hA_not_P a2 ha2A ha2_ne i hi (congrArg Prod.fst h1)
    have hRz : R (Q[k - 1]'(by omega)) x := by
      have := hQadj (k - 1) (by omega); convert this using 1; rw [← hkx]; congr 1; omega
    rcases hRz with ⟨hDzx, hnotFzx⟩ | hFxz
    · exfalso
      rcases hF1 with ⟨i, hi, rfl, rfl⟩ | ⟨i, hi, rfl, rfl⟩
      · rcases hDzx with ⟨hzf, _, hzeq⟩ | ⟨_, hft, _⟩
        · have hz_eq : Q[k - 1]'(by omega) = (vp i, false) := Prod.ext hzeq hzf
          exact hnotFzx (hz_eq.symm ▸ Or.inr ⟨i, le_of_lt hi, rfl, rfl⟩)
        · exact Bool.false_ne_true hft.symm
      · rcases hQadj k hk with ⟨hDxy2, hnotFxy2⟩ | hFy2x
        · rw [hkx, hky2] at hDxy2 hnotFxy2
          rcases hDxy2 with ⟨_, hy2t, hyeq⟩ | ⟨hft, _, _⟩
          · exact hnotFxy2 (Or.inr ⟨i, hi, rfl, Prod.ext hyeq.symm hy2t⟩)
          · exact Bool.false_ne_true hft
        · rw [hkx, hky2] at hFy2x; exact hnotF2 hFy2x
    · have hzy1 : Q[k - 1]'(by omega) = y1 := hF_out_uniq x _ y1 hFxz hF1
      exact ⟨k - 1, by omega, hzy1, by convert hkx using 1; congr 1; omega⟩
  -- Symmetric key cancellation: if F x1 y and Qarc x2 y (with ¬ F y x2), then Qarc y x1!
  have hF_Qarc_in_cancel : ∀ x1 x2 y, F x1 y → Qarc x2 y → ¬ F y x2 → Qarc y x1 := by
    intro x1 x2 y hF1 hQ2 hnotF2
    obtain ⟨k, hk, hkx2, hky⟩ := hQ2
    have hk_lt : k + 2 < Q.length := by
      by_contra hge
      have hkl : k + 1 = Q.length - 1 := by omega
      have hy_b2 : y = (b2, true) := hky.symm.trans (by
        rw [show Q[k + 1]'hk = Q[Q.length - 1]'(by omega) from by congr 1]; exact hQ_last_elem)
      subst hy_b2
      rcases hF1 with ⟨_, _, _, h2⟩ | ⟨i, hi, _, h2⟩
      · exact Bool.false_ne_true.symm (congrArg Prod.snd h2)
      · exact hB_not_P b2 hb2B hb2_ne i hi (congrArg Prod.fst h2)
    have hRz : R y (Q[k + 2]'hk_lt) := by
      have := hQadj (k + 1) hk_lt; rwa [hky] at this
    rcases hRz with ⟨hDyz, hnotFyz⟩ | hFzy
    · exfalso
      rcases hF1 with ⟨i, hi, rfl, rfl⟩ | ⟨i, hi, rfl, rfl⟩
      · rcases hDyz with ⟨_, hzt, hzeq⟩ | ⟨hft, _, _⟩
        · exact hnotFyz (Or.inr ⟨i + 1, by omega, rfl, Prod.ext hzeq.symm hzt⟩)
        · exact Bool.false_ne_true hft
      · rcases hQadj k hk with ⟨hDx2y, hnotFx2y⟩ | hFyx2
        · rw [hkx2, hky] at hDx2y hnotFx2y
          rcases hDx2y with ⟨hx2f, _, hxeq⟩ | ⟨_, hft, _⟩
          · exact hnotFx2y (Or.inr ⟨i, hi, Prod.ext hxeq hx2f, rfl⟩)
          · exact Bool.false_ne_true hft.symm
        · rw [hkx2, hky] at hFyx2; exact hnotF2 hFyx2
    · have hzx1 : Q[k + 2]'hk_lt = x1 := hF_in_uniq _ x1 y hFzy hF1
      exact ⟨k + 1, hk_lt, hky, hzx1⟩
  have hF'_out_uniq : ∀ x y1 y2, F' x y1 → F' x y2 → y1 = y2 := by
    rintro x y1 y2 (⟨hF1, hQ1⟩ | ⟨hQ1, hF1⟩) (⟨hF2, hQ2⟩ | ⟨hQ2, hF2⟩)
    · exact hF_out_uniq x y1 y2 hF1 hF2
    · exact absurd (hF_Qarc_out_cancel x y1 y2 hF1 hQ2 hF2) hQ1
    · exact absurd (hF_Qarc_out_cancel x y2 y1 hF2 hQ1 hF1) hQ2
    · exact hQarc_out_uniq x y1 y2 hQ1 hQ2
  have hF'_in_uniq : ∀ x1 x2 y, F' x1 y → F' x2 y → x1 = x2 := by
    rintro x1 x2 y (⟨hF1, hQ1⟩ | ⟨hQ1, hF1⟩) (⟨hF2, hQ2⟩ | ⟨hQ2, hF2⟩)
    · exact hF_in_uniq x1 x2 y hF1 hF2
    · exact absurd (hF_Qarc_in_cancel x1 x2 y hF1 hQ2 hF2) hQ1
    · exact absurd (hF_Qarc_in_cancel x2 x1 y hF2 hQ1 hF1) hQ2
    · exact hQarc_in_uniq x1 x2 y hQ1 hQ2
  -- No incoming F'-edges to (v0, false) or (a2, false)
  have hno_in_v0 : ∀ x, ¬ F' x (v0, false) := by
    rintro x (⟨hF, _⟩ | ⟨hQ, hnotF⟩)
    · rcases hF with ⟨i, hi, _, h2⟩ | ⟨_, _, _, h2⟩
      · have := hvp_inj (i + 1) 0 (by omega) (Nat.zero_le r) ((congrArg Prod.fst h2).symm.trans hvp0.symm); omega
      · exact Bool.false_ne_true (congrArg Prod.snd h2)
    · exact hnotF (Or.inr ⟨0, Nat.zero_le r, by rw [hvp0], by
        -- Wait: if Qarc x (v0, false) and ¬ F (v0, false) x, then Q enters (v0, false) from x,
        -- then Q leaves (v0, false)? Only D-edge out of (v0, false) is to (v0, true), which IS in F!
        -- So Q cannot leave (v0, false) at all! Wait: let's prove ¬ Qarc x (v0, false) directly!
        exfalso
        obtain ⟨k, hk, hkx, hkv0⟩ := hQ
        have hk_lt : k + 2 < Q.length := by
          by_contra hge
          have hkl : k + 1 = Q.length - 1 := by omega
          have h1 : (v0, false) = (b2, true) := hkv0.symm.trans (by
            rw [show Q[k + 1]'hk = Q[Q.length - 1]'(by omega) from by congr 1]; exact hQ_last_elem)
          exact Bool.false_ne_true (congrArg Prod.snd h1)
        rcases hQadj (k + 1) hk_lt with ⟨hD, hnotF'⟩ | hFback
        · rw [hkv0] at hD hnotF'
          rcases hD with ⟨_, hzt, hzeq⟩ | ⟨hft, _, _⟩
          · exact hnotF' (Or.inr ⟨0, Nat.zero_le r, by rw [hvp0], Prod.ext (hzeq.symm.trans hvp0.symm) hzt⟩)
          · exact Bool.false_ne_true hft
        · rw [hkv0] at hFback
          rcases hFback with ⟨i, hi, _, h2⟩ | ⟨_, _, _, h2⟩
          · have := hvp_inj (i + 1) 0 (by omega) (Nat.zero_le r) ((congrArg Prod.fst h2).symm.trans hvp0.symm); omega
          · exact Bool.false_ne_true (congrArg Prod.snd h2)⟩)
  have hno_in_a2 : ∀ x, ¬ F' x (a2, false) := by
    rintro x (⟨hF, _⟩ | ⟨⟨k, hk, _, hka2⟩, _⟩)
    · rcases hF with ⟨i, hi, _, h2⟩ | ⟨_, _, _, h2⟩
      · exact hA_not_P a2 ha2A ha2_ne (i + 1) (by omega) (congrArg Prod.fst h2)
      · exact Bool.false_ne_true (congrArg Prod.snd h2)
    · have := (List.Nodup.getElem_inj_iff hQnodup).mp (hka2.trans hQ_zero.symm)
      omega
  -- Continuation property: every node with an incoming F'-edge except (vr, true), (b2, true) has an outgoing F'-edge
  have hcont : ∀ x, (∃ w, F' w x) → x ≠ (vr, true) → x ≠ (b2, true) → ∃ y, F' x y := by
    rintro x ⟨w, hw⟩ hxvr hxb2
    rcases hw with ⟨hFwx, hnotQxw⟩ | ⟨hQwx, hnotFxw⟩
    · -- x is on P and x ≠ (vr, true), so F has an outgoing edge F x y!
      have hex_Fy : ∃ y, F x y := by
        rcases hFwx with ⟨i, hi, _, rfl⟩ | ⟨i, hi, _, rfl⟩
        · exact ⟨(vp (i + 1), true), Or.inr ⟨i + 1, by omega, rfl, rfl⟩⟩
        · by_cases hir : i < r
          · exact ⟨(vp (i + 1), false), Or.inl ⟨i, hir, rfl, rfl⟩⟩
          · exfalso; apply hxvr; rw [show i = r by omega, hvpr]
      obtain ⟨y, hFxy⟩ := hex_Fy
      by_cases hQyx : Qarc y x
      · obtain ⟨k, hk, hky, hkx⟩ := hQyx
        have hk_lt : k + 2 < Q.length := by
          by_contra hge
          have hkl : k + 1 = Q.length - 1 := by omega
          exact hxb2 (hkx.symm.trans (by
            rw [show Q[k + 1]'hk = Q[Q.length - 1]'(by omega) from by congr 1]; exact hQ_last_elem))
        refine ⟨Q[k + 2]'hk_lt, Or.inr ⟨⟨k + 1, hk_lt, hkx, rfl⟩, fun hFzx => ?_⟩⟩
        have hzw : Q[k + 2]'hk_lt = w := hF_in_uniq _ w x hFzx hFwx
        exact hnotQxw ⟨k + 1, hk_lt, hkx, hzw⟩
      · exact ⟨y, Or.inl ⟨hFxy, hQyx⟩⟩
    · obtain ⟨k, hk, hkw, hkx⟩ := hQwx
      have hk_lt : k + 2 < Q.length := by
        by_contra hge
        have hkl : k + 1 = Q.length - 1 := by omega
        exact hxb2 (hkx.symm.trans (by
          rw [show Q[k + 1]'hk = Q[Q.length - 1]'(by omega) from by congr 1]; exact hQ_last_elem))
      let z := Q[k + 2]'hk_lt
      by_cases hFzx : F z x
      · -- x has incoming F-edge F z x and x ≠ (vr, true), so F has outgoing edge F x y!
        have hex_Fy : ∃ y, F x y := by
          rcases hFzx with ⟨i, hi, _, rfl⟩ | ⟨i, hi, _, rfl⟩
          · exact ⟨(vp (i + 1), true), Or.inr ⟨i + 1, by omega, rfl, rfl⟩⟩
          · by_cases hir : i < r
            · exact ⟨(vp (i + 1), false), Or.inl ⟨i, hir, rfl, rfl⟩⟩
            · exfalso; apply hxvr; rw [show i = r by omega, hvpr]
        obtain ⟨y, hFxy⟩ := hex_Fy
        refine ⟨y, Or.inl ⟨hFxy, fun hQyx => ?_⟩⟩
        have hyw : y = w := hQarc_in_uniq y w x hQyx ⟨k, hk, hkw, hkx⟩
        exact hnotFxw (hyw ▸ hFxy)
      · exact ⟨z, Or.inr ⟨⟨k + 1, hk_lt, hkx, rfl⟩, hFzx⟩⟩
  -- Both sources (v0, false) and (a2, false) have outgoing F'-edges!
  have hout_v0 : ∃ y, F' (v0, false) y := by
    refine ⟨(v0, true), Or.inl ⟨Or.inr ⟨0, Nat.zero_le r, by rw [hvp0], by rw [hvp0]⟩, fun hQ => ?_⟩⟩
    obtain ⟨k, hk, _, hkv0⟩ := hQ
    have hk_lt : k + 2 < Q.length := by
      by_contra hge; have hkl : k + 1 = Q.length - 1 := by omega
      have h1 : (v0, false) = (b2, true) := hkv0.symm.trans (by
        rw [show Q[k + 1]'hk = Q[Q.length - 1]'(by omega) from by congr 1]; exact hQ_last_elem)
      exact Bool.false_ne_true (congrArg Prod.snd h1)
    rcases hQadj (k + 1) hk_lt with ⟨hD, hnotF'⟩ | hFback
    · rw [hkv0] at hD hnotF'
      rcases hD with ⟨_, hzt, hzeq⟩ | ⟨hft, _, _⟩
      · exact hnotF' (Or.inr ⟨0, Nat.zero_le r, by rw [hvp0], Prod.ext (hzeq.symm.trans hvp0.symm) hzt⟩)
      · exact Bool.false_ne_true hft
    · rw [hkv0] at hFback
      rcases hFback with ⟨i, hi, _, h2⟩ | ⟨_, _, _, h2⟩
      · have := hvp_inj (i + 1) 0 (by omega) (Nat.zero_le r) ((congrArg Prod.fst h2).symm.trans hvp0.symm); omega
      · exact Bool.false_ne_true (congrArg Prod.snd h2)
  have hout_a2 : ∃ y, F' (a2, false) y := by
    have hQlen2 : 1 < Q.length := by
      by_contra hle
      have h1 : Q.length = 1 := by have := List.length_pos_of_ne_nil hQne; omega
      have heq : Q.head! = Q.getLast! := by
        cases Q with | nil => exact absurd rfl hQne | cons x xs => cases xs with | nil => rfl | cons _ _ => simp at h1
      rw [← ha2_eq, ← hb2_eq] at heq
      exact Bool.false_ne_true (congrArg Prod.snd heq)
    refine ⟨Q[1], Or.inr ⟨⟨0, hQlen2, hQ_zero, rfl⟩, fun hF => ?_⟩⟩
    rcases hF with ⟨i, hi, _, h2⟩ | ⟨_, _, _, h2⟩
    · exact hA_not_P a2 ha2A ha2_ne (i + 1) (by omega) (congrArg Prod.fst h2)
    · exact Bool.false_ne_true (congrArg Prod.snd h2)
  -- Step 6: Trace F' from (v0, false) and from (a2, false)!
  obtain ⟨L1, hL1ne, hL1nd, hL1h, hL1adj, hL1end⟩ :=
    trace_functional_rel F' hF'_out_uniq hF'_in_uniq (v0, false) hno_in_v0
  obtain ⟨L2, hL2ne, hL2nd, hL2h, hL2adj, hL2end⟩ :=
    trace_functional_rel F' hF'_out_uniq hF'_in_uniq (a2, false) hno_in_a2
  have hL12_disj : L1.Disjoint L2 :=
    trace_disjoint F' hF'_in_uniq (fun h => ha2_ne (congrArg Prod.fst h).symm)
      hno_in_v0 hno_in_a2 hL1ne hL2ne hL1h hL2h hL1adj hL2adj
  -- Both traces must end in {(vr, true), (b2, true)}!
  have hL1_last : L1.getLast! = (vr, true) ∨ L1.getLast! = (b2, true) := by
    by_contra hnot; push Not at hnot
    have hL1_len2 : 1 < L1.length := by
      by_contra hle
      have hlen1 : L1.length = 1 := by have := List.length_pos_of_ne_nil hL1ne; omega
      have hlast : L1.getLast! = (v0, false) := by
        rw [← hL1h]; cases L1 with | nil => exact absurd rfl hL1ne | cons x xs => cases xs with | nil => rfl | cons _ _ => simp at hlen1
      obtain ⟨y, hy⟩ := hout_v0
      exact hL1end y (hlast ▸ hy)
    have hin : ∃ w, F' w L1.getLast! := by
      refine ⟨L1[L1.length - 2]'(by omega), ?_⟩
      have hlast_eq : L1.getLast! = L1[L1.length - 1]'(by omega) := by
        rw [List.getLast!_eq_getLast?_getD, List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)]; rfl
      rw [hlast_eq]; convert hL1adj (L1.length - 2) (by omega) using 1; congr 1; omega
    obtain ⟨y, hy⟩ := hcont L1.getLast! hin hnot.1 hnot.2
    exact hL1end y hy
  have hL2_last : L2.getLast! = (vr, true) ∨ L2.getLast! = (b2, true) := by
    by_contra hnot; push Not at hnot
    have hL2_len2 : 1 < L2.length := by
      by_contra hle
      have hlen1 : L2.length = 1 := by have := List.length_pos_of_ne_nil hL2ne; omega
      have hlast : L2.getLast! = (a2, false) := by
        rw [← hL2h]; cases L2 with | nil => exact absurd rfl hL2ne | cons x xs => cases xs with | nil => rfl | cons _ _ => simp at hlen1
      obtain ⟨y, hy⟩ := hout_a2
      exact hL2end y (hlast ▸ hy)
    have hin : ∃ w, F' w L2.getLast! := by
      refine ⟨L2[L2.length - 2]'(by omega), ?_⟩
      have hlast_eq : L2.getLast! = L2[L2.length - 1]'(by omega) := by
        rw [List.getLast!_eq_getLast?_getD, List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)]; rfl
      rw [hlast_eq]; convert hL2adj (L2.length - 2) (by omega) using 1; congr 1; omega
    obtain ⟨y, hy⟩ := hcont L2.getLast! hin hnot.1 hnot.2
    exact hL2end y hy
  -- Convert L1, L2 to vertex-disjoint simple paths in G, then trim to minimal A-B subpaths!
  have hL1_end_mem : L1.getLast! ∈ L1 := by
    rw [List.getLast!_eq_getLast?_getD, List.getLast?_eq_getElem?]
    have hpos : 0 < L1.length := List.length_pos_of_ne_nil hL1ne
    simp [List.getElem?_eq_getElem (by omega : L1.length - 1 < L1.length)]
  have hL2_end_mem : L2.getLast! ∈ L2 := by
    rw [List.getLast!_eq_getLast?_getD, List.getLast?_eq_getElem?]
    have hpos : 0 < L2.length := List.length_pos_of_ne_nil hL2ne
    simp [List.getElem?_eq_getElem (by omega : L2.length - 1 < L2.length)]
  have hfin : ∀ (t1 t2 : V), t1 ∈ B → t2 ∈ B →
      L1.getLast! = (t1, true) → L2.getLast! = (t2, true) →
      ∃ (a1 a2' b1 b2' : V) (p1 : G.Walk a1 b1) (p2 : G.Walk a2' b2'),
        a1 ∈ A ∧ a2' ∈ A ∧ a1 ≠ a2' ∧ b1 ∈ B ∧ b2' ∈ B ∧ b1 ≠ b2' ∧
        p1.IsPath ∧ p2.IsPath ∧ 1 ≤ p1.length ∧ 1 ≤ p2.length ∧
        Disjoint (walkVerts G p1) (walkVerts G p2) ∧
        (∀ w ∈ p1.support, w ≠ a1 → w ≠ b1 → w ∉ A ∧ w ∉ B) ∧
        (∀ w ∈ p2.support, w ≠ a2' → w ≠ b2' → w ∉ A ∧ w ∉ B) := by
    intro t1 t2 ht1B ht2B hL1t hL2t
    obtain ⟨q1, hq1_path, hq1_mem⟩ := walk_of_D_trace G L1 hL1ne hL1nd hL1h hL1t
      (fun i hi => hF'_sub_D _ _ (hL1adj i hi))
    obtain ⟨q2, hq2_path, hq2_mem⟩ := walk_of_D_trace G L2 hL2ne hL2nd hL2h hL2t
      (fun i hi => hF'_sub_D _ _ (hL2adj i hi))
    have hq_disj : Disjoint (walkVerts G q1) (walkVerts G q2) := Finset.disjoint_left.mpr fun w hw1 hw2 =>
      List.disjoint_left.mp hL12_disj (hq1_mem w ((mem_walkVerts G).mp hw1)).1 (hq2_mem w ((mem_walkVerts G).mp hw2)).1
    obtain ⟨a1, b1, p1, ha1A, hb1B, hp1_path, hp1_pos, hp1_sub, hp1_int⟩ := trim_path_between G hAB q1 hv0A ht1B
    obtain ⟨a2', b2', p2, ha2'A, hb2'B, hp2_path, hp2_pos, hp2_sub, hp2_int⟩ := trim_path_between G hAB q2 ha2A ht2B
    have hp_disj : Disjoint (walkVerts G p1) (walkVerts G p2) := hq_disj.mono hp1_sub hp2_sub
    have ha12 : a1 ≠ a2' := fun h =>
      Finset.disjoint_left.mp hp_disj ((mem_walkVerts G).mpr (Walk.start_mem_support p1))
        (h ▸ (mem_walkVerts G).mpr (Walk.start_mem_support p2))
    have hb12 : b1 ≠ b2' := fun h =>
      Finset.disjoint_left.mp hp_disj ((mem_walkVerts G).mpr (Walk.end_mem_support p1))
        (h ▸ (mem_walkVerts G).mpr (Walk.end_mem_support p2))
    exact ⟨a1, a2', b1, b2', p1, p2, ha1A, ha2'A, ha12, hb1B, hb2'B, hb12,
      hp1_path, hp2_path, hp1_pos, hp2_pos, hp_disj, hp1_int, hp2_int⟩
  rcases hL1_last with h1 | h1 <;> rcases hL2_last with h2 | h2
  · exact absurd (h1 ▸ hL1_end_mem) (fun hm => List.disjoint_left.mp hL12_disj hm (h2 ▸ hL2_end_mem))
  · exact hfin vr b2 hvrB hb2B h1 h2
  · exact hfin b2 vr hb2B hvrB h1 h2
  · exact absurd (h1 ▸ hL1_end_mem) (fun hm => List.disjoint_left.mp hL12_disj hm (h2 ▸ hL2_end_mem))


/-- Split a cycle c at two distinct vertices x, y ∈ walkVerts G c into two internally disjoint paths
p : x → y and q : y → x with p.length + q.length = c.length. -/
lemma split_cycle {v : V} {c : G.Walk v v} (hc : c.IsCycle)
    {x y : V} (hx : x ∈ walkVerts G c) (hy : y ∈ walkVerts G c) (hxy : x ≠ y) :
    ∃ (p : G.Walk x y) (q : G.Walk y x),
      p.IsPath ∧ q.IsPath ∧ 1 ≤ p.length ∧ 1 ≤ q.length ∧
      p.length + q.length = c.length ∧
      walkVerts G p ⊆ walkVerts G c ∧ walkVerts G q ⊆ walkVerts G c ∧
      (∀ w ∈ walkVerts G c, w ∈ p.support ∨ w ∈ q.support) ∧
      (∀ w, w ∈ p.support → w ∈ q.support → w = x ∨ w = y) := by
  have hx' : x ∈ c.support := (mem_walkVerts G).mp hx
  let c' : G.Walk x x := c.rotate x hx'
  have hc' : c'.IsCycle := hc.rotate hx'
  have hlen' : c'.length = c.length := Walk.length_rotate c x hx'
  have hmem_rot : ∀ w : V, w ∈ c'.support ↔ w ∈ c.support := fun w => Walk.mem_support_rotate_iff c x hx'
  have hy' : y ∈ c'.support := (hmem_rot y).mpr ((mem_walkVerts G).mp hy)
  let p : G.Walk x y := c'.takeUntil y hy'
  let q : G.Walk y x := c'.dropUntil y hy'
  have hspec : p.append q = c' := Walk.take_spec c' hy'
  have hp_path : p.IsPath := hc'.isPath_takeUntil hy'
  have hp_pos : 1 ≤ p.length := by
    cases hp : p with
    | nil => exact absurd rfl hxy
    | cons _ _ => simp
  have hq_pos : 1 ≤ q.length := by
    cases hq : q with
    | nil => exact absurd rfl hxy.symm
    | cons _ _ => simp
  have hq_path : q.IsPath := by
    have hp_not_nil : ¬ p.Nil := fun h => hxy (Walk.Nil.eq h)
    exact Walk.IsCycle.isPath_of_append_right hp_not_nil (by rw [hspec]; exact hc')
  have hsum : p.length + q.length = c.length := by
    rw [← hlen', ← hspec, Walk.length_append]
  have hp_sub : walkVerts G p ⊆ walkVerts G c := fun w hw =>
    (mem_walkVerts G).mpr ((hmem_rot w).mp (Walk.support_takeUntil_subset c' hy' ((mem_walkVerts G).mp hw)))
  have hq_sub : walkVerts G q ⊆ walkVerts G c := fun w hw =>
    (mem_walkVerts G).mpr ((hmem_rot w).mp (Walk.support_dropUntil_subset c' hy' ((mem_walkVerts G).mp hw)))
  have hcov : ∀ w ∈ walkVerts G c, w ∈ p.support ∨ w ∈ q.support := by
    intro w hw
    have hw' : w ∈ (p.append q).support := by rw [hspec]; exact (hmem_rot w).mpr ((mem_walkVerts G).mp hw)
    exact (Walk.mem_support_append_iff p q).mp hw'
  have hinter : ∀ w, w ∈ p.support → w ∈ q.support → w = x ∨ w = y := by
    intro w hwp hwq
    by_contra hnot; push Not at hnot
    -- w ∈ p.support.tail and w ∈ q.support.tail, contradicting c'.support.tail.Nodup!
    have hwp_t : w ∈ p.support.tail := by
      have h1 := p.cons_tail_support
      rw [← h1, List.mem_cons] at hwp
      exact hwp.resolve_left hnot.1
    have hwq_t : w ∈ q.support.tail := by
      have h1 := q.cons_tail_support
      rw [← h1, List.mem_cons] at hwq
      exact hwq.resolve_left hnot.2
    have hnd : c'.support.tail.Nodup := hc'.support_nodup
    rw [← hspec, Walk.tail_support_append, List.nodup_append'] at hnd
    exact List.disjoint_left.mp hnd.2.2 hwp_t hwq_t
  exact ⟨p, q, hp_path, hq_path, hp_pos, hq_pos, hsum, hp_sub, hq_sub, hcov, hinter⟩


/-- Concatenate two paths p : a → b and q : b → c that share only b into a path a → c. -/
lemma isPath_append_of_inter_eq {a b c : V} (p : G.Walk a b) (q : G.Walk b c)
    (hp : p.IsPath) (hq : q.IsPath) (hinter : ∀ w, w ∈ p.support → w ∈ q.support → w = b) :
    (p.append q).IsPath := by
  apply Walk.IsPath.mk'
  rw [Walk.support_append, List.nodup_append']
  refine ⟨hp.support_nodup, hq.support_nodup.tail, ?_⟩
  rw [List.disjoint_left]
  intro w hwp hwq
  have hwb : w = b := hinter w hwp (List.mem_of_mem_tail hwq)
  subst hwb
  have hnd := hq.support_nodup
  rw [← q.cons_tail_support, List.nodup_cons] at hnd
  exact hnd.1 hwq

end DeanLink

namespace DeanOdd

open SimpleGraph

/-
Split a walk at index `k`: `w = (prefix of length k) ++ (rest)`.
-/
set_option maxHeartbeats 2000000 in
theorem walk_split_at {V : Type*} {G : SimpleGraph V} {u v : V} (w : G.Walk u v)
    (k : ℕ) (hk : k ≤ w.length) :
    ∃ (w1 : G.Walk u (w.getVert k)) (w2 : G.Walk (w.getVert k) v),
      w = w1.append w2 ∧ w1.length = k := by
  exact ⟨w.take k, w.drop k, (w.append_take_drop_eq k).symm, by simp [hk]⟩

/-
A non-cycle closed walk of length `≥ 3` has a repeated vertex at two indices
`i < j < length`.
-/
set_option maxHeartbeats 2000000 in
theorem walk_vertex_repeat {V : Type*} {G : SimpleGraph V} {v : V} (w : G.Walk v v)
    (hcyc : ¬ w.IsCycle) (hlen : 3 ≤ w.length) :
    ∃ i j, i < j ∧ j < w.length ∧ w.getVert i = w.getVert j := by
  have h_not_path : ¬ w.tail.IsPath := by
    grind +suggestions;
  -- Since `w.tail` is not a path, there exist indices `a` and `b` such that `1 ≤ a < b ≤ w.length` and `w.getVert a = w.getVert b`.
  obtain ⟨a, b, hab⟩ : ∃ a b : ℕ, 1 ≤ a ∧ a < b ∧ b ≤ w.length ∧ w.getVert a = w.getVert b := by
    contrapose! h_not_path;
    have h_tail_nodup : List.Nodup (List.tail (w.support)) := by
      rw [ List.nodup_iff_getElem?_ne_getElem? ];
      grind +suggestions;
    convert! h_tail_nodup using 1;
    simp +decide [ SimpleGraph.Walk.isPath_def ];
    cases w <;> simp +decide [ SimpleGraph.Walk.support ];
  by_cases hb : b = w.length;
  · aesop;
  · exact ⟨ a, b, hab.2.1, lt_of_le_of_ne hab.2.2.1 hb, hab.2.2.2 ⟩

/-
**Odd closed walks contain odd cycles.**  From a closed walk of odd length
one can extract a cycle of odd length.
-/
set_option maxHeartbeats 2000000 in
theorem exists_odd_cycle_aux {V : Type*} (G : SimpleGraph V) (n : ℕ) :
    ∀ (v : V) (w : G.Walk v v), w.length = n → Odd n →
      ∃ (u : V) (c : G.Walk u u), c.IsCycle ∧ Odd c.length := by
  intro v w hw hn_odd
  induction' n using Nat.strong_induction_on with n ih generalizing v w;
  by_cases hw_cycle : w.IsCycle;
  · exact ⟨ v, w, hw_cycle, hw ▸ hn_odd ⟩;
  · -- Apply `walk_vertex_repeat` to find indices `i` and `j` such that `i < j < n` and `w.getVert i = w.getVert j =: x`.
    obtain ⟨i, j, hij, hjn, hx⟩ : ∃ i j, i < j ∧ j < n ∧ w.getVert i = w.getVert j := by
      convert! walk_vertex_repeat w hw_cycle _;
      · exact hw.symm;
      · rcases w with ( _ | ⟨ _, _, w ⟩ ) <;> simp_all +decide;
        · grind +extAll;
        · exact absurd ‹G.Adj v v› ( by simp +decide );
        · rcases n with ( _ | _ | _ | n ) <;> simp_all +arith +decide;
    -- Split `w` into three parts: `w1`, `c₁`, and `w3`.
    obtain ⟨w1, w2, hw1, hw2⟩ : ∃ w1 : G.Walk v (w.getVert i), ∃ w2 : G.Walk (w.getVert i) v, w = w1.append w2 ∧ w1.length = i := by
      exact walk_split_at w i ( by linarith )
    obtain ⟨c₁, w3, hc₁, hw3⟩ : ∃ c₁ : G.Walk (w.getVert i) (w.getVert i), ∃ w3 : G.Walk (w.getVert i) v, w2 = c₁.append w3 ∧ c₁.length = j - i := by
      have := walk_split_at w2 ( j - i ) ( by
        have := congr_arg SimpleGraph.Walk.length hw1; norm_num at this; omega; );
      grind +suggestions;
    -- Consider the two closed walks `c₁` and `c₂ = w3.append w1`.
    set c₂ : G.Walk (w.getVert i) (w.getVert i) := w3.append w1
    have hc₂ : c₂.length = n - (j - i) := by
      simp +zetaDelta at *;
      simp_all +decide [ SimpleGraph.Walk.length_append ];
      omega
    have hc₁_odd : Odd c₁.length ∨ Odd c₂.length := by
      grind +qlia
    generalize_proofs at *;
    grind

/- **No odd cycle implies 2-colorable.**  A simple graph in which every cycle
has even length is 2-colorable. -/
set_option maxHeartbeats 2000000 in
theorem colorable_two_of_cycle_even {V : Type*} (G : SimpleGraph V)
    (h : ∀ (v : V) (c : G.Walk v v), c.IsCycle → Even c.length) : G.Colorable 2 := by
  rw [SimpleGraph.two_colorable_iff_forall_loop_even]
  intro u w
  by_contra hodd
  rw [Nat.not_even_iff_odd] at hodd
  obtain ⟨x, c, hc, hcodd⟩ := exists_odd_cycle_aux G w.length u w rfl hodd
  exact (Nat.not_odd_iff_even.mpr (h x c hc)) hcodd

end DeanOdd

namespace OMA.R_Arxiv_2605_02731_dean_conjecture_R1

open SimpleGraph

private def inComponent {V : Type} (G : SimpleGraph V) {S : Set V} (r : S) : Set V :=
  {v | ∃ hv : v ∈ S, (G.induce S).Reachable r ⟨v, hv⟩}

private lemma mem_comp {V : Type} (G : SimpleGraph V) {S : Set V} (r v : S) :
    v.val ∈ inComponent G r ↔ (G.induce S).Reachable r v :=
  ⟨fun ⟨_, h⟩ => h, fun h => ⟨v.property, h⟩⟩

private lemma comp_subset {V : Type} (G : SimpleGraph V) {S : Set V} (r : S) :
    inComponent G r ⊆ S :=
  fun _ ⟨h, _⟩ => h

private lemma comp_closed {V : Type} {G : SimpleGraph V} {S : Set V} {r : S}
    {u v : V} (hu : u ∈ inComponent G r) (hv : v ∈ S) (ha : G.Adj u v) :
    v ∈ inComponent G r := by
  obtain ⟨huS, hru⟩ := hu
  have h : (G.induce S).Adj ⟨u, huS⟩ ⟨v, hv⟩ := ha
  exact ⟨hv, hru.trans h.reachable⟩

private lemma comp_conn {V : Type} {G : SimpleGraph V} {S : Set V} (r : S) :
    (G.induce (inComponent G r)).Connected := by
  rw [connected_iff_exists_forall_reachable]
  refine ⟨⟨r.val, ⟨r.property, .rfl⟩⟩, ?_⟩
  rintro ⟨v, hv, hrv⟩
  obtain ⟨p⟩ := hrv
  classical
  have all (w : S) (hw : w ∈ p.support) : w.val ∈ inComponent G r :=
    ⟨w.property, (p.takeUntil w hw).reachable⟩
  let f := SimpleGraph.Embedding.induce S (G := G)
  have hsub : ∀ w ∈ (p.map f.toHom).support, w ∈ inComponent G r := by
    simp only [Walk.support_map, List.mem_map]
    rintro _ ⟨w, hw, rfl⟩
    exact all w hw
  exact ⟨(p.map f.toHom).induce _ hsub⟩

private def twoConn {V : Type} (G : SimpleGraph V) : Prop :=
  G.Connected ∧ ∀ v : V, (G.induce {w | w ≠ v}).Connected

private lemma induce_compl_conn {V : Type} {G : SimpleGraph V} {S : Set V} {c : S}
    (h : ¬ (G.induce S |>.induce {w : S | w ≠ c}).Connected)
    (hne : ∃ v ∈ S, v ≠ c.val) :
    ∃ r t : {v : V | v ∈ S ∧ v ≠ c.val},
      ¬ (G.induce {v : V | v ∈ S ∧ v ≠ c.val}).Reachable r t := by
  let T := {v : V | v ∈ S ∧ v ≠ c.val}
  by_contra hn
  push Not at hn
  have hconn : (G.induce T).Connected := by
    obtain ⟨v, hv, hvc⟩ := hne
    let _ : Nonempty T := ⟨⟨v, hv, hvc⟩⟩
    exact Connected.mk hn
  apply h
  let f : G.induce T →g (G.induce S).induce {w : S | w ≠ c} :=
    ⟨fun v => ⟨⟨v, v.property.1⟩, fun he => v.property.2 (congrArg Subtype.val he)⟩,
     fun ha => ha⟩
  exact hconn.map f (by
    rintro ⟨⟨v, hv⟩, hvc⟩
    exact ⟨⟨v, hv, fun h => hvc (Subtype.ext h)⟩, rfl⟩)

private noncomputable def boundary {V : Type} [DecidableEq V] (G : SimpleGraph V)
    (B S : Finset V) : Finset V := by
  classical
  exact S.filter fun v => v ∈ B ∨ ∃ w ∉ S, G.Adj v w

private lemma mem_boundary {V : Type} [DecidableEq V] {G : SimpleGraph V}
    {B S : Finset V} {v : V} :
    v ∈ boundary G B S ↔ v ∈ S ∧ (v ∈ B ∨ ∃ w ∉ S, G.Adj v w) := by
  classical
  simp [boundary]

private lemma card_le_of_good {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    [DecidableRel G.Adj] {B S : Finset V} {v : V} {k : ℕ}
    (hdeg : ∀ w ∉ B, k ≤ (G.neighborSet w).ncard) (hv : v ∈ S) (hb : v ∉ boundary G B S) :
    k < S.card := by
  have hvB : v ∉ B := fun h => hb (mem_boundary.mpr ⟨hv, Or.inl h⟩)
  have hsub : G.neighborSet v ⊆ (S : Set V) := by
    intro w hw
    by_contra hs
    exact hb (mem_boundary.mpr ⟨hv, Or.inr ⟨w, hs, hw⟩⟩)
  let f (w : G.neighborSet v) : ↥(S.erase v) :=
    ⟨w, Finset.mem_erase.mpr ⟨(G.ne_of_adj w.property).symm, hsub w.property⟩⟩
  have hn := Fintype.card_le_of_injective f
    (fun _ _ e => Subtype.ext (congrArg (fun w : ↥(S.erase v) => w.val) e))
  rw [Set.fintypeCard_eq_ncard, Fintype.card_coe, Finset.card_erase_of_mem hv] at hn
  exact ((hdeg v hvB).trans hn).trans_lt
    (Nat.sub_lt (Finset.card_pos.mpr ⟨v, hv⟩) (by decide))

theorem exists_twoConn_core {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (B : Finset V) (k q : ℕ)
    (hq : 1 ≤ q) (hqk : q < k) (hB : B.card ≤ q)
    (hdeg : ∀ w ∉ B, k ≤ (G.neighborSet w).ncard) (hgood : ∃ v, v ∉ B) :
    ∃ S : Finset V, twoConn (G.induce (S : Set V)) ∧
      (boundary G B S).card ≤ q ∧ ∃ v ∈ S, v ∉ boundary G B S := by
  classical
  let P (S : Finset V) : Prop :=
    (boundary G B S).card ≤ q ∧ ∃ v ∈ S, v ∉ boundary G B S
  have hP : ∃ S, P S := by
    obtain ⟨v, hv⟩ := hgood
    have heq : boundary G B Finset.univ = B := by
      ext w
      simp [mem_boundary]
    exact ⟨Finset.univ, by rwa [heq], v, Finset.mem_univ _, by rwa [heq]⟩
  obtain ⟨S, hS, hmin⟩ := exists_minimalFor_of_wellFoundedLT P Finset.card hP
  obtain ⟨hbS, v, hv, hvb⟩ := hS
  have hlarge := card_le_of_good hdeg hv hvb
  have hconn : (G.induce (S : Set V)).Connected := by
    let r : (S : Set V) := ⟨v, hv⟩
    let T := inComponent G r
    let F := T.toFinset
    have hFT : (F : Set V) = T := Set.coe_toFinset T
    have hFsub : F ⊆ S := by
      intro w hw
      exact comp_subset G r ((Set.mem_toFinset).mp hw)
    have hvT : v ∈ F := Set.mem_toFinset.mpr ⟨hv, .rfl⟩
    have hbsub : boundary G B F ⊆ boundary G B S := by
      intro w hw
      rw [mem_boundary] at hw ⊢
      refine ⟨hFsub hw.1, hw.2.imp_right ?_⟩
      rintro ⟨u, hu, hwu⟩
      refine ⟨u, fun huS => hu ?_, hwu⟩
      exact Set.mem_toFinset.mpr (comp_closed (Set.mem_toFinset.mp hw.1) huS hwu)
    have hPF : P F := ⟨(Finset.card_le_card hbsub).trans hbS, v, hvT, fun h => hvb (hbsub h)⟩
    have heq : F = S := by
      apply Finset.eq_of_subset_of_card_le hFsub
      exact hmin hPF (Finset.card_le_card hFsub)
    have hc := comp_conn (G := G) r
    change (G.induce T).Connected at hc
    rwa [← hFT, heq] at hc
  refine ⟨S, ⟨hconn, ?_⟩, hbS, v, hv, hvb⟩
  intro c
  by_contra hcut
  have hex : ∃ t ∈ S, t ≠ c.val := by
    have : 1 < S.card := by omega
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp this
    by_cases h : a = c.val
    · exact ⟨b, hb, fun he => hab (h.trans he.symm)⟩
    · exact ⟨a, ha, h⟩
  let D := {w : V | w ∈ S ∧ w ≠ c.val}
  obtain ⟨r, t, hrt⟩ := induce_compl_conn hcut hex
  have hgoodD : ∃ u : D, u.val ∉ boundary G B S := by
    have hcsmall : (insert c.val (boundary G B S)).card ≤ q + 1 :=
      (Finset.card_insert_le _ _).trans (by omega)
    have hns : ¬ S ⊆ insert c.val (boundary G B S) :=
      fun h => by have := Finset.card_le_card h; omega
    obtain ⟨u, hu, hbad⟩ := Finset.not_subset.mp hns
    rw [Finset.mem_insert, not_or] at hbad
    exact ⟨⟨u, hu, hbad.1⟩, hbad.2⟩
  obtain ⟨u, hu⟩ := hgoodD
  have hpick : ∃ a b : D, a.val ∉ boundary G B S ∧
      ¬ (G.induce D).Reachable a b ∧
      ((boundary G B S).card < q ∨
        ∃ z ∈ boundary G B S, z ∉ inComponent G a) := by
    have hout : ∃ b : D, ¬ (G.induce D).Reachable u b := by
      by_cases h : (G.induce D).Reachable u r
      · exact ⟨t, fun ht => hrt (h.symm.trans ht)⟩
      · exact ⟨r, h⟩
    obtain ⟨b, hb⟩ := hout
    by_cases hsmall : (boundary G B S).card < q
    · exact ⟨u, b, hu, hb, Or.inl hsmall⟩
    by_cases hbad : ∃ z ∈ boundary G B S, z ∉ inComponent G u
    · exact ⟨u, b, hu, hb, Or.inr hbad⟩
    have hh : ∀ z ∈ boundary G B S, z ∈ inComponent G u := by
      push Not at hbad
      exact hbad
    have hb' : b.val ∉ boundary G B S := fun h =>
      hb ((mem_comp G u b).mp (hh b.val h))
    obtain ⟨z, hz⟩ := Finset.card_pos.mp (by omega : 0 < (boundary G B S).card)
    refine ⟨b, u, hb', fun h => hb h.symm, Or.inr ⟨z, hz, ?_⟩⟩
    intro hzb
    obtain ⟨hzD, huz⟩ := hh z hz
    obtain ⟨_, hbz⟩ := hzb
    exact hb (huz.trans hbz.symm)
  obtain ⟨a, b, ha, hab, hlimit⟩ := hpick
  let T := inComponent G a
  let F := insert c.val T.toFinset
  have hsub : F ⊆ S := by
    intro w hw
    rw [Finset.mem_insert] at hw
    rcases hw with rfl | hw
    · exact c.property
    · exact (comp_subset G a (Set.mem_toFinset.mp hw)).1
  have hbF : b.val ∉ F := by
    rw [Finset.mem_insert, not_or, Set.mem_toFinset]
    exact ⟨b.property.2, fun h => hab ((mem_comp G a b).mp h)⟩
  have hlt : F.card < S.card :=
    Finset.card_lt_card (Finset.ssubset_iff_of_subset hsub |>.mpr ⟨b, b.property.1, hbF⟩)
  have hbadF : boundary G B F ⊆ insert c.val ((boundary G B S).filter (· ∈ T)) := by
    intro w hw
    rw [mem_boundary] at hw
    have hwF : w = c.val ∨ w ∈ T := by simpa [F] using hw.1
    rcases hwF with rfl | hwT
    · exact Finset.mem_insert_self _ _
    apply Finset.mem_insert_of_mem
    rw [Finset.mem_filter, mem_boundary]
    refine ⟨⟨hsub hw.1, hw.2.imp_right ?_⟩, hwT⟩
    rintro ⟨z, hzF, hwz⟩
    refine ⟨z, fun hzS => hzF ?_, hwz⟩
    by_cases hzc : z = c.val
    · exact Finset.mem_insert.mpr (Or.inl hzc)
    · exact Finset.mem_insert_of_mem (Set.mem_toFinset.mpr
        (comp_closed hwT ⟨hzS, hzc⟩ hwz))
  have hcard : (boundary G B F).card ≤ q := by
    apply (Finset.card_le_card hbadF).trans
    apply (Finset.card_insert_le _ _).trans
    rcases hlimit with hlim | ⟨z, hz, hzT⟩
    · have := Finset.card_filter_le (s := boundary G B S) (p := (· ∈ T))
      omega
    · have hl := Finset.card_lt_card (Finset.filter_ssubset.mpr ⟨z, hz, hzT⟩)
      change ((boundary G B S).filter (· ∈ T)).card < (boundary G B S).card at hl
      omega
  have haT : a.val ∈ T := ⟨a.property, .rfl⟩
  have haF : a.val ∈ F := Finset.mem_insert_of_mem (Set.mem_toFinset.mpr haT)
  have haBad : a.val ∉ boundary G B F := by
    intro h
    rcases Finset.mem_insert.mp (hbadF h) with hc | hm
    · exact a.property.2 hc
    · exact ha (Finset.mem_filter.mp hm).1
  exact (not_le_of_gt hlt) (hmin (show P F from ⟨hcard, a, haF, haBad⟩) hlt.le)

private def HasCycle {V : Type} (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ (v : V) (p : G.Walk v v), p.IsCycle ∧ k ∣ p.length

private def PathOfLength {V : Type} (G : SimpleGraph V) (x y : V) (n : ℕ) : Prop :=
  ∃ p : G.Walk x y, p.IsPath ∧ p.length = n

lemma combine {V : Type} {G : SimpleGraph V} {x y : V} {p q : G.Walk x y}
    (hp : p.IsPath) (hq : q.IsPath) (hl : 1 < p.length ∨ 1 < q.length)
    (hinter : ∀ z ∈ p.support, z ∈ q.support → z = x ∨ z = y) :
    (p.append q.reverse).IsCycle := by
  apply hp.isCycle_append hq.reverse ?_ (by simpa using hl)
  apply List.disjoint_left.mpr
  intro z hzp hzq
  have hqp : z ∈ q.support := by
    simpa only [Walk.support_reverse, List.mem_reverse] using List.mem_of_mem_tail hzq
  rcases hinter z (List.mem_of_mem_tail hzp) hqp with rfl | rfl
  · exact (List.nodup_cons.mp (show (_ :: p.support.tail).Nodup by
      simpa only [Walk.cons_tail_support] using hp.support_nodup)).1 hzp
  · exact (List.nodup_cons.mp (show (_ :: q.reverse.support.tail).Nodup by
      simpa only [Walk.cons_tail_support] using hq.reverse.support_nodup)).1 hzq

private lemma add_mod_complement (a k : ℕ) (hk : 0 < k) :
    k ∣ a + (k - a % k) % k := by
  have hlt := Nat.mod_lt a hk
  rw [Nat.dvd_iff_mod_eq_zero]
  rw [Nat.add_mod]
  by_cases hz : a % k = 0
  · simp [hz]
  · rw [Nat.mod_mod, Nat.mod_eq_of_lt (show k - a % k < k by omega)]
    have he : a % k + (k - a % k) = k := by omega
    rw [he, Nat.mod_self]

private lemma one_step (k a t : ℕ) (hk : 5 ≤ k) (ht : t = 1 ∨ t = 2) :
    ∃ i < k - 1, ∃ j < k - 1, k ∣ a + i + t * j := by
  let r := (k - a % k) % k
  have hr : r < k := Nat.mod_lt _ (by omega)
  have hd : k ∣ a + r := add_mod_complement a k (by omega)
  by_cases h : r < k - 1
  · exact ⟨r, h, 0, by omega, by simpa using hd⟩
  · refine ⟨r - t, by omega, 1, by omega, ?_⟩
    rw [Nat.mul_one, show a + (r - t) + t = a + r by omega]
    exact hd

lemma pair_step (k a s t : ℕ) (hk : 5 ≤ k)
    (hs : s = 1 ∨ s = 2) (ht : t = 1 ∨ t = 2) :
    (∃ i < k - 1, ∃ j < k - 1, k ∣ a + s * i + t * j) ∨
      (Even k ∧ Odd a ∧ s = 2 ∧ t = 2) := by
  rcases hs with rfl | rfl
  · exact Or.inl (by simpa using one_step k a t hk ht)
  rcases ht with rfl | rfl
  · obtain ⟨j, hj, i, hi, hd⟩ := one_step k a 2 hk (Or.inr rfl)
    exact Or.inl ⟨i, hi, j, hj, by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hd⟩
  let r := (k - a % k) % k
  have hr : r < k := Nat.mod_lt _ (by omega)
  have hd : k ∣ a + r := add_mod_complement a k (by omega)
  by_cases hke : Even k
  · by_cases hae : Even a
    · obtain ⟨b, hb⟩ := hae
      obtain ⟨c, hc⟩ := hke
      let u := (c - b % c) % c
      have hlu : u < c := Nat.mod_lt _ (by omega)
      obtain ⟨m, hm⟩ := add_mod_complement b c (by omega)
      refine Or.inl ⟨u, by omega, 0, by omega, m, ?_⟩
      change b + u = c * m at hm
      rw [hc, Nat.add_mul]
      omega
    · exact Or.inr ⟨hke, Nat.not_even_iff_odd.mp hae, rfl, rfl⟩
  · have hko : k % 2 = 1 := by simpa [Nat.even_iff] using hke
    let u := if r % 2 = 0 then r else r + k
    have hue : u % 2 = 0 := by simp only [u]; split <;> omega
    have hlu : u / 2 ≤ 2 * (k - 2) := by simp only [u]; split <;> omega
    have hdu : k ∣ a + u := by
      simp only [u]
      split
      · exact hd
      · rw [← Nat.add_assoc]
        exact dvd_add hd (dvd_refl k)
    let i := min (u / 2) (k - 2)
    let j := u / 2 - i
    have hij : i + j = u / 2 := by dsimp [j, i]; omega
    have hi : i < k - 1 := by dsimp [i]; omega
    have hj : j < k - 1 := by dsimp [j, i]; omega
    exact Or.inl ⟨i, hi, j, hj, by
      rw [show a + 2 * i + 2 * j = a + u by omega]
      exact hdu⟩


private lemma preserves_reachable {A B : Type} {G : SimpleGraph A} {H : SimpleGraph B}
    (f : A → B) (hf : ∀ ⦃a b⦄, G.Adj a b → H.Reachable (f a) (f b))
    {a b : A} (h : G.Reachable a b) : H.Reachable (f a) (f b) := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => exact .rfl
  | cons hadj _ ih => exact (hf hadj).trans ih

private def addEdge {V : Type} (G : SimpleGraph V) (x y : V) : SimpleGraph V where
  Adj a b := G.Adj a b ∨ (x ≠ y ∧ ((a = x ∧ b = y) ∨ (a = y ∧ b = x)))
  symm := ⟨fun a b h => by
    rcases h with h | ⟨hxy, h⟩
    · exact Or.inl h.symm
    · exact Or.inr ⟨hxy, by tauto⟩⟩
  loopless := ⟨fun a h => by
    rcases h with h | ⟨hxy, h⟩
    · exact G.loopless.irrefl a h
    · rcases h with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
      · exact hxy (h₁.symm.trans h₂)
      · exact hxy (h₂.symm.trans h₁)⟩

private def side {V : Type} (x y : V) (M : Set V) : Set V := {v | v = x ∨ v = y ∨ v ∈ M}

private lemma sideConnected {V : Type} {G : SimpleGraph V} {x y : V}
    {M D : Set V} (hxy : x ≠ y)
    (hclosed : ∀ ⦃a b⦄, a ∈ M → b ≠ x → b ≠ y → G.Adj a b → b ∈ M)
    (hD : (G.induce D).Connected) {r : V} (hr : r = x ∨ r = y) (hrD : r ∈ D) :
    ((addEdge G x y).induce (D ∩ side x y M)).Connected := by
  classical
  let S := side x y M
  let H := (addEdge G x y).induce (D ∩ S)
  have hrS : r ∈ S := hr.imp_right Or.inl
  let root : ↥(D ∩ S) := ⟨r, hrD, hrS⟩
  let f (v : D) : ↥(D ∩ S) := if hv : v.val ∈ S then ⟨v.val, v.property, hv⟩ else root
  have hf : ∀ ⦃a b : D⦄, (G.induce D).Adj a b → H.Reachable (f a) (f b) := by
    intro a b hab
    change G.Adj a.val b.val at hab
    have root_reach {v : V} (hvD : v ∈ D) (hvS : v ∈ S)
        (hv : v = x ∨ v = y) : H.Reachable ⟨v, hvD, hvS⟩ root := by
      rcases hv with hv | hv <;> rcases hr with hr | hr
      · rw [show (⟨v, hvD, hvS⟩ : ↥(D ∩ S)) = root from Subtype.ext (hv.trans hr.symm)]
      · exact (show H.Adj ⟨v, hvD, hvS⟩ root from Or.inr ⟨hxy, Or.inl ⟨hv, hr⟩⟩).reachable
      · exact (show H.Adj ⟨v, hvD, hvS⟩ root from Or.inr ⟨hxy, Or.inr ⟨hv, hr⟩⟩).reachable
      · rw [show (⟨v, hvD, hvS⟩ : ↥(D ∩ S)) = root from Subtype.ext (hv.trans hr.symm)]
    have adj_to_out {u v : V} (hu : u ∈ S) (hv : v ∉ S) (h : G.Adj u v) :
        u = x ∨ u = y := by
      rcases hu with he | he | hm
      · exact Or.inl he
      · exact Or.inr he
      · exact (hv (Or.inr (Or.inr (hclosed hm
          (fun e => hv (Or.inl e)) (fun e => hv (Or.inr (Or.inl e))) h)))).elim
    by_cases ha : a.val ∈ S <;> by_cases hb : b.val ∈ S
    · rw [show f a = ⟨a.val, a.property, ha⟩ by simp [f, ha],
          show f b = ⟨b.val, b.property, hb⟩ by simp [f, hb]]
      exact (show H.Adj ⟨a.val, a.property, ha⟩ ⟨b.val, b.property, hb⟩ from
        Or.inl hab).reachable
    · simpa only [f, dif_pos ha, dif_neg hb] using root_reach a.property ha (adj_to_out ha hb hab)
    · simpa only [f, dif_neg ha, dif_pos hb] using
        (root_reach b.property hb (adj_to_out hb ha hab.symm)).symm
    · simp [f, ha, hb]
  let _ : Nonempty (D ∩ S : Set V) := ⟨root⟩
  apply Connected.mk
  intro a b
  have he (z : ↥(D ∩ S)) : f ⟨z.val, z.property.1⟩ = z := by simp [f, z.property.2]
  simpa only [he] using preserves_reachable f hf
    (hD ⟨a.val, a.property.1⟩ ⟨b.val, b.property.1⟩)

private lemma sideTwoConn {V : Type} {G : SimpleGraph V} {x y : V} {M : Set V}
    (hxy : x ≠ y) (hG : twoConn G)
    (hclosed : ∀ ⦃a b⦄, a ∈ M → b ≠ x → b ≠ y → G.Adj a b → b ∈ M) :
    twoConn (addEdge (G.induce (side x y M))
      ⟨x, Or.inl rfl⟩ ⟨y, Or.inr (Or.inl rfl)⟩) := by
  let S := side x y M
  let R : S := ⟨x, Or.inl rfl⟩
  let T : S := ⟨y, Or.inr (Or.inl rfl)⟩
  let H := addEdge (G.induce S) R T
  have heq : H = (addEdge G x y).induce S := by
    ext a b
    change
      (G.Adj a.val b.val ∨ (R ≠ T ∧
        ((a = R ∧ b = T) ∨ (a = T ∧ b = R)))) ↔
      (G.Adj a.val b.val ∨ (x ≠ y ∧
        ((a.val = x ∧ b.val = y) ∨ (a.val = y ∧ b.val = x))))
    rw [← Subtype.coe_ne_coe]
    simp only [Subtype.ext_iff]
    rfl
  change twoConn H
  rw [heq]
  constructor
  · let f : G →g G.induce Set.univ := ⟨fun v => ⟨v, Set.mem_univ _⟩, fun h => h⟩
    have hconn := hG.1.map f (fun v => ⟨v.val, Subtype.ext rfl⟩)
    change ((addEdge G x y).induce (side x y M)).Connected
    have hc := sideConnected hxy hclosed hconn
      (Or.inl rfl : x = x ∨ x = y) (Set.mem_univ x)
    rwa [Set.univ_inter] at hc
  · intro c
    let D := {v : V | v ≠ c.val}
    have hex : ∃ r, (r = x ∨ r = y) ∧ r ∈ D := by
      by_cases h : x = c.val
      · exact ⟨y, Or.inr rfl, fun h' => hxy (h.trans h'.symm)⟩
      · exact ⟨x, Or.inl rfl, h⟩
    obtain ⟨r, hr, hrD⟩ := hex
    have hconn := sideConnected hxy hclosed (hG.2 c.val) hr hrD
    let f : (addEdge G x y).induce (D ∩ S) →g
        ((addEdge G x y).induce S).induce {w : S | w ≠ c} :=
      ⟨fun v => ⟨⟨v.val, v.property.2⟩,
        fun he => v.property.1 (congrArg Subtype.val he)⟩, fun h => h⟩
    exact hconn.map f (by
      rintro ⟨⟨v, hv⟩, hvc⟩
      exact ⟨⟨v, fun he => hvc (Subtype.ext he), hv⟩, rfl⟩)

private lemma ncard_induce {V : Type} {G : SimpleGraph V} {S : Set V} (v : S)
    (h : G.neighborSet v.val ⊆ S) :
    ((G.induce S).neighborSet v).ncard = (G.neighborSet v.val).ncard := by
  apply Set.ncard_congr'
  exact {
    toFun := fun w => ⟨w.val.val, w.property⟩
    invFun := fun w => ⟨⟨w.val, h w.property⟩, w.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }

private def cutOutside {V : Type} (x y : V) : Set V := {v | v ≠ x ∧ v ≠ y}

private def EssentialCut {V : Type} (G : SimpleGraph V) : Prop :=
  ∃ (x y : V) (_ : x ≠ y) (a b : cutOutside x y),
    ¬ (G.induce (cutOutside x y)).Reachable a b ∧
    (inComponent G a).Nontrivial ∧ (inComponent G b).Nontrivial

private lemma comp_disjoint {V : Type} {G : SimpleGraph V} {D : Set V} {a b : D}
    (h : ¬ (G.induce D).Reachable a b) : Disjoint (inComponent G a) (inComponent G b) := by
  rw [Set.disjoint_left]
  rintro v ⟨hv, hav⟩ ⟨_, hbv⟩
  exact h (hav.trans hbv.symm)

private lemma four_side {V : Type} [Finite V] {G : SimpleGraph V} {x y : V}
    (hxy : x ≠ y) {a : cutOutside x y} (ha : (inComponent G a).Nontrivial) :
    4 ≤ (side x y (inComponent G a)).ncard := by
  obtain ⟨u, hu, v, hv, huv⟩ := ha
  have hu' : u ≠ x ∧ u ≠ y := comp_subset G a hu
  have hv' : v ≠ x ∧ v ≠ y := comp_subset G a hv
  have hsub : ({x, y, u, v} : Set V) ⊆ side x y (inComponent G a) := by
    intro w hw
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
    rcases hw with rfl | rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr hu)
    · exact Or.inr (Or.inr hv)
  classical
  have hl := Set.ncard_le_ncard hsub
  have hcard : ({x, y, u, v} : Set V).ncard = 4 := by
    rw [Set.ncard_insert_of_notMem, Set.ncard_insert_of_notMem, Set.ncard_pair huv]
    · simp [hu'.2.symm, hv'.2.symm]
    · simp [hxy, hu'.1.symm, hv'.1.symm]
  rw [hcard] at hl
  exact hl



private lemma cycle_lift {U V : Type} {G : SimpleGraph U} {J : SimpleGraph V}
    (f : G ↪g J) {k : ℕ} (h : HasCycle G k) : HasCycle J k := by
  obtain ⟨v, p, hp, hd⟩ := h
  exact ⟨f v, p.map f.toHom, hp.map f.injective, by simpa using hd⟩

private lemma supported_map {V : Type} {G : SimpleGraph V} {S : Set V}
    {x y : S} (p : (G.induce S).Walk x y) :
    ∀ v ∈ (p.map (Embedding.induce S).toHom).support, v ∈ S := by
  simp only [Walk.support_map, List.mem_map]
  rintro v ⟨w, _, rfl⟩
  exact w.property

private lemma glue_sides {V : Type} {G : SimpleGraph V} {x y : V} {M N : Set V}
    (hdisj : Disjoint M N) {m n : ℕ} (hmn : 1 < m ∨ 1 < n)
    (hp : PathOfLength (G.induce (side x y M)) ⟨x, Or.inl rfl⟩ ⟨y, Or.inr (Or.inl rfl)⟩ m)
    (hq : PathOfLength (G.induce (side x y N)) ⟨x, Or.inl rfl⟩ ⟨y, Or.inr (Or.inl rfl)⟩ n)
    {k : ℕ} (hd : k ∣ m + n) : HasCycle G k := by
  obtain ⟨p, hpp, hpl⟩ := hp
  obtain ⟨q, hqp, hql⟩ := hq
  let f : G.induce (side x y M) ↪g G := Embedding.induce _
  let g : G.induce (side x y N) ↪g G := Embedding.induce _
  let a : G.Walk x y := p.map f.toHom
  let b : G.Walk x y := q.map g.toHom
  have hla : a.length = m := by
    change (p.map f.toHom).length = m
    rw [Walk.length_map, hpl]
  have hlb : b.length = n := by
    change (q.map g.toHom).length = n
    rw [Walk.length_map, hql]
  refine ⟨x, a.append b.reverse, ?_, ?_⟩
  · have ha : a.IsPath := hpp.map (f := f.toHom) f.injective
    have hb : b.IsPath := hqp.map (f := g.toHom) g.injective
    apply combine ha hb (by rwa [hla, hlb])
    intro v hva hvb
    have hm := supported_map p v hva
    have hn := supported_map q v hvb
    rcases hm with rfl | rfl | hm
    · exact Or.inl rfl
    · exact Or.inr rfl
    rcases hn with rfl | rfl | hn
    · exact Or.inl rfl
    · exact Or.inr rfl
    exact (Set.disjoint_left.mp hdisj hm hn).elim
  · simpa only [Walk.length_append, Walk.length_reverse, hla, hlb] using hd

private lemma even_modulus_step (k a : ℕ) (hk : 5 ≤ k) (hke : Even k) (ha : Even a) :
    ∃ i < k - 1, k ∣ a + 2 * i := by
  obtain ⟨b, hb⟩ := ha
  obtain ⟨c, hc⟩ := hke
  let u := (c - b % c) % c
  have hlu : u < c := Nat.mod_lt _ (by omega)
  obtain ⟨m, hm⟩ := add_mod_complement b c (by omega)
  refine ⟨u, by omega, m, ?_⟩
  change b + u = c * m at hm
  rw [hc, Nat.add_mul]
  omega

private lemma good_in_induced {V : Type} [DecidableEq V] {G : SimpleGraph V} {B S : Finset V}
    {k : ℕ} (hd : ∀ v ∉ B, k ≤ (G.neighborSet v).ncard) (v : ↥(S : Set V))
    (hv : v.val ∉ boundary G B S) :
    k ≤ ((G.induce (S : Set V)).neighborSet v).ncard := by
  have hvB : v.val ∉ B := fun h => hv (mem_boundary.mpr ⟨v.property, Or.inl h⟩)
  have hs : G.neighborSet v.val ⊆ (S : Set V) := by
    intro w hw
    by_contra hwS
    exact hv (mem_boundary.mpr ⟨v.property, Or.inr ⟨w, hwS, hw⟩⟩)
  rw [ncard_induce v hs]
  exact hd v.val hvB

private lemma bad_subtype_card {V : Type} [DecidableEq V] {G : SimpleGraph V} {B S : Finset V} :
    ((boundary G B S).subtype (· ∈ (S : Set V))).card = (boundary G B S).card := by
  rw [Finset.card_subtype]
  congr 1
  apply Finset.filter_eq_self.mpr
  intro v hv
  exact (mem_boundary.mp hv).1


private lemma cycle_of_copy {V : Type} {G : SimpleGraph V} {n k : ℕ}
    (hn : 2 < n) (h : cycleGraph n ⊑ G) (hd : k ∣ n) : HasCycle G k := by
  obtain ⟨v, p, hp, rfl⟩ := (cycleGraph_isContained_iff hn).mp h
  exact ⟨v, p, hp, hd⟩

private lemma cycle_of_clique {V : Type} {G : SimpleGraph V} {k : ℕ}
    (hk : 3 ≤ k) (h : completeGraph (Fin k) ⊑ G) : HasCycle G k :=
  cycle_of_copy (by omega) ((IsContained.of_le le_top).trans h) (dvd_refl k)

private lemma even_cycle_in_biclique (k : ℕ) :
    cycleGraph (2 * k) ⊑ completeBipartiteGraph (Fin k) (Fin k) := by
  let h (i : Fin (2 * k)) : Fin k := ⟨i.val / 2, by have := i.isLt; omega⟩
  let f (i : Fin (2 * k)) : Fin k ⊕ Fin k :=
    if i.val % 2 = 0 then Sum.inl (h i) else Sum.inr (h i)
  have hinj : Function.Injective f := by
    intro i j he
    have agree : h i = h j → i.val % 2 = j.val % 2 → i = j := by
      intro hval hpar
      have hdiv : i.val / 2 = j.val / 2 := congrArg Fin.val hval
      apply Fin.ext
      omega
    by_cases hi : i.val % 2 = 0 <;> by_cases hj : j.val % 2 = 0 <;>
      simp [f, hi, hj] at he
    · exact agree he (hi.trans hj.symm)
    · exact agree he (by omega)
  have hpar : ∀ {i j : Fin (2 * k)}, (i - j).val = 1 → i.val % 2 ≠ j.val % 2 := by
    intro i j hh
    have hh' := congrArg (fun n : ℕ => n % 2) hh
    rw [Fin.val_sub, Nat.mod_mod_of_dvd _ (dvd_mul_right 2 k)] at hh'
    have hi := i.isLt
    have hj := j.isLt
    omega
  refine ⟨⟨⟨f, ?_⟩, hinj⟩⟩
  intro i j hij
  have hp : i.val % 2 ≠ j.val % 2 :=
    (cycleGraph_adj'.mp hij).elim hpar (fun h => (hpar h).symm)
  by_cases hi : i.val % 2 = 0
  · have hj : j.val % 2 ≠ 0 := fun e => hp (hi.trans e.symm)
    simp [f, hi, hj]
  · have hj : j.val % 2 = 0 := by omega
    simp [f, hi, hj]

private lemma cycle_of_biclique {V : Type} {G : SimpleGraph V} {k : ℕ}
    (hk : 3 ≤ k) (h : completeBipartiteGraph (Fin k) (Fin k) ⊑ G) : HasCycle G k :=
  cycle_of_copy (by omega) ((even_cycle_in_biclique k).trans h) (dvd_mul_left k 2)


private def threeConn {V : Type} (G : SimpleGraph V) : Prop :=
  twoConn G ∧ ∀ x y : V, x ≠ y → (G.induce (cutOutside x y)).Connected

private def weakGraph {V : Type} (k : ℕ) (G : SimpleGraph V) (z : V) : Prop :=
  threeConn G ∨
    ∃ x y : V, x ≠ y ∧ G.neighborSet z = {x, y} ∧ ¬ G.Adj x y ∧
      threeConn ((addEdge G x y).induce {v : V | v ≠ z}) ∧
      ∀ v : {v : V | v ≠ z},
        k ≤ (((addEdge G x y).induce {v : V | v ≠ z}).neighborSet v).ncard

/-- Residue zero in the weak-graph branch at modulus five. -/
def H1 : Prop :=
  ∀ {V : Type} [Fintype V] (G : SimpleGraph V) (z : V),
    4 ≤ Fintype.card V → weakGraph 5 G z →
    (∀ v, v ≠ z → 5 ≤ (G.neighborSet v).ncard) →
    (completeGraph (Fin 5)).Free G → (completeBipartiteGraph (Fin 5) (Fin 5)).Free G →
    HasCycle G 5

/-- Rooted admissible paths with one exceptional internal vertex.
The progression starts at a path length of at least two. -/
def H2 : Prop :=
  ∀ {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (x y z : V),
    5 ≤ k → 4 ≤ Fintype.card V → x ≠ y → twoConn (addEdge G x y) →
    (∀ v, v ≠ x → v ≠ y → v ≠ z → k ≤ (G.neighborSet v).ncard) →
    ∃ a s : ℕ, 2 ≤ a ∧ (s = 1 ∨ s = 2) ∧
      ∀ i < k - 1, PathOfLength G x y (a + s * i)

/-- Residue zero in the weak-graph branch. Any two-vertex cut consists of the two
nonadjacent neighbors of the possible deficient vertex. The exceptional families have
already been excluded by the clique and biclique conditions. -/
def H3 : Prop :=
  ∀ {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (z : V),
    6 ≤ k → 4 ≤ Fintype.card V → weakGraph k G z →
    (∀ v, v ≠ z → k ≤ (G.neighborSet v).ncard) →
    (completeGraph (Fin k)).Free G → (completeBipartiteGraph (Fin k) (Fin k)).Free G →
    HasCycle G k


section

private lemma walk_parity {V : Type} {G : SimpleGraph V} (c : G.Coloring (Fin 2))
    {u v : V} (p : G.Walk u v) : p.length % 2 = if c u = c v then 0 else 1 := by
  have toggle : ∀ a b d : Fin 2, a ≠ b →
      (((if b = d then 0 else 1) + 1) % 2 : ℕ) = (if a = d then 0 else 1) := by decide
  induction p with
  | nil => simp
  | @cons x y z h p ih =>
    rw [Walk.length_cons, Nat.add_mod, ih]
    exact toggle (c x) (c y) (c z) (c.valid h)

private lemma solve_bipartite_core {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (k : ℕ) (B : Finset V) (h₂ : H2)
    (hk : 5 ≤ k) (hek : Even k) (hc : 4 ≤ Fintype.card V) (hg : twoConn G)
    (hb : G.IsBipartite) (hB : B.card ≤ 2)
    (hd : ∀ v ∉ B, k ≤ (G.neighborSet v).ncard) : HasCycle G k := by
  classical
  obtain ⟨w⟩ := hg.1.nonempty
  have hchoose : ∃ x z : V, ∀ v ∈ B, v = x ∨ v = z := by
    by_cases hn : B.Nonempty
    · obtain ⟨x, hx⟩ := hn
      have hB' : (B.erase x).card ≤ 1 := by rw [Finset.card_erase_of_mem hx]; omega
      let _ : Nonempty V := ⟨w⟩
      obtain ⟨z, hz⟩ := Finset.card_le_one_iff_subset_singleton.mp hB'
      exact ⟨x, z, fun v hv => or_iff_not_imp_left.mpr fun hvx =>
        Finset.mem_singleton.mp (hz (Finset.mem_erase.mpr ⟨hvx, hv⟩))⟩
    · exact ⟨w, w, fun v hv => (hn ⟨v, hv⟩).elim⟩
  obtain ⟨x, z, hxz⟩ := hchoose
  let _ : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨y, hxy⟩ := hg.1.preconnected.exists_adj_of_nontrivial x
  have haug : addEdge G x y = G := by
    ext a b
    change (G.Adj a b ∨ (x ≠ y ∧ ((a = x ∧ b = y) ∨ (a = y ∧ b = x)))) ↔ G.Adj a b
    refine ⟨?_, Or.inl⟩
    rintro (h | ⟨_, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩)
    · exact h
    · exact hxy
    · exact hxy.symm
  obtain ⟨a, s, ha, hs, hf⟩ := h₂ G k x y z hk hc hxy.ne (by rwa [haug])
    (fun v hvx _ hvz => hd v (fun hh => (hxz v hh).elim hvx hvz))
  obtain ⟨c⟩ := hb
  have hodd {n : ℕ} (hn : PathOfLength G x y n) : n % 2 = 1 := by
    obtain ⟨p, _, rfl⟩ := hn
    simpa [c.valid hxy] using walk_parity c p
  have hao : a % 2 = 1 := hodd (by simpa using hf 0 (by omega))
  have hs2 : s = 2 := hs.resolve_left fun h => by
    have h1 := hodd (hf 1 (by omega))
    rw [h, Nat.mul_one] at h1
    omega
  subst s
  have hev : Even (a + 1) := by
    rw [Nat.even_iff]
    omega
  obtain ⟨i, hi, hdi⟩ := even_modulus_step k (a + 1) hk hek hev
  obtain ⟨p, hp, hpl⟩ := hf i hi
  refine ⟨x, p.append hxy.toWalk.reverse, ?_, ?_⟩
  · apply combine hp hxy.isPath_toWalk (Or.inl (by omega))
    intro v _ hv
    simpa [hxy.support_toWalk] using hv
  · simpa [Walk.length_append, Walk.length_reverse, hpl, Nat.add_assoc, Nat.add_left_comm,
      Nat.add_comm] using hdi


private lemma bipartite_side {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    {x y : V} {M : Set V} {k : ℕ}
    (h₂ : H2) (hk : 5 ≤ k) (hke : Even k)
    (hclosed : ∀ ⦃a b⦄, a ∈ M → b ≠ x → b ≠ y → G.Adj a b → b ∈ M)
    (hdeg : ∀ v ∈ M, k ≤ (G.neighborSet v).ncard)
    (hne : ∃ v ∈ M, v ≠ x ∧ v ≠ y)
    (hbi : (G.induce (side x y M)).IsBipartite) : HasCycle G k := by
  classical
  let S := side x y M
  let J := G.induce S
  let R : S := ⟨x, Or.inl rfl⟩
  let T : S := ⟨y, Or.inr (Or.inl rfl)⟩
  let B : Finset S := {R, T}
  have hsub (v : S) (hv : v ∉ B) : G.neighborSet v.val ⊆ S := by
    intro w hw
    by_cases hx : w = x
    · exact Or.inl hx
    by_cases hy : w = y
    · exact Or.inr (Or.inl hy)
    have Hv : v.val ∈ M := by
      rcases v.property with h | h | h
      · exact (hv (Finset.mem_insert.mpr (Or.inl (Subtype.ext h)))).elim
      · exact (hv (Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr (Subtype.ext h))))).elim
      · exact h
    exact Or.inr (Or.inr (hclosed Hv hx hy hw))
  have hd : ∀ v ∉ B, k ≤ (J.neighborSet v).ncard := by
    intro v hv
    rw [ncard_induce v (hsub v hv)]
    rcases v.property with h | h | h
    · exact (hv (Finset.mem_insert.mpr (Or.inl (Subtype.ext h)))).elim
    · exact (hv (Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr (Subtype.ext h))))).elim
    · exact hdeg _ h
  obtain ⟨a, ha, hax, hay⟩ := hne
  have hgood : ∃ v : S, v ∉ B := by
    refine ⟨⟨a, Or.inr (Or.inr ha)⟩, ?_⟩
    simp only [B, Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨fun h => hax (congrArg Subtype.val h), fun h => hay (congrArg Subtype.val h)⟩
  have hB : B.card ≤ 2 := (Finset.card_insert_le _ _).trans (by simp)
  obtain ⟨F, hF, hFb, v, hv, hvb⟩ :=
    exists_twoConn_core J B k 2 (by decide) (by omega) hB hd hgood
  have hlarge := card_le_of_good hd hv hvb
  let K := J.induce (F : Set S)
  let f : K ↪g J := Embedding.induce _
  let bad := (boundary J B F).subtype (· ∈ (F : Set S))
  have hcard : 4 ≤ Fintype.card (F : Set S) := by
    rw [Set.fintypeCard_eq_ncard, Set.ncard_coe_finset]
    omega
  have hbad : bad.card ≤ 2 := by rwa [bad_subtype_card]
  have hbound (w : (F : Set S)) (hw : w ∉ bad) :
      k ≤ (K.neighborSet w).ncard :=
    good_in_induced hd w (fun h => hw (Finset.mem_subtype.mpr h))
  have hK := solve_bipartite_core K k bad h₂ hk hke hcard hF (hbi.of_hom f.toHom) hbad hbound
  exact cycle_lift (Embedding.induce _) (cycle_lift f hK)

private lemma side_progression {V : Type} [Fintype V] {G : SimpleGraph V}
    {x y : V} (hxy : x ≠ y) (w : cutOutside x y) (hw : (inComponent G w).Nontrivial)
    {k : ℕ} (hk : 5 ≤ k) (z : V)
    (hG : twoConn G) (hd : ∀ v, v ≠ z → k ≤ (G.neighborSet v).ncard) (h₂ : H2) :
    let S := side x y (inComponent G w)
    let R : S := ⟨x, Or.inl rfl⟩
    let T : S := ⟨y, Or.inr (Or.inl rfl)⟩
    ∃ a s : ℕ, 2 ≤ a ∧ (s = 1 ∨ s = 2) ∧
      ∀ i < k - 1, PathOfLength (G.induce S) R T (a + s * i) := by
  classical
  dsimp only
  let M := inComponent G w
  let S := side x y M
  let R : S := ⟨x, Or.inl rfl⟩
  let T : S := ⟨y, Or.inr (Or.inl rfl)⟩
  let Z : S := if hz : z ∈ S then ⟨z, hz⟩ else R
  have hst : R ≠ T := fun h => hxy (congrArg Subtype.val h)
  have hcl (a b : V) (ha : a ∈ M) (hx : b ≠ x) (hy : b ≠ y) (hab : G.Adj a b) :
      b ∈ M := comp_closed ha ⟨hx, hy⟩ hab
  have hcard : 4 ≤ Fintype.card S := by
    rw [Set.fintypeCard_eq_ncard]
    exact four_side hxy hw
  have htwo := sideTwoConn hxy hG (M := M) (fun {a b} => hcl a b)
  apply h₂ (G.induce S) k R T Z hk hcard hst htwo
  intro a ha hb hz
  have habs : a.val ≠ x ∧ a.val ≠ y :=
    ⟨fun h => ha (Subtype.ext h), fun h => hb (Subtype.ext h)⟩
  have haz : a.val ≠ z := by
    intro h
    have hzS : z ∈ S := h ▸ a.property
    apply hz
    rw [show Z = ⟨z, hzS⟩ by simp [Z, hzS]]
    exact Subtype.ext h
  have hm : a.val ∈ M := a.property.resolve_left habs.1 |>.resolve_left habs.2
  have hsub : G.neighborSet a.val ⊆ S := by
    intro b hab
    by_cases hx : b = x
    · exact Or.inl hx
    by_cases hy : b = y
    · exact Or.inr (Or.inl hy)
    exact Or.inr (Or.inr (hcl a.val b hm hx hy hab))
  rw [ncard_induce a hsub]
  exact hd _ haz


private lemma reach_avoiding {V : Type} [DecidableEq V] {G : SimpleGraph V} {r u v : V}
    (hu : u ≠ r) (hv : v ≠ r)
    (hc : (G.induce {w : V | w ≠ r}).Connected) :
    DeanLink.ReachAvoiding G {r} u v := by
  let S := {w : V | w ≠ r}
  obtain ⟨p⟩ := hc.preconnected ⟨u, hu⟩ ⟨v, hv⟩
  let f : G.induce S ↪g G := Embedding.induce S
  exact ⟨p.map f.toHom, fun w hw hm =>
    supported_map p w hw (Finset.mem_singleton.mp hm)⟩

private lemma restrict_augmented_path {V : Type} {G : SimpleGraph V} {x y a b : V}
    (p : (addEdge G x y).Walk a b) (hp : p.IsPath)
    (hmiss : x ∉ p.support ∨ y ∉ p.support) :
    ∃ q : G.Walk a b, q.IsPath ∧ q.support = p.support := by
  have h : ∀ e ∈ p.edges, e ∈ G.edgeSet := by
    intro e he
    obtain ⟨u, v, rfl⟩ := Sym2.mk_surjective e
    rcases p.adj_of_mem_edges he with hh | ⟨_, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
    · exact hh
    · exact (hmiss.elim (fun hx => hx (p.fst_mem_support_of_mem_edges he))
        (fun hy => hy (p.snd_mem_support_of_mem_edges he))).elim
    · exact (hmiss.elim (fun hx => hx (p.snd_mem_support_of_mem_edges he))
        (fun hy => hy (p.fst_mem_support_of_mem_edges he))).elim
  exact ⟨p.transfer G h, hp.transfer h, Walk.support_transfer _ _⟩

private lemma root_attach {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    {x y : V} (hxy : x ≠ y) (hG : twoConn (addEdge G x y))
    (C : Finset V) (hC : 2 ≤ C.card) :
    ∃ (a b : V) (p : G.Walk x a) (q : G.Walk y b),
      a ∈ C ∧ b ∈ C ∧ a ≠ b ∧ p.IsPath ∧ q.IsPath ∧ p.support.Disjoint q.support ∧
      (∀ w ∈ p.support, w ∈ C → w = a) ∧ (∀ w ∈ q.support, w ∈ C → w = b) := by
  classical
  let J := addEdge G x y
  have single (r s : V) (hrs : r ≠ s) (hr : r ∈ C) (hs : s ∉ C)
      (hroot : r = x ∨ r = y) :
      ∃ (b : V) (q : G.Walk s b),
        b ∈ C ∧ b ≠ r ∧ q.IsPath ∧ r ∉ q.support ∧
        (∀ w ∈ q.support, w ∈ C → w = b) := by
    have hpos : 0 < (C.erase r).card := by rw [Finset.card_erase_of_mem hr]; omega
    obtain ⟨b, hb⟩ := Finset.card_pos.mp hpos
    have hbr := (Finset.mem_erase.mp hb).1
    have hAB : Disjoint ({s} : Finset V) (C.erase r) := by
      simp [Finset.disjoint_left, hs]
    have hAS : Disjoint ({s} : Finset V) {r} := by simpa using hrs.symm
    have hBS : Disjoint (C.erase r) ({r} : Finset V) :=
      Finset.disjoint_left.mpr (fun v hv hw =>
        (Finset.mem_erase.mp hv).1 (Finset.mem_singleton.mp hw))
    obtain ⟨t, u, p, ht, hu, hp, _, havoids, hint⟩ :=
      DeanLink.exists_minimal_path_between J hAB hAS hBS
        ⟨s, by simp, b, hb, reach_avoiding hrs.symm hbr (hG.2 r)⟩
    have hts : t = s := Finset.mem_singleton.mp ht
    subst t
    have hmiss : r ∉ p.support := fun h => havoids r h (by simp)
    have hmiss' : x ∉ p.support ∨ y ∉ p.support := hroot.elim
      (fun h => Or.inl (h ▸ hmiss)) (fun h => Or.inr (h ▸ hmiss))
    obtain ⟨q, hq, heq⟩ := restrict_augmented_path p hp hmiss'
    refine ⟨u, q, (Finset.mem_erase.mp hu).2, (Finset.mem_erase.mp hu).1,
      hq, heq ▸ hmiss, ?_⟩
    intro w hw hwC
    by_contra hwu
    rw [heq] at hw
    have hws : w ≠ s := fun h => hs (h ▸ hwC)
    exact (hint w hw hws hwu).2 (Finset.mem_erase.mpr
      ⟨fun h => hmiss (h ▸ hw), hwC⟩)
  by_cases hx : x ∈ C <;> by_cases hy : y ∈ C
  · exact ⟨x, y, .nil, .nil, hx, hy, hxy, .nil, .nil,
      by simpa [hxy.symm], by simp, by simp⟩
  · obtain ⟨b, q, hb, hbx, hq, hdis, ha⟩ := single x y hxy hx hy (Or.inl rfl)
    exact ⟨x, b, .nil, q, hx, hb, hbx.symm, .nil, hq, by simpa, by simp, ha⟩
  · obtain ⟨a, p, ha, hay, hp, hdis, hb⟩ := single y x hxy.symm hy hx (Or.inr rfl)
    exact ⟨a, y, p, .nil, ha, hy, hay, hp, .nil,
      (show ([y] : List V).Disjoint p.support by simpa).symm, hb, by simp⟩
  have hAB : Disjoint ({x, y} : Finset V) C := by
    rw [Finset.disjoint_left]
    intro v hv
    rcases (show v = x ∨ v = y by simpa using hv) with rfl | rfl
    · exact hx
    · exact hy
  have hsep (r : V) : ¬ DeanLink.IsSeparating J {r} := by
    rintro ⟨a, b, ha, hb, h⟩
    exact h (reach_avoiding (by simpa using ha) (by simpa using hb) (hG.2 r))
  obtain ⟨u, v, a, b, p, q, hu, hv, huv, ha, hb, hab, hp, hq, _, _, hdis, hintp, hintq⟩ :=
    DeanLink.two_disjoint_paths_of_no_cut_vertex J hG.1 hsep hAB (by simp [hxy]) hC
  have hpair : (u = x ∧ v = y) ∨ (u = y ∧ v = x) := by
    have hu' : u = x ∨ u = y := by simpa using hu
    have hv' : v = x ∨ v = y := by simpa using hv
    rcases hu' with h | h <;> rcases hv' with h' | h'
    · exact (huv (h.trans h'.symm)).elim
    · exact Or.inl ⟨h, h'⟩
    · exact Or.inr ⟨h, h'⟩
    · exact (huv (h.trans h'.symm)).elim
  have huv' : v ∉ p.support := fun h =>
    Finset.disjoint_left.mp hdis
      ((DeanLink.mem_walkVerts J).mpr h) ((DeanLink.mem_walkVerts J).mpr q.start_mem_support)
  have hvu' : u ∉ q.support := fun h =>
    Finset.disjoint_left.mp hdis
      ((DeanLink.mem_walkVerts J).mpr p.start_mem_support) ((DeanLink.mem_walkVerts J).mpr h)
  have hpMiss : x ∉ p.support ∨ y ∉ p.support := by
    rcases hpair with h | h
    · exact Or.inr (fun hm => huv' (by rwa [h.2]))
    · exact Or.inl (fun hm => huv' (by rwa [h.2]))
  have hqMiss : x ∉ q.support ∨ y ∉ q.support := by
    rcases hpair with h | h
    · exact Or.inl (fun hm => hvu' (by rwa [h.1]))
    · exact Or.inr (fun hm => hvu' (by rwa [h.1]))
  have hpathsP := restrict_augmented_path p hp hpMiss
  have hpathsQ := restrict_augmented_path q hq hqMiss
  obtain ⟨p', hp', hep⟩ := hpathsP
  obtain ⟨q', hq', heq⟩ := hpathsQ
  have hdis' : p'.support.Disjoint q'.support := by
    rw [hep, heq, List.disjoint_left]
    exact fun w hp hq => Finset.disjoint_left.mp hdis
      ((DeanLink.mem_walkVerts J).mpr hp) ((DeanLink.mem_walkVerts J).mpr hq)
  have hap (w : V) (hw : w ∈ p'.support) (hwC : w ∈ C) : w = a := by
    rw [hep] at hw
    by_contra h
    apply (hintp w hw (fun he => Finset.disjoint_left.mp hAB hu (he ▸ hwC)) h).2
    exact hwC
  have hbq (w : V) (hw : w ∈ q'.support) (hwC : w ∈ C) : w = b := by
    rw [heq] at hw
    by_contra h
    apply (hintq w hw (fun he => Finset.disjoint_left.mp hAB hv (he ▸ hwC)) h).2
    exact hwC
  rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨a, b, p', q', ha, hb, hab, hp', hq', hdis', hap, hbq⟩
  · exact ⟨b, a, q', p', hb, ha, hab.symm, hq', hp', hdis'.symm, hbq, hap⟩

private lemma root_parity {V : Type} [Fintype V] (G : SimpleGraph V) (x y : V)
    (hxy : x ≠ y) (hG : twoConn (addEdge G x y)) :
    G.IsBipartite ∨ ∃ e o : ℕ, Even e ∧ Odd o ∧
      PathOfLength G x y e ∧ PathOfLength G x y o := by
  classical
  by_cases hb : G.IsBipartite
  · exact Or.inl hb
  have ho : ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧ Odd c.length := by
    by_contra hn
    apply hb
    apply DeanOdd.colorable_two_of_cycle_even
    exact fun v c hc => Nat.not_odd_iff_even.mp (fun h => hn ⟨v, c, hc, h⟩)
  obtain ⟨v, c, hc, hoc⟩ := ho
  let C := c.support.toFinset
  have hC : 2 ≤ C.card := by
    have hlen := hc.three_le_length
    have hle : c.support.tail.toFinset.card ≤ C.card :=
      Finset.card_le_card (fun v hv => List.mem_toFinset.mpr
        (List.mem_of_mem_tail (List.mem_toFinset.mp hv)))
    rw [List.toFinset_card_of_nodup hc.support_nodup, List.length_tail, c.length_support] at hle
    omega
  obtain ⟨a, b, p, q, ha, hb, hab, hp, hq, hd, hap, hbq⟩ :=
    root_attach hxy hG C hC
  obtain ⟨r, s, hr, hs, _, _, hsum, hrc, hsc, _, _⟩ := DeanLink.split_cycle G hc ha hb hab
  have assemble (t : G.Walk a b) (ht : t.IsPath)
      (hsub : ∀ w ∈ t.support, w ∈ C) : (p.append (t.append q.reverse)).IsPath := by
    apply DeanLink.isPath_append_of_inter_eq G p _ hp
    · apply DeanLink.isPath_append_of_inter_eq G t q.reverse ht hq.reverse
      intro w hwt hwq
      exact hbq w (by simpa using hwq) (hsub w hwt)
    · intro w hwp hwt
      rcases (Walk.mem_support_append_iff t q.reverse).mp hwt with hw | hw
      · exact hap w hwp (hsub w hw)
      · exact (List.disjoint_left.mp hd hwp (by simpa using hw)).elim
  let P := p.append (r.append q.reverse)
  let Q := p.append (s.reverse.append q.reverse)
  have hP : P.IsPath := assemble r hr (fun w hw => hrc ((DeanLink.mem_walkVerts G).mpr hw))
  have hQ : Q.IsPath := assemble s.reverse hs.reverse (fun w hw => hsc ((DeanLink.mem_walkVerts G).mpr (by simpa using hw)))
  have hpar : Odd (P.length + Q.length) := by
    simp only [P, Q, Walk.length_append, Walk.length_reverse, Nat.odd_iff] at *
    omega
  rw [Nat.odd_iff] at hpar
  by_cases hE : Even P.length
  · exact Or.inr ⟨P.length, Q.length, hE, by rw [Nat.odd_iff]; rw [Nat.even_iff] at hE; omega,
      ⟨P, hP, rfl⟩, ⟨Q, hQ, rfl⟩⟩
  · have hO := Nat.not_even_iff_odd.mp hE
    exact Or.inr ⟨Q.length, P.length, by rw [Nat.even_iff]; rw [Nat.odd_iff] at hO; omega, hO,
      ⟨Q, hQ, rfl⟩, ⟨P, hP, rfl⟩⟩


private lemma solve_essential {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    {k : ℕ} (z : V) (hk : 5 ≤ k)
    (hG : twoConn G) (hd : ∀ v, v ≠ z → k ≤ (G.neighborSet v).ncard)
    (hc : EssentialCut G) (h₂ : H2) : HasCycle G k := by
  classical
  obtain ⟨x, y, hxy, u, v, huv, hU, hV⟩ := hc
  let D := cutOutside x y
  have side_family (w : D) (hw : (inComponent G w).Nontrivial) :
      let S := side x y (inComponent G w)
      let R : S := ⟨x, Or.inl rfl⟩
      let T : S := ⟨y, Or.inr (Or.inl rfl)⟩
      (∃ a s : ℕ, 2 ≤ a ∧ (s = 1 ∨ s = 2) ∧
        ∀ i < k - 1, PathOfLength (G.induce S) R T (a + s * i)) ∧
      ((G.induce S).IsBipartite ∨ ∃ e o : ℕ, Even e ∧ Odd o ∧
        PathOfLength (G.induce S) R T e ∧ PathOfLength (G.induce S) R T o) := by
    dsimp only
    have htwo := sideTwoConn hxy hG (M := inComponent G w)
      (fun {a b} hm hx hy ha => comp_closed (G := G) (r := w) hm ⟨hx, hy⟩ ha)
    exact ⟨side_progression hxy w hw hk z hG hd h₂,
      root_parity _ _ _ (fun he => hxy (congrArg Subtype.val he)) htwo⟩
  obtain ⟨⟨a, s, ha, hs, hf⟩, hp⟩ := side_family u hU
  obtain ⟨⟨b, t, hb, ht, hg⟩, hq⟩ := side_family v hV
  have hdisj := comp_disjoint huv
  rcases pair_step k (a + b) s t hk hs ht with ⟨i, hi, j, hj, hdvd⟩ | ⟨he, _, rfl, rfl⟩
  · exact glue_sides hdisj (Or.inl (by omega)) (hf i hi) (hg j hj)
      (by simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hdvd)
  have first (h : ¬ (G.induce (side x y (inComponent G u))).IsBipartite) : HasCycle G k := by
    obtain ⟨e, o, he', ho', hpe, hpo⟩ := hp.resolve_left h
    have hsel : ∃ l : ℕ, Even (l + b) ∧
        PathOfLength (G.induce (side x y (inComponent G u))) ⟨x, Or.inl rfl⟩
          ⟨y, Or.inr (Or.inl rfl)⟩ l := by
      by_cases hbe : Even b
      · exact ⟨e, he'.add hbe, hpe⟩
      · exact ⟨o, ho'.add_odd (Nat.not_even_iff_odd.mp hbe), hpo⟩
    obtain ⟨l, hl, hpath⟩ := hsel
    obtain ⟨i, hi, hdvd⟩ := even_modulus_step k (l + b) hk he hl
    exact glue_sides hdisj (Or.inr (by omega)) hpath (hg i hi) (by rwa [Nat.add_assoc] at hdvd)
  have second (h : ¬ (G.induce (side x y (inComponent G v))).IsBipartite) : HasCycle G k := by
    obtain ⟨e, o, he', ho', hpe, hpo⟩ := hq.resolve_left h
    have hsel : ∃ l : ℕ, Even (l + a) ∧
        PathOfLength (G.induce (side x y (inComponent G v))) ⟨x, Or.inl rfl⟩
          ⟨y, Or.inr (Or.inl rfl)⟩ l := by
      by_cases hae : Even a
      · exact ⟨e, he'.add hae, hpe⟩
      · exact ⟨o, ho'.add_odd (Nat.not_even_iff_odd.mp hae), hpo⟩
    obtain ⟨l, hl, hpath⟩ := hsel
    obtain ⟨i, hi, hdvd⟩ := even_modulus_step k (l + a) hk he hl
    exact glue_sides hdisj (Or.inl (by omega)) (hf i hi) hpath
      (by simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hdvd)
  by_cases hbu : (G.induce (side x y (inComponent G u))).IsBipartite
  · by_cases hbv : (G.induce (side x y (inComponent G v))).IsBipartite
    · have use (w : D) (hw : z ∉ inComponent G w)
          (hbi : (G.induce (side x y (inComponent G w))).IsBipartite) : HasCycle G k :=
        bipartite_side h₂ hk he (fun {a b} hm hx hy ha =>
          comp_closed (G := G) (r := w) hm ⟨hx, hy⟩ ha)
          (fun a ha => hd a (fun e => hw (e ▸ ha)))
          ⟨w.val, ⟨w.property, .rfl⟩, w.property⟩ hbi
      by_cases hz : z ∈ inComponent G u
      · exact use v (fun h => Set.disjoint_left.mp hdisj hz h) hbv
      · exact use u hz hbu
    · exact second hbv
  · exact first hbu




private lemma short_shift (k a s : ℕ) (hk : 5 ≤ k) (hs : s = 1 ∨ s = 2) :
    ∃ i < k - 1, ∃ d : ℕ, (d = 1 ∨ d = 2) ∧ k ∣ a + s * i + d := by
  let r := (k - (a + 1) % k) % k
  have hr : r < k := Nat.mod_lt _ (by omega)
  have hd : k ∣ (a + 1) + r := add_mod_complement _ _ (by omega)
  rcases hs with rfl | rfl
  · by_cases hh : r < k - 1
    · exact ⟨r, hh, 1, Or.inl rfl, by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hd⟩
    · refine ⟨r - 1, by omega, 2, Or.inr rfl, ?_⟩
      rw [show a + 1 * (r - 1) + 2 = (a + 1) + r by omega]
      exact hd
  · refine ⟨r / 2, by omega, 1 + r % 2, by omega, ?_⟩
    rw [show a + 2 * (r / 2) + (1 + r % 2) = (a + 1) + r by omega]
    exact hd

private lemma singleton_component {V : Type} {G : SimpleGraph V} {D : Set V} (a : D)
    (ha : ¬ (inComponent G a).Nontrivial) :
    inComponent G a = {a.val} := by
  ext v
  constructor
  · intro hv
    by_contra hn
    exact ha ⟨v, hv, a.val, ⟨a.property, .rfl⟩, hn⟩
  · intro hv
    rcases Set.mem_singleton_iff.mp hv with rfl
    exact ⟨a.property, .rfl⟩

private lemma no_neighbors_of_singleton {V : Type} {G : SimpleGraph V} {x y : V}
    (a : cutOutside x y) (ha : ¬ (inComponent G a).Nontrivial) :
    G.neighborSet a.val ⊆ {x, y} := by
  intro w hw
  by_contra h
  have hwxy : w ≠ x ∧ w ≠ y := by simpa using h
  have hcomp := comp_closed (G := G) (r := a) ⟨a.property, .rfl⟩ hwxy hw
  rw [singleton_component a ha] at hcomp
  exact G.ne_of_adj hw (Set.mem_singleton_iff.mp hcomp).symm

private lemma has_both_neighbors {V : Type} {G : SimpleGraph V} {x y z : V}
    (hxy : x ≠ y) (hzx : z ≠ x) (hzy : z ≠ y) (hG : twoConn G)
    (hsub : G.neighborSet z ⊆ {x, y}) :
    G.neighborSet z = {x, y} := by
  have attach (u v : V) (hzU : z ≠ u) (hzV : z ≠ v) (huv : u ≠ v)
      (hs : G.neighborSet z ⊆ {u, v}) : G.Adj z u := by
    by_contra h
    let D := {w : V | w ≠ v}
    let r : D := ⟨z, hzV⟩
    let s : D := ⟨u, huv⟩
    have hn : (G.induce D).neighborSet r = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro w hw
      have ha : G.Adj z w.val := hw
      rcases (show w.val = u ∨ w.val = v by simpa using hs ha) with he | he
      · exact h (he ▸ ha)
      · exact w.property he
    exact not_reachable_of_neighborSet_left_eq_empty (fun e => hzU (congrArg Subtype.val e)) hn
      ((hG.2 v).preconnected r s)
  have hₓ := attach x y hzx hzy hxy hsub
  have hᵧ := attach y x hzy hzx hxy.symm (by simpa [Set.pair_comm] using hsub)
  apply Set.Subset.antisymm hsub
  intro w hw
  rcases (show w = x ∨ w = y by simpa using hw) with rfl | rfl
  · exact hₓ
  · exact hᵧ

private lemma two_routes {V : Type} {G : SimpleGraph V} {x y z : V}
    (hxy : G.Adj x y) (hxz : G.Adj x z) (hzy : G.Adj z y) :
    ∀ d : ℕ, (d = 1 ∨ d = 2) → PathOfLength
      (G.induce (side x y ({z} : Set V))) ⟨x, Or.inl rfl⟩ ⟨y, Or.inr (Or.inl rfl)⟩ d := by
  let S := side x y ({z} : Set V)
  let x' : S := ⟨x, Or.inl rfl⟩
  let y' : S := ⟨y, Or.inr (Or.inl rfl)⟩
  let z' : S := ⟨z, Or.inr (Or.inr rfl)⟩
  have e : (G.induce S).Adj x' y' := hxy
  have f : (G.induce S).Adj x' z' := hxz
  have g : (G.induce S).Adj z' y' := hzy
  intro d hd
  rcases hd with rfl | rfl
  · exact ⟨e.toWalk, e.isPath_toWalk, rfl⟩
  refine ⟨g.toWalk.cons f, g.isPath_toWalk.cons ?_, rfl⟩
  simpa [g.support_toWalk] using And.intro f.ne e.ne

private lemma weak_cuts {V : Type} [Fintype V] {G : SimpleGraph V} {k : ℕ} (z : V)
    (hk : 5 ≤ k) (hcard : 4 ≤ Fintype.card V) (hG : twoConn G)
    (hd : ∀ v, v ≠ z → k ≤ (G.neighborSet v).ncard)
    (hno : ¬ EssentialCut G) (hcycle : ¬ HasCycle G k) (h₂ : H2) :
    ∀ x y : V, x ≠ y → ¬ (G.induce (cutOutside x y)).Connected →
      G.neighborSet z = {x, y} ∧ ¬ G.Adj x y := by
  classical
  intro x y hxy hcut
  let D := cutOutside x y
  have hD : D = ({x, y} : Set V)ᶜ := by
    ext v
    simp [D, cutOutside]
  have hDcard : D.ncard = Fintype.card V - 2 := by
    rw [hD, Set.ncard_compl, Set.ncard_pair hxy, Nat.card_eq_fintype_card]
  obtain ⟨r, hr⟩ := (Set.ncard_pos (s := D)).mp (show 0 < D.ncard by omega)
  let _ : Nonempty D := ⟨⟨r, hr⟩⟩
  have hnon : ∃ a b : D, ¬ (G.induce D).Reachable a b := by
    by_contra hn
    push Not at hn
    exact hcut (Connected.mk hn)
  obtain ⟨a, b, hab⟩ := hnon
  have hsing : ∃ u v : D, ¬ (G.induce D).Reachable u v ∧ ¬ (inComponent G u).Nontrivial := by
    by_cases ha : (inComponent G a).Nontrivial
    · refine ⟨b, a, fun h => hab h.symm, ?_⟩
      exact fun hb => hno ⟨x, y, hxy, a, b, hab, ha, hb⟩
    · exact ⟨a, b, hab, ha⟩
  obtain ⟨u, v, huv, hu⟩ := hsing
  have is_z (w : D) (hw : ¬ (inComponent G w).Nontrivial) : w.val = z := by
    by_contra hn
    have hle := (hd w.val hn).trans (Set.ncard_le_ncard (no_neighbors_of_singleton w hw))
    rw [Set.ncard_pair hxy] at hle
    omega
  have huz := is_z u hu
  have hsubset : G.neighborSet z ⊆ {x, y} := huz ▸ no_neighbors_of_singleton u hu
  have hzD : z ∈ D := huz ▸ u.property
  have hn := has_both_neighbors hxy hzD.1 hzD.2 hG hsubset
  refine ⟨hn, ?_⟩
  intro hxy'
  have hv : (inComponent G v).Nontrivial := by
    by_contra hnv
    have he := is_z v hnv
    exact huv ((Subtype.ext (huz.trans he.symm) : u = v) ▸ .rfl)
  obtain ⟨a, s, ha, hs, hpaths⟩ := side_progression hxy v hv hk z hG hd h₂
  obtain ⟨i, hi, d, h12, hdvd⟩ := short_shift k a s hk hs
  have hdisj : Disjoint (inComponent G v) ({z} : Set V) := by
    have h' := (comp_disjoint huv).symm
    rw [singleton_component u hu, huz] at h'
    exact h'
  have hxz : G.Adj x z := by
    apply Adj.symm
    change x ∈ G.neighborSet z
    rw [hn]
    simp
  have hzy : G.Adj z y := by
    change y ∈ G.neighborSet z
    rw [hn]
    simp
  exact hcycle (glue_sides hdisj (Or.inl (by omega)) (hpaths i hi)
    (two_routes hxy' hxz hzy d h12) hdvd)



private lemma different_neighbor_pair {V : Type} {x y a b : V} (hxy : x ≠ y)
    (he : ({x, y} : Set V) = {a, b}) : (a = x ∧ b = y) ∨ (a = y ∧ b = x) := by
  have hx : x = a ∨ x = b := by
    have h : x ∈ ({a, b} : Set V) := he ▸ Set.mem_insert _ _
    simpa using h
  have hy : y = a ∨ y = b := by
    have h : y ∈ ({a, b} : Set V) := he ▸ Set.mem_insert_of_mem _ (Set.mem_singleton _)
    simpa using h
  rcases hx with hx | hx <;> rcases hy with hy | hy
  · exact (hxy (hx.trans hy.symm)).elim
  · exact Or.inl ⟨hx.symm, hy.symm⟩
  · exact Or.inr ⟨hy.symm, hx.symm⟩
  · exact (hxy (hx.trans hy.symm)).elim

private lemma flat_conn {V : Type} {G : SimpleGraph V} {D S : Set V}
    (hc : (G.induce (D ∩ S)).Connected) :
    ((G.induce S).induce {w : S | w.val ∈ D}).Connected := by
  let f : G.induce (D ∩ S) →g (G.induce S).induce {w : S | w.val ∈ D} :=
    ⟨fun w => ⟨⟨w.val, w.property.2⟩, w.property.1⟩, fun h => h⟩
  exact hc.map f (by
    rintro ⟨⟨w, hwS⟩, hwD⟩
    exact ⟨⟨w, hwD, hwS⟩, rfl⟩)

private lemma connected_after_three_deletions {V : Type} [Fintype V] {G : SimpleGraph V}
    {x y z : V} {k : ℕ} (hk : 5 ≤ k) (hcard : 4 ≤ Fintype.card V)
    (hxy : x ≠ y) (hzx : z ≠ x) (hzy : z ≠ y)
    (hn : G.neighborSet z = {x, y})
    (hd : ∀ v, v ≠ z → k ≤ (G.neighborSet v).ncard) (hno : ¬ EssentialCut G) :
    (G.induce (cutOutside x y ∩ {v : V | v ≠ z})).Connected := by
  let D := cutOutside x y
  let W := D ∩ {v : V | v ≠ z}
  have hW : W = ({x, y, z} : Set V)ᶜ := by
    ext v
    simp [W, D, cutOutside, and_assoc]
  have hc : ({x, y, z} : Set V).ncard = 3 := by
    classical
    rw [Set.ncard_insert_of_notMem, Set.ncard_pair hzy.symm]
    simp [hxy, hzx.symm]
  have hWc : W.ncard = Fintype.card V - 3 := by
    rw [hW, Set.ncard_compl, hc, Nat.card_eq_fintype_card]
  obtain ⟨w, hw⟩ := (Set.ncard_pos (s := W)).mp (show 0 < W.ncard by omega)
  let a : D := ⟨w, hw.1⟩
  let zz : D := ⟨z, hzx, hzy⟩
  have hzero : (G.induce D).neighborSet zz = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro v hv
    have h : v.val ∈ G.neighborSet z := hv
    rw [hn] at h
    have hvrt : v.val = x ∨ v.val = y := by simpa using h
    exact hvrt.elim v.property.1 v.property.2
  have hnontriv (v : D) (hv : v.val ≠ z) : (inComponent G v).Nontrivial := by
    by_contra he
    have hle := (hd v.val hv).trans (Set.ncard_le_ncard (no_neighbors_of_singleton v he))
    rw [Set.ncard_pair hxy] at hle
    omega
  have heq : inComponent G a = W := by
    ext v
    constructor
    · intro hv
      obtain ⟨hvD, hreach⟩ := hv
      refine ⟨hvD, ?_⟩
      intro he
      have hh : (⟨v, hvD⟩ : D) = zz := Subtype.ext he
      rw [hh] at hreach
      exact not_reachable_of_neighborSet_right_eq_empty
        (fun e => hw.2 (congrArg Subtype.val e)) hzero hreach
    · intro hv
      have hwz : a.val ≠ z := hw.2
      have hvz : (⟨v, hv.1⟩ : D).val ≠ z := hv.2
      refine ⟨hv.1, ?_⟩
      by_contra he
      exact hno ⟨x, y, hxy, a, ⟨v, hv.1⟩, he, hnontriv a hwz, hnontriv _ hvz⟩
  rw [← show inComponent G a = (cutOutside x y ∩ {v : V | v ≠ z}) from heq]
  exact comp_conn a

private lemma smooth_connected {V : Type} {G : SimpleGraph V}
    {x y z : V} (hxy : x ≠ y) (hzx : z ≠ x) (hzy : z ≠ y)
    (hn : G.neighborSet z = {x, y}) {D : Set V}
    (hc : (G.induce D).Connected) (hr : x ∈ D ∨ y ∈ D) :
    ((addEdge G x y).induce (D ∩ {v : V | v ≠ z})).Connected := by
  let M := {v : V | v ≠ z ∧ v ≠ x ∧ v ≠ y}
  have hS : side x y M = {v : V | v ≠ z} := by
    ext v
    constructor
    · rintro (rfl | rfl | hv)
      · exact hzx.symm
      · exact hzy.symm
      · exact hv.1
    · intro hv
      by_cases hx : v = x
      · exact Or.inl hx
      by_cases hy : v = y
      · exact Or.inr (Or.inl hy)
      exact Or.inr (Or.inr ⟨hv, hx, hy⟩)
  have hcl : ∀ ⦃a b⦄, a ∈ M → b ≠ x → b ≠ y → G.Adj a b → b ∈ M := by
    intro a b ha hbx hby hab
    refine ⟨?_, hbx, hby⟩
    intro hbz
    have h : a ∈ G.neighborSet z := hbz ▸ hab.symm
    rw [hn] at h
    exact (show a = x ∨ a = y by simpa using h).elim ha.2.1 ha.2.2
  rw [← hS]
  rcases hr with hx | hy
  · exact sideConnected hxy hcl hc (Or.inl rfl) hx
  · exact sideConnected hxy hcl hc (Or.inr rfl) hy

private lemma smooth_degree {V : Type} [Fintype V] {G : SimpleGraph V}
    {x y z : V} (hxy : x ≠ y) (hzx : z ≠ x) (hzy : z ≠ y)
    (hn : G.neighborSet z = {x, y}) (hno : ¬ G.Adj x y)
    (u : {v : V | v ≠ z}) :
    (G.neighborSet u.val).ncard ≤
      (((addEdge G x y).induce {v : V | v ≠ z}).neighborSet u).ncard := by
  classical
  let S := {v : V | v ≠ z}
  let J := (addEdge G x y).induce S
  change _ ≤ (J.neighborSet u).ncard
  rw [← Set.fintypeCard_eq_ncard, ← Set.fintypeCard_eq_ncard]
  have transfer {r : V} (hr : r ≠ z) (hnew : (addEdge G x y).Adj u.val r)
      (hOld : ¬ G.Adj u.val r) :
      Fintype.card (G.neighborSet u.val) ≤ Fintype.card (J.neighborSet u) := by
    let f (w : G.neighborSet u.val) : J.neighborSet u :=
      if h : w.val = z then ⟨⟨r, hr⟩, hnew⟩ else ⟨⟨w.val, h⟩, Or.inl w.property⟩
    apply Fintype.card_le_of_injective f
    intro a b hab
    have eq := congrArg (fun v : J.neighborSet u => v.val.val) hab
    by_cases ha : a.val = z <;> by_cases hb : b.val = z
    · exact Subtype.ext (ha.trans hb.symm)
    · have he : r = b.val := by simpa [f, ha, hb] using eq
      exact (hOld (he ▸ b.property)).elim
    · have he : a.val = r := by simpa [f, ha, hb] using eq
      exact (hOld (he ▸ a.property)).elim
    · exact Subtype.ext (by simpa [f, ha, hb] using eq)
  by_cases hux : u.val = x
  · exact transfer hzy.symm (Or.inr ⟨hxy, Or.inl ⟨hux, rfl⟩⟩)
      (fun he => hno (hux ▸ he))
  by_cases huy : u.val = y
  · exact transfer hzx.symm (Or.inr ⟨hxy, Or.inr ⟨huy, rfl⟩⟩)
      (fun he => hno (huy ▸ he).symm)
  have hp (w : G.neighborSet u.val) : w.val ≠ z := by
    intro he
    have hh : G.Adj w.val u.val := (show G.Adj u.val w.val from w.property).symm
    rw [he] at hh
    have hz : u.val ∈ G.neighborSet z := hh
    rw [hn] at hz
    exact (show u.val = x ∨ u.val = y by simpa using hz).elim hux huy
  let f (w : G.neighborSet u.val) : J.neighborSet u := ⟨⟨w.val, hp w⟩, Or.inl w.property⟩
  exact Fintype.card_le_of_injective f
    (fun a b e => Subtype.ext (congrArg (fun v : J.neighborSet u => v.val.val) e))

private lemma smooth_threeConn {V : Type} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    {x y z : V} (hk : 5 ≤ k) (hcard : 4 ≤ Fintype.card V)
    (hxy : x ≠ y) (hzx : z ≠ x) (hzy : z ≠ y)
    (hn : G.neighborSet z = {x, y}) (hG : twoConn G) (hno : ¬ EssentialCut G)
    (hd : ∀ v, v ≠ z → k ≤ (G.neighborSet v).ncard)
    (hshape : ∀ a b : V, a ≠ b → ¬ (G.induce (cutOutside a b)).Connected →
      G.neighborSet z = {a, b} ∧ ¬ G.Adj a b) :
    threeConn ((addEdge G x y).induce {v : V | v ≠ z}) := by
  let S := {v : V | v ≠ z}
  let H := addEdge G x y
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · let f : G →g G.induce Set.univ := ⟨fun v => ⟨v, Set.mem_univ _⟩, fun h => h⟩
    have hconn := hG.1.map f (fun v => ⟨v.val, Subtype.ext rfl⟩)
    have hc := smooth_connected hxy hzx hzy hn hconn (Or.inl (Set.mem_univ x))
    rwa [Set.univ_inter] at hc
  · intro a
    have hstay : x ∈ {v : V | v ≠ a.val} ∨ y ∈ {v : V | v ≠ a.val} := by
      by_cases h : x = a.val
      · exact Or.inr (fun h' => hxy (h.trans h'.symm))
      · exact Or.inl h
    have hc := flat_conn
      (smooth_connected hxy hzx hzy hn (hG.2 a.val) hstay)
    apply Connected.map (G := (H.induce S).induce {w : S | w.val ≠ a.val}) ?_ ?_ hc
    · exact ⟨fun w => ⟨w.val, fun e => w.property (congrArg Subtype.val e)⟩, fun h => h⟩
    · rintro ⟨w, hw⟩
      exact ⟨⟨w, fun e => hw (Subtype.ext e)⟩, rfl⟩
  · intro a b hab
    have hne : a.val ≠ b.val := fun h => hab (Subtype.ext h)
    let D := cutOutside a.val b.val
    have hpre : (H.induce (D ∩ S)).Connected := by
      by_cases hroots : D = cutOutside x y
      · rw [hroots]
        exact (connected_after_three_deletions hk hcard hxy hzx hzy hn hd hno).mono
          (fun _ _ h => Or.inl h)
      have hnopair : ¬ ((a.val = x ∧ b.val = y) ∨ (a.val = y ∧ b.val = x)) := by
        rintro (⟨ha, hb⟩ | ⟨ha, hb⟩)
        · exact hroots (by simp [D, ha, hb])
        · exact hroots (by simp [D, ha, hb, cutOutside, and_comm])
      have hstay : x ∈ D ∨ y ∈ D := by
        by_contra he
        push Not at he
        have hx : a.val = x ∨ b.val = x := by
          by_cases ha : x = a.val
          · exact Or.inl ha.symm
          by_cases hb : x = b.val
          · exact Or.inr hb.symm
          exact (he.1 ⟨ha, hb⟩).elim
        have hy : a.val = y ∨ b.val = y := by
          by_cases ha : y = a.val
          · exact Or.inl ha.symm
          by_cases hb : y = b.val
          · exact Or.inr hb.symm
          exact (he.2 ⟨ha, hb⟩).elim
        rcases hx with hx | hx <;> rcases hy with hy | hy
        · exact hxy (hx.symm.trans hy)
        · exact hnopair (Or.inl ⟨hx, hy⟩)
        · exact hnopair (Or.inr ⟨hy, hx⟩)
        · exact hxy (hx.symm.trans hy)
      have hconn : (G.induce D).Connected := by
        by_contra h
        exact hnopair (different_neighbor_pair hxy (hn.symm.trans (hshape _ _ hne h).1))
      exact smooth_connected hxy hzx hzy hn hconn hstay
    have heq : {v : S | v.val ∈ D} = cutOutside a b := by
      ext v
      change (v.val ≠ a.val ∧ v.val ≠ b.val) ↔ (v ≠ a ∧ v ≠ b)
      rw [← Subtype.coe_ne_coe, ← Subtype.coe_ne_coe]
    rw [← heq]
    exact flat_conn hpre

private lemma weak_type {V : Type} [Fintype V] {G : SimpleGraph V} {k : ℕ} (z : V)
    (hk : 5 ≤ k) (hcard : 4 ≤ Fintype.card V) (hG : twoConn G)
    (hd : ∀ v, v ≠ z → k ≤ (G.neighborSet v).ncard)
    (hno : ¬ EssentialCut G) (hcycle : ¬ HasCycle G k) (h₂ : H2) :
    weakGraph k G z := by
  classical
  by_cases hcuts : ∀ x y : V, x ≠ y → (G.induce (cutOutside x y)).Connected
  · exact Or.inl ⟨hG, hcuts⟩
  push Not at hcuts
  obtain ⟨x, y, hxy, hcut⟩ := hcuts
  have hshape := weak_cuts z hk hcard hG hd hno hcycle h₂
  obtain ⟨hn, hnot⟩ := hshape x y hxy hcut
  have hzx : z ≠ x := by
    intro he
    have hx : x ∈ G.neighborSet z := hn.symm ▸ Set.mem_insert _ _
    exact G.irrefl (he ▸ hx)
  have hzy : z ≠ y := by
    intro he
    have hy : y ∈ G.neighborSet z := hn.symm ▸ Set.mem_insert_of_mem _ (Set.mem_singleton _)
    exact G.irrefl (he ▸ hy)
  refine Or.inr ⟨x, y, hxy, hn, hnot, smooth_threeConn hk hcard hxy hzx hzy hn hG hno hd hshape, ?_⟩
  intro v
  exact (hd v.val v.property).trans (smooth_degree hxy hzx hzy hn hnot v)


private lemma solve_large {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {k : ℕ} (hk : 5 ≤ k) (hdeg : k ≤ G.minDegree)
    (h₁ : H1) (h₂ : H2) (h₃ : H3) : HasCycle G k := by
  classical
  have hne : Nonempty V := by
    cases isEmpty_or_nonempty V
    · simp at hdeg
      omega
    · assumption
  obtain ⟨v⟩ := hne
  have hd : ∀ w ∉ (∅ : Finset V), k ≤ (G.neighborSet w).ncard := by
    intro w _
    rw [← Set.fintypeCard_eq_ncard, card_neighborSet_eq_degree]
    exact hdeg.trans (G.minDegree_le_degree w)
  obtain ⟨S, hS, hSb, w, hw, hwb⟩ :=
    exists_twoConn_core G ∅ k 1 (by decide) (by omega) (by simp) hd ⟨v, by simp⟩
  have hlarge := card_le_of_good hd hw hwb
  let J := G.induce (S : Set V)
  let bad := (boundary G ∅ S).subtype (· ∈ (S : Set V))
  have hbad : bad.card ≤ 1 := by rwa [bad_subtype_card]
  let z : ↥(S : Set V) := if h : bad.Nonempty then h.choose else ⟨w, hw⟩
  have hbound : ∀ a, a ≠ z → k ≤ (J.neighborSet a).ncard := by
    intro a ha
    apply good_in_induced hd a
    intro ham
    have hab := Finset.mem_subtype.mpr ham
    have hne' : bad.Nonempty := ⟨a, hab⟩
    apply ha
    rw [show z = hne'.choose by simp [z, hne']]
    exact Finset.card_le_one.mp hbad _ hab _ hne'.choose_spec
  have hcard : 4 ≤ Fintype.card (S : Set V) := by
    rw [Set.fintypeCard_eq_ncard, Set.ncard_coe_finset]
    omega
  apply cycle_lift (Embedding.induce (G := G) (S : Set V))
  by_cases hc : EssentialCut J
  · exact solve_essential J z hk hS hbound hc h₂
  · by_cases hcl : completeGraph (Fin k) ⊑ J
    · exact cycle_of_clique (by omega) hcl
    by_cases hbi : completeBipartiteGraph (Fin k) (Fin k) ⊑ J
    · exact cycle_of_biclique (by omega) hbi
    by_contra hh
    have hshape := weak_type z hk hcard hS hbound hc hh h₂
    by_cases hk5 : k = 5
    · subst k
      exact hh (h₁ J z hcard hshape hbound hcl hbi)
    · exact hh (h₃ J k z (by omega) hcard hshape hbound hcl hbi)

private lemma lengths_of_cycle {V : Type} {G : SimpleGraph V} {k : ℕ} (h : HasCycle G k) :
    ∃ m ∈ G.cycleLengths, k ∣ m := by
  obtain ⟨v, p, hp, hd⟩ := h
  exact ⟨p.length, ⟨v, p, hp, rfl⟩, hd⟩


end

/-- Reduction of the exact Dean conjecture to the three remaining lemmas. -/
theorem main : H1 → H2 → H3 → type_of% @Arxiv.«2605.02731».dean_conjecture := by
  intro h₁ h₂ h₃ k hk V _ _ G _ hd
  by_cases hk3 : k = 3
  · subst k
    exact deanThree G hd
  by_cases hk4 : k = 4
  · subst k
    exact deanFour G hd
  exact lengths_of_cycle (solve_large G (by omega) hd h₁ h₂ h₃)

end OMA.R_Arxiv_2605_02731_dean_conjecture_R1
