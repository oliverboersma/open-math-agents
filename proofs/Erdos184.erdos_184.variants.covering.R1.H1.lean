import OMAReductions.R_Erdos184_erdos_184_variants_covering_R1
import Mathlib

-- Step Erdos184.erdos_184.variants.covering.R1.H1: hypothesis H1 of reduction Erdos184.erdos_184.variants.covering.R1
-- Credit: @ivillar

/-!
# Contraction step for Pyber's covering theorem

Let `v w` be adjacent vertices of `G` with at most one common neighbour, and let `G'` be `G` with
the edge `vw` contracted into `v` (the vertex `w` stays, isolated). A cover of `G'` by cycles and
edges lifts to a cover of `G` with one more piece:

* a cycle of `G'` avoiding `v` is a cycle of `G`;
* a cycle of `G'` through `v`, say `v x ... y v`, lifts to `t y ... x t'` closed up through the
  edge `vw` when `t ≠ t'`, where `t, t' ∈ {v, w}` are the ends attached to `y` and `x` in `G`
  (`w` whenever possible);
* an edge of `G'` lifts to an edge of `G` in the same way;
* one more piece, the triangle on `v`, `w` and the common neighbour, or the edge `vw`, covers the
  edge `vw` and the edge from `v` to the common neighbour;
* `G'` has one more connected component than `G`, which pays for the extra piece.
-/

open SimpleGraph

namespace Erdos184CoveringStep

variable {V : Type}

lemma not_mem_support_of_isolated {G : SimpleGraph V} {w : V}
    (hw : ∀ a b, G.Adj a b → a ≠ w) :
    ∀ {a b : V} (r : G.Walk a b), b ≠ w → w ∉ r.support := by
  intro a b r
  induction r with
  | nil =>
    intro hb
    rw [Walk.support_nil, List.mem_singleton]
    exact fun h => hb h.symm
  | cons h r ih =>
    intro hb
    rw [Walk.support_cons, List.mem_cons, not_or]
    exact ⟨fun e => hw _ _ h e.symm, ih hb⟩

lemma close_path [DecidableEq V] (G : SimpleGraph V) {a b y x : V}
    (r : G.Walk y x) (hr : r.IsPath) (hxy : x ≠ y)
    (ha : a ∉ r.support) (hb : b ∉ r.support)
    (hay : G.Adj a y) (hxb : G.Adj x b) (hab : a = b ∨ G.Adj b a) :
    ∃ c : G.Walk a a, c.IsCycle ∧ s(a, y) ∈ c.edges ∧ s(x, b) ∈ c.edges ∧
      ∀ e ∈ r.edges, e ∈ c.edges := by
  have hyb : y ≠ b := fun h => hb (h ▸ r.start_mem_support)
  rcases hab with rfl | hba
  · refine ⟨Walk.cons hay (r.concat hxb), ?_, ?_, ?_, ?_⟩
    · rw [Walk.cons_isCycle_iff]
      refine ⟨hr.concat ha hxb, ?_⟩
      rw [Walk.edges_concat, List.concat_eq_append, List.mem_append, List.mem_singleton, not_or]
      refine ⟨fun h => ha (Walk.fst_mem_support_of_mem_edges r h), fun h => ?_⟩
      rcases Sym2.eq_iff.mp h with ⟨-, h2⟩ | ⟨-, h2⟩
      · exact hyb h2
      · exact hxy h2.symm
    · rw [Walk.edges_cons]
      exact List.mem_cons.mpr (Or.inl rfl)
    · rw [Walk.edges_cons, Walk.edges_concat, List.concat_eq_append]
      exact List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_singleton.mpr rfl))
    · intro e he
      rw [Walk.edges_cons, Walk.edges_concat, List.concat_eq_append]
      exact List.mem_cons_of_mem _ (List.mem_append_left _ he)
  · have hab' : a ≠ b := hba.ne.symm
    refine ⟨Walk.cons hay ((r.concat hxb).concat hba), ?_, ?_, ?_, ?_⟩
    · rw [Walk.cons_isCycle_iff]
      refine ⟨(hr.concat hb hxb).concat ?_ hba, ?_⟩
      · rw [Walk.support_concat, List.mem_append, List.mem_singleton, not_or]
        exact ⟨ha, hab'⟩
      · rw [Walk.edges_concat, Walk.edges_concat, List.concat_eq_append, List.concat_eq_append,
          List.mem_append, List.mem_append, List.mem_singleton, List.mem_singleton, not_or,
          not_or]
        refine ⟨⟨fun h => ha (Walk.fst_mem_support_of_mem_edges r h), fun h => ?_⟩, fun h => ?_⟩
        · rcases Sym2.eq_iff.mp h with ⟨-, h2⟩ | ⟨h1, -⟩
          · exact hyb h2
          · exact hab' h1
        · rcases Sym2.eq_iff.mp h with ⟨h1, -⟩ | ⟨-, h2⟩
          · exact hab' h1
          · exact hyb h2
    · rw [Walk.edges_cons]
      exact List.mem_cons.mpr (Or.inl rfl)
    · rw [Walk.edges_cons, Walk.edges_concat, Walk.edges_concat, List.concat_eq_append,
        List.concat_eq_append]
      exact List.mem_cons_of_mem _
        (List.mem_append_left _ (List.mem_append_right _ (List.mem_singleton.mpr rfl)))
    · intro e he
      rw [Walk.edges_cons, Walk.edges_concat, Walk.edges_concat, List.concat_eq_append,
        List.concat_eq_append]
      exact List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_append_left _ he))

section Lift

variable [DecidableEq V] {G G' : SimpleGraph V} {v w : V}

/-- A cycle of the contracted graph lifts to a cycle of `G`. -/
lemma lift_cycle (hvw : G.Adj v w)
    (hG' : ∀ a b : V, G'.Adj a b ↔
      a ≠ b ∧ a ≠ w ∧ b ≠ w ∧ (G.Adj a b ∨ (a = v ∧ G.Adj w b) ∨ (b = v ∧ G.Adj w a)))
    {u : V} (p : G'.Walk u u) (hp : p.IsCycle) :
    ∃ (u' : V) (p' : G.Walk u' u'), p'.IsCycle ∧
      (∀ e ∈ p.edges, v ∉ e → e ∈ p'.edges) ∧
      (∀ b, s(v, b) ∈ p.edges →
        (G.Adj w b → s(w, b) ∈ p'.edges) ∧ (¬ G.Adj w b → s(v, b) ∈ p'.edges)) := by
  have F1 : ∀ a b, G'.Adj a b → a ≠ w := fun a b h => ((hG' a b).mp h).2.1
  have F2 : ∀ a b, G'.Adj a b → a ≠ v → b ≠ v → G.Adj a b := by
    intro a b h ha hb
    rcases ((hG' a b).mp h).2.2.2 with h | ⟨h, -⟩ | ⟨h, -⟩
    · exact h
    · exact absurd h ha
    · exact absurd h hb
  have F3 : ∀ b, G'.Adj v b → G.Adj v b ∨ G.Adj w b := by
    intro b h
    rcases ((hG' v b).mp h).2.2.2 with h' | ⟨-, h'⟩ | ⟨h', -⟩
    · exact Or.inl h'
    · exact Or.inr h'
    · exact absurd h'.symm ((hG' v b).mp h).1
  have hatt : ∀ b, G'.Adj v b → ∃ t, G.Adj t b ∧ (G.Adj w b → t = w) ∧
      (¬ G.Adj w b → t = v) ∧ (t = v ∨ t = w) := by
    intro b h
    by_cases hwb : G.Adj w b
    · exact ⟨w, hwb, fun _ => rfl, fun h' => absurd hwb h', Or.inr rfl⟩
    · exact ⟨v, (F3 b h).resolve_right hwb, fun h' => absurd h' hwb, fun _ => rfl, Or.inl rfl⟩
  by_cases hv : v ∈ p.support
  · obtain ⟨c, hc, hce⟩ : ∃ c : G'.Walk v v, c.IsCycle ∧ ∀ e, e ∈ c.edges ↔ e ∈ p.edges :=
      ⟨p.rotate v hv, (Walk.isCycle_rotate hv).mpr hp, fun e => (p.rotate_edges v hv).mem_iff⟩
    cases c with
    | nil => exact absurd rfl hc.ne_nil
    | cons h q =>
      rename_i x
      rw [Walk.cons_isCycle_iff] at hc
      obtain ⟨hq, hvx⟩ := hc
      obtain ⟨qr, hqrp, hqre⟩ : ∃ qr : G'.Walk v x, qr.IsPath ∧
          ∀ e, e ∈ qr.edges ↔ e ∈ q.edges :=
        ⟨q.reverse, hq.reverse, fun e => by rw [Walk.edges_reverse, List.mem_reverse]⟩
      cases qr with
      | nil => exact absurd rfl h.ne
      | cons h' r =>
        rename_i y
        rw [Walk.cons_isPath_iff] at hqrp
        obtain ⟨hr, hvr⟩ := hqrp
        have hxy : x ≠ y := by
          rintro rfl
          exact hvx ((hqre _).mp (by rw [Walk.edges_cons]; exact List.mem_cons.mpr (Or.inl rfl)))
        have hpe : ∀ e, e ∈ p.edges → e = s(v, x) ∨ e = s(v, y) ∨ e ∈ r.edges := by
          intro e he
          have h1 := (hce e).mpr he
          rw [Walk.edges_cons, List.mem_cons] at h1
          rcases h1 with h1 | h1
          · exact Or.inl h1
          · have h2 := (hqre e).mpr h1
            rw [Walk.edges_cons, List.mem_cons] at h2
            exact Or.inr h2
        have hxw : x ≠ w := fun e => F1 x v h.symm e
        have hwr : w ∉ r.support := not_mem_support_of_isolated F1 r hxw
        have hrG : ∀ e ∈ r.edges, e ∈ G.edgeSet := by
          intro e he
          induction e using Sym2.ind with
          | h a b =>
            have ha : a ≠ v := fun e => hvr (e ▸ Walk.fst_mem_support_of_mem_edges r he)
            have hb : b ≠ v := fun e => hvr (e ▸ Walk.snd_mem_support_of_mem_edges r he)
            exact F2 a b (r.adj_of_mem_edges he) ha hb
        obtain ⟨ax, hax, hax1, hax2, hax3⟩ := hatt x h
        obtain ⟨ay, hay, hay1, hay2, hay3⟩ := hatt y h'
        have hsx : ax ∉ (r.transfer G hrG).support := by
          rw [Walk.support_transfer]
          rcases hax3 with rfl | rfl
          · exact hvr
          · exact hwr
        have hsy : ay ∉ (r.transfer G hrG).support := by
          rw [Walk.support_transfer]
          rcases hay3 with rfl | rfl
          · exact hvr
          · exact hwr
        have hab : ay = ax ∨ G.Adj ax ay := by
          rcases hax3 with rfl | rfl <;> rcases hay3 with rfl | rfl
          · exact Or.inl rfl
          · exact Or.inr hvw
          · exact Or.inr hvw.symm
          · exact Or.inl rfl
        obtain ⟨c, hc, hc1, hc2, hc3⟩ :=
          close_path G (r.transfer G hrG) (hr.transfer hrG) hxy hsy hsx hay hax.symm hab
        refine ⟨ay, c, hc, ?_, ?_⟩
        · intro e he hve
          rcases hpe e he with rfl | rfl | h3
          · exact absurd (Sym2.mem_mk_left v x) hve
          · exact absurd (Sym2.mem_mk_left v y) hve
          · exact hc3 e (by rw [Walk.edges_transfer]; exact h3)
        · intro b hb
          rcases hpe _ hb with h3 | h3 | h3
          · have hbx : b = x := by
              rcases Sym2.eq_iff.mp h3 with ⟨-, h4⟩ | ⟨h4, -⟩
              · exact h4
              · exact absurd h4 h.ne
            subst hbx
            constructor
            · intro hwb
              rw [← hax1 hwb, Sym2.eq_swap]
              exact hc2
            · intro hwb
              rw [← hax2 hwb, Sym2.eq_swap]
              exact hc2
          · have hby : b = y := by
              rcases Sym2.eq_iff.mp h3 with ⟨-, h4⟩ | ⟨h4, -⟩
              · exact h4
              · exact absurd h4 h'.ne
            subst hby
            constructor
            · intro hwb
              rw [← hay1 hwb]
              exact hc1
            · intro hwb
              rw [← hay2 hwb]
              exact hc1
          · exact absurd (Walk.fst_mem_support_of_mem_edges r h3) hvr
  · have hpG : ∀ e ∈ p.edges, e ∈ G.edgeSet := by
      intro e he
      induction e using Sym2.ind with
      | h a b =>
        have ha : a ≠ v := fun e => hv (e ▸ Walk.fst_mem_support_of_mem_edges p he)
        have hb : b ≠ v := fun e => hv (e ▸ Walk.snd_mem_support_of_mem_edges p he)
        exact F2 a b (p.adj_of_mem_edges he) ha hb
    refine ⟨u, p.transfer G hpG, hp.transfer hpG, ?_, ?_⟩
    · intro e he _
      rw [Walk.edges_transfer]
      exact he
    · intro b hb
      exact absurd (Walk.fst_mem_support_of_mem_edges p hb) hv

/-- An edge of the contracted graph lifts to an edge of `G`. -/
lemma lift_edge
    (hG' : ∀ a b : V, G'.Adj a b ↔
      a ≠ b ∧ a ≠ w ∧ b ≠ w ∧ (G.Adj a b ∨ (a = v ∧ G.Adj w b) ∨ (b = v ∧ G.Adj w a)))
    (e : Sym2 V) (he : e ∈ G'.edgeSet) :
    ∃ e' ∈ G.edgeSet, (v ∉ e → e = e') ∧
      (∀ b, e = s(v, b) → (G.Adj w b → e' = s(w, b)) ∧ (¬ G.Adj w b → e' = s(v, b))) := by
  have key : ∀ b, G'.Adj v b → ∃ e' ∈ G.edgeSet, (v ∉ s(v, b) → s(v, b) = e') ∧
      (∀ b', s(v, b) = s(v, b') →
        (G.Adj w b' → e' = s(w, b')) ∧ (¬ G.Adj w b' → e' = s(v, b'))) := by
    intro b h
    have hvb : v ≠ b := ((hG' v b).mp h).1
    have hbb : ∀ b', s(v, b) = s(v, b') → b = b' := by
      intro b' h3
      rcases Sym2.eq_iff.mp h3 with ⟨-, h4⟩ | ⟨-, h4⟩
      · exact h4
      · exact absurd h4.symm hvb
    by_cases hwb : G.Adj w b
    · refine ⟨s(w, b), hwb, fun h' => absurd (Sym2.mem_mk_left v b) h', ?_⟩
      intro b' h3
      obtain rfl := hbb b' h3
      exact ⟨fun _ => rfl, fun h' => absurd hwb h'⟩
    · have hvb' : G.Adj v b := by
        rcases ((hG' v b).mp h).2.2.2 with h' | ⟨-, h'⟩ | ⟨h', -⟩
        · exact h'
        · exact absurd h' hwb
        · exact absurd h'.symm hvb
      refine ⟨s(v, b), hvb', fun _ => rfl, ?_⟩
      intro b' h3
      obtain rfl := hbb b' h3
      exact ⟨fun h' => absurd h' hwb, fun _ => rfl⟩
  induction e using Sym2.ind with
  | h a b =>
    have hab : G'.Adj a b := he
    by_cases ha : a = v
    · subst ha
      exact key b hab
    · by_cases hb : b = v
      · subst hb
        rw [Sym2.eq_swap]
        exact key a hab.symm
      · have hG : G.Adj a b := by
          rcases ((hG' a b).mp hab).2.2.2 with h | ⟨h, -⟩ | ⟨h, -⟩
          · exact h
          · exact absurd h ha
          · exact absurd h hb
        refine ⟨s(a, b), hG, fun _ => rfl, ?_⟩
        intro b' h3
        have hmem : v ∈ s(a, b) := h3 ▸ Sym2.mem_mk_left v b'
        rcases Sym2.mem_iff.mp hmem with h4 | h4
        · exact absurd h4.symm ha
        · exact absurd h4.symm hb

end Lift

lemma card_components_lt {G G' : SimpleGraph V} [Finite V] {v w : V}
    (hreach : ∀ a b, G'.Adj a b → G.Reachable a b)
    (hvw : G.Reachable v w) (hnot : ¬ G'.Reachable v w) :
    Nat.card G.ConnectedComponent < Nat.card G'.ConnectedComponent := by
  classical
  have hR : ∀ a b, G'.Reachable a b → G.Reachable a b := by
    rintro a b ⟨p⟩
    induction p with
    | nil => exact Reachable.refl _
    | cons h p ih => exact (hreach _ _ h).trans ih
  have hfin : Finite G.ConnectedComponent :=
    Finite.of_surjective G.connectedComponentMk (fun c => Quot.exists_rep c)
  have hfin' : Finite G'.ConnectedComponent :=
    Finite.of_surjective G'.connectedComponentMk (fun c => Quot.exists_rep c)
  have := Fintype.ofFinite G.ConnectedComponent
  have := Fintype.ofFinite G'.ConnectedComponent
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  refine Fintype.card_lt_of_surjective_not_injective
    (ConnectedComponent.lift (fun a => G.connectedComponentMk a)
      (fun a b p _ => ConnectedComponent.sound (hR a b ⟨p⟩))) ?_ ?_
  · intro c
    obtain ⟨a, rfl⟩ := Quot.exists_rep c
    exact ⟨G'.connectedComponentMk a, rfl⟩
  · intro hinj
    have h : G'.connectedComponentMk v = G'.connectedComponentMk w :=
      hinj (ConnectedComponent.sound hvw)
    exact hnot (ConnectedComponent.exact h)

theorem contraction_step :
  ∀ (V : Type) [Fintype V] [DecidableEq V] (G G' : SimpleGraph V) (v w : V),
    G.Adj v w →
    (∀ x y : V, G.Adj v x → G.Adj w x → G.Adj v y → G.Adj w y → x = y) →
    (∀ a b : V, G'.Adj a b ↔
      a ≠ b ∧ a ≠ w ∧ b ≠ w ∧ (G.Adj a b ∨ (a = v ∧ G.Adj w b) ∨ (b = v ∧ G.Adj w a))) →
    (∃ S : Finset (Finset (Sym2 V)),
      (∀ s ∈ S, (∃ e ∈ G'.edgeSet, s = {e}) ∨
        ∃ (u : V) (p : G'.Walk u u), p.IsCycle ∧ s = p.edges.toFinset) ∧
      (∀ e ∈ G'.edgeSet, ∃ s ∈ S, e ∈ s) ∧
      S.card + Nat.card G'.ConnectedComponent ≤ Fintype.card V) →
    ∃ S : Finset (Finset (Sym2 V)),
      (∀ s ∈ S, (∃ e ∈ G.edgeSet, s = {e}) ∨
        ∃ (u : V) (p : G.Walk u u), p.IsCycle ∧ s = p.edges.toFinset) ∧
      (∀ e ∈ G.edgeSet, ∃ s ∈ S, e ∈ s) ∧
      S.card + Nat.card G.ConnectedComponent ≤ Fintype.card V := by
  intro V _ _ G G' v w hvw hcom hG'
  rintro ⟨S', hS', hcov', hcard'⟩
  -- every piece of the cover of `G'` lifts to a piece of `G`
  have hitem : ∀ s ∈ S', ∃ s' : Finset (Sym2 V),
      ((∃ e ∈ G.edgeSet, s' = {e}) ∨
        ∃ (u : V) (p : G.Walk u u), p.IsCycle ∧ s' = p.edges.toFinset) ∧
      (∀ e ∈ s, v ∉ e → e ∈ s') ∧
      (∀ b, s(v, b) ∈ s → (G.Adj w b → s(w, b) ∈ s') ∧ (¬ G.Adj w b → s(v, b) ∈ s')) := by
    intro s hs
    rcases hS' s hs with ⟨e, he, rfl⟩ | ⟨u, p, hp, rfl⟩
    · obtain ⟨e', he', h1, h2⟩ := lift_edge hG' e he
      refine ⟨{e'}, Or.inl ⟨e', he', rfl⟩, ?_, ?_⟩
      · intro e₁ he₁ hv
        rw [Finset.mem_singleton] at he₁ ⊢
        subst he₁
        exact h1 hv
      · intro b hb
        rw [Finset.mem_singleton] at hb
        obtain ⟨h3, h4⟩ := h2 b hb.symm
        exact ⟨fun hwb => Finset.mem_singleton.mpr (h3 hwb).symm,
          fun hwb => Finset.mem_singleton.mpr (h4 hwb).symm⟩
    · obtain ⟨u', p', hp', h1, h2⟩ := lift_cycle hvw hG' p hp
      refine ⟨p'.edges.toFinset, Or.inr ⟨u', p', hp', rfl⟩, ?_, ?_⟩
      · intro e he hv
        exact List.mem_toFinset.mpr (h1 e (List.mem_toFinset.mp he) hv)
      · intro b hb
        obtain ⟨h3, h4⟩ := h2 b (List.mem_toFinset.mp hb)
        exact ⟨fun hwb => List.mem_toFinset.mpr (h3 hwb),
          fun hwb => List.mem_toFinset.mpr (h4 hwb)⟩
  choose! g hg using hitem
  -- one more piece: the triangle on `v`, `w` and their common neighbour, or the edge `vw`
  obtain ⟨X, hX, hXvw, hXz⟩ : ∃ X : Finset (Sym2 V),
      ((∃ e ∈ G.edgeSet, X = {e}) ∨
        ∃ (u : V) (p : G.Walk u u), p.IsCycle ∧ X = p.edges.toFinset) ∧
      s(v, w) ∈ X ∧ ∀ z, G.Adj v z → G.Adj w z → s(v, z) ∈ X := by
    by_cases hz : ∃ z, G.Adj v z ∧ G.Adj w z
    · obtain ⟨z, hvz, hwz⟩ := hz
      have hcyc : (Walk.cons hvw (Walk.cons hwz (Walk.cons hvz.symm Walk.nil))).IsCycle := by
        rw [Walk.cons_isCycle_iff]
        constructor
        · rw [Walk.cons_isPath_iff, Walk.cons_isPath_iff]
          refine ⟨⟨Walk.IsPath.nil, ?_⟩, ?_⟩
          · rw [Walk.support_nil, List.mem_singleton]
            exact hvz.ne.symm
          · rw [Walk.support_cons, Walk.support_nil, List.mem_cons, List.mem_singleton, not_or]
            exact ⟨hwz.ne, hvw.ne.symm⟩
        · rw [Walk.edges_cons, Walk.edges_cons, Walk.edges_nil, List.mem_cons, List.mem_singleton,
            not_or]
          constructor
          · intro h
            rcases Sym2.eq_iff.mp h with ⟨h1, -⟩ | ⟨h1, -⟩
            · exact hvw.ne h1
            · exact hvz.ne h1
          · intro h
            rcases Sym2.eq_iff.mp h with ⟨h1, -⟩ | ⟨-, h1⟩
            · exact hvz.ne h1
            · exact hwz.ne h1
      refine ⟨_, Or.inr ⟨v, _, hcyc, rfl⟩, ?_, ?_⟩
      · rw [List.mem_toFinset, Walk.edges_cons]
        exact List.mem_cons.mpr (Or.inl rfl)
      · intro z' hvz' hwz'
        obtain rfl := hcom z' z hvz' hwz' hvz hwz
        rw [List.mem_toFinset, Walk.edges_cons, Walk.edges_cons, Walk.edges_cons]
        exact List.mem_cons_of_mem _
          (List.mem_cons_of_mem _ (List.mem_cons.mpr (Or.inl Sym2.eq_swap)))
    · refine ⟨{s(v, w)}, Or.inl ⟨s(v, w), hvw, rfl⟩, Finset.mem_singleton.mpr rfl, ?_⟩
      intro z hvz hwz
      exact absurd ⟨z, hvz, hwz⟩ hz
  have hvw' : v ≠ w := hvw.ne
  -- coverage of the three kinds of edges of `G`
  have C1 : ∀ b, G.Adj w b → b ≠ v → ∃ s ∈ insert X (S'.image g), s(w, b) ∈ s := by
    intro b hwb hbv
    have hG'b : G'.Adj v b :=
      (hG' v b).mpr ⟨fun e => hbv e.symm, hvw', hwb.ne.symm, Or.inr (Or.inl ⟨rfl, hwb⟩)⟩
    obtain ⟨s, hs, hes⟩ := hcov' s(v, b) hG'b
    exact ⟨g s, Finset.mem_insert_of_mem (Finset.mem_image_of_mem g hs),
      ((hg s hs).2.2 b hes).1 hwb⟩
  have C2 : ∀ b, G.Adj v b → b ≠ w → ∃ s ∈ insert X (S'.image g), s(v, b) ∈ s := by
    intro b hvb hbw
    by_cases hwb : G.Adj w b
    · exact ⟨X, Finset.mem_insert_self _ _, hXz b hvb hwb⟩
    · have hG'b : G'.Adj v b := (hG' v b).mpr ⟨hvb.ne, hvw', hbw, Or.inl hvb⟩
      obtain ⟨s, hs, hes⟩ := hcov' s(v, b) hG'b
      exact ⟨g s, Finset.mem_insert_of_mem (Finset.mem_image_of_mem g hs),
        ((hg s hs).2.2 b hes).2 hwb⟩
  have hreach : ∀ a b, G'.Adj a b → G.Reachable a b := by
    intro a b h
    rcases ((hG' a b).mp h).2.2.2 with h' | ⟨rfl, h'⟩ | ⟨rfl, h'⟩
    · exact h'.reachable
    · exact hvw.reachable.trans h'.reachable
    · exact h'.symm.reachable.trans hvw.symm.reachable
  have hnot : ¬ G'.Reachable v w := by
    rintro ⟨p⟩
    have q := p.reverse
    cases q with
    | nil => exact hvw' rfl
    | cons h _ => exact ((hG' _ _).mp h).2.1 rfl
  have hcomp := card_components_lt hreach hvw.reachable hnot
  refine ⟨insert X (S'.image g), ?_, ?_, ?_⟩
  · intro s hs
    rcases Finset.mem_insert.mp hs with rfl | hs
    · exact hX
    · obtain ⟨s₀, hs₀, rfl⟩ := Finset.mem_image.mp hs
      exact (hg s₀ hs₀).1
  · intro e he
    induction e using Sym2.ind with
    | h a b =>
      have hab : G.Adj a b := he
      by_cases haw : a = w
      · subst haw
        by_cases hbv : b = v
        · subst hbv
          exact ⟨X, Finset.mem_insert_self _ _, by rw [Sym2.eq_swap]; exact hXvw⟩
        · exact C1 b hab hbv
      · by_cases hbw : b = w
        · subst hbw
          by_cases hav : a = v
          · subst hav
            exact ⟨X, Finset.mem_insert_self _ _, hXvw⟩
          · rw [Sym2.eq_swap]
            exact C1 a hab.symm hav
        · by_cases hav : a = v
          · subst hav
            exact C2 b hab hbw
          · by_cases hbv : b = v
            · subst hbv
              rw [Sym2.eq_swap]
              exact C2 a hab.symm haw
            · have hG'ab : G'.Adj a b := (hG' a b).mpr ⟨hab.ne, haw, hbw, Or.inl hab⟩
              obtain ⟨s, hs, hes⟩ := hcov' s(a, b) hG'ab
              refine ⟨g s, Finset.mem_insert_of_mem (Finset.mem_image_of_mem g hs),
                (hg s hs).2.1 _ hes ?_⟩
              intro hmem
              rcases Sym2.mem_iff.mp hmem with h4 | h4
              · exact hav h4.symm
              · exact hbv h4.symm
  · have h1 : (insert X (S'.image g)).card ≤ S'.card + 1 :=
      (Finset.card_insert_le _ _).trans (Nat.succ_le_succ Finset.card_image_le)
    omega

end Erdos184CoveringStep

theorem OMA.solution : OMA.R_Erdos184_erdos_184_variants_covering_R1.H1 :=
  Erdos184CoveringStep.contraction_step
