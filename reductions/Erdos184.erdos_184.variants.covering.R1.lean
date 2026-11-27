import FormalConjectures.ErdosProblems.«184»

-- Reduction Erdos184.erdos_184.variants.covering.R1 of Erdős Problem 184 — covering
-- Credit: @ivillar
-- The three helper lemmas edge_card_eq_ncard, coe_edge_card and cycle_subgraph_good are reused from the
-- merged proof of Erdos184.erdos_184.variants.n_log_n by @Genbox (PR #720).

/-!
# Pyber's covering theorem: contraction of an edge lying in at most one triangle

Pyber's theorem says that the edges of a graph on `n` vertices can be covered by `n - 1` cycles and
edges. Both hypotheses use the component form of the bound, and describe a cover by the edge sets of
its pieces: a finite set `S` of finite sets of edges, each of them a single edge of `G` or the edge
set of a cycle (a closed walk with `IsCycle`), covering every edge of `G`, with
`S.card + (number of connected components of G) ≤ (number of vertices)`.

* `H1` (contraction step): let `v w` be adjacent with at most one common neighbour, and let `G'` be
  `G` with the edge `vw` contracted into `v` (the vertex `w` stays, isolated). A cover of `G'` of
  that size gives a cover of `G` of that size. Proof idea: a cycle of `G'` through `v` lifts to a
  cycle of `G` through `v`, through `w`, or through the edge `vw`; one more piece (the triangle on
  `v`, `w` and the common neighbour, or the edge `vw`) covers what is left, and `G'` has one more
  component than `G`.
* `H2` (core): the same bound for the graphs in which every edge lies in at least two triangles.

`main` is an induction on the number of non-isolated vertices: contract while some edge has at most
one common neighbour (`H1`), finish with `H2`, and turn the pieces into subgraphs.
-/

namespace OMA.R_Erdos184_erdos_184_variants_covering_R1

/-- Contraction step: a cover of the graph `G'`, obtained by contracting an edge `vw` of `G` whose
ends have at most one common neighbour, gives a cover of `G` within the same bound. -/
def H1 : Prop :=
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
      S.card + Nat.card G.ConnectedComponent ≤ Fintype.card V

/-- Core: Pyber's bound, in the component form, for the graphs in which the two ends of every edge
have at least two common neighbours. -/
def H2 : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
    (∀ v w : V, G.Adj v w →
      ∃ x y : V, x ≠ y ∧ G.Adj v x ∧ G.Adj w x ∧ G.Adj v y ∧ G.Adj w y) →
    ∃ S : Finset (Finset (Sym2 V)),
      (∀ s ∈ S, (∃ e ∈ G.edgeSet, s = {e}) ∨
        ∃ (u : V) (p : G.Walk u u), p.IsCycle ∧ s = p.edges.toFinset) ∧
      (∀ e ∈ G.edgeSet, ∃ s ∈ S, e ∈ s) ∧
      S.card + Nat.card G.ConnectedComponent ≤ Fintype.card V

open SimpleGraph
open scoped Classical

lemma edge_card_eq_ncard {V : Type} [Fintype V] (G : SimpleGraph V)
    [Fintype G.edgeSet] : G.edgeFinset.card = G.edgeSet.ncard := by
  exact (Set.ncard_eq_toFinset_card' G.edgeSet).symm

lemma coe_edge_card {V : Type} [Fintype V] (G : SimpleGraph V) (H : G.Subgraph) :
    H.coe.edgeFinset.card = H.edgeSet.ncard := by
  rw [edge_card_eq_ncard, ← H.image_coe_edgeSet_coe]
  exact (Set.ncard_image_of_injective _ (Sym2.map.injective Subtype.val_injective)).symm

lemma cycle_subgraph_good {V : Type} [Fintype V] (G : SimpleGraph V)
    {v : V} (p : G.Walk v v) (hp : p.IsCycle) : Erdos184.IsCycleOrEdge p.toSubgraph.coe := by
  apply Or.inl
  refine ⟨p.toSubgraph_connected.coe, ?_⟩
  intro w
  rw [Subgraph.coe_degree]
  change Fintype.card (p.toSubgraph.neighborSet (w : V)) = 2
  rw [Set.fintypeCard_eq_ncard]
  exact hp.ncard_neighborSet_toSubgraph_eq_two ((Walk.mem_verts_toSubgraph p).mp w.property)

lemma piece_of_item {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (s : Finset (Sym2 V))
    (hs : (∃ e ∈ G.edgeSet, s = {e}) ∨
      ∃ (u : V) (p : G.Walk u u), p.IsCycle ∧ s = p.edges.toFinset) :
    ∃ H : G.Subgraph, Erdos184.IsCycleOrEdge H.coe ∧ H.edgeSet = (s : Set (Sym2 V)) := by
  rcases hs with ⟨e, he, rfl⟩ | ⟨u, p, hp, rfl⟩
  · induction e using Sym2.ind with
    | h a b =>
      have hab : G.Adj a b := by simpa using he
      have hH : (G.subgraphOfAdj hab).edgeSet = {s(a, b)} := by simp
      have hcount : (G.subgraphOfAdj hab).edgeSet.ncard = 1 := by
        rw [hH, Set.ncard_singleton]
      exact ⟨G.subgraphOfAdj hab, Or.inr ((coe_edge_card G _).trans hcount), by rw [hH]; simp⟩
  · refine ⟨p.toSubgraph, cycle_subgraph_good G p hp, ?_⟩
    rw [Walk.edgeSet_toSubgraph]
    ext e
    simp

theorem main : H1 → H2 → type_of% @Erdos184.erdos_184.variants.covering := by
  intro h1 h2 V _ _ _ G
  have key : ∀ (n : ℕ) (G : SimpleGraph V), G.support.ncard = n →
      ∃ S : Finset (Finset (Sym2 V)),
        (∀ s ∈ S, (∃ e ∈ G.edgeSet, s = {e}) ∨
          ∃ (u : V) (p : G.Walk u u), p.IsCycle ∧ s = p.edges.toFinset) ∧
        (∀ e ∈ G.edgeSet, ∃ s ∈ S, e ∈ s) ∧
        S.card + Nat.card G.ConnectedComponent ≤ Fintype.card V := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro G hG
      by_cases hA : ∃ v w, G.Adj v w ∧
          ∀ x y : V, G.Adj v x → G.Adj w x → G.Adj v y → G.Adj w y → x = y
      · obtain ⟨v, w, hvw, hcom⟩ := hA
        have hG' : ∀ a b : V,
            (SimpleGraph.fromRel (fun a b : V =>
              a ≠ w ∧ b ≠ w ∧ (G.Adj a b ∨ (a = v ∧ G.Adj w b)))).Adj a b ↔
            a ≠ b ∧ a ≠ w ∧ b ≠ w ∧
              (G.Adj a b ∨ (a = v ∧ G.Adj w b) ∨ (b = v ∧ G.Adj w a)) := by
          intro a b
          have hc := G.adj_comm a b
          simp only [SimpleGraph.fromRel_adj]
          tauto
        have hsub : (SimpleGraph.fromRel (fun a b : V =>
              a ≠ w ∧ b ≠ w ∧ (G.Adj a b ∨ (a = v ∧ G.Adj w b)))).support ⊆
            G.support \ {w} := by
          intro a ha
          obtain ⟨b, hab⟩ := (SimpleGraph.mem_support _).mp ha
          rw [hG'] at hab
          obtain ⟨-, haw, -, h⟩ := hab
          refine ⟨(SimpleGraph.mem_support _).mpr ?_, by simpa using haw⟩
          rcases h with h | ⟨rfl, -⟩ | ⟨-, h⟩
          · exact ⟨b, h⟩
          · exact ⟨w, hvw⟩
          · exact ⟨w, h.symm⟩
        have hw : w ∈ G.support := (SimpleGraph.mem_support _).mpr ⟨v, hvw.symm⟩
        have hfin : G.support.Finite := Set.toFinite _
        have hlt : (SimpleGraph.fromRel (fun a b : V =>
              a ≠ w ∧ b ≠ w ∧ (G.Adj a b ∨ (a = v ∧ G.Adj w b)))).support.ncard <
            G.support.ncard :=
          lt_of_le_of_lt (Set.ncard_le_ncard hsub (hfin.subset Set.sdiff_subset))
            (Set.ncard_sdiff_singleton_lt_of_mem hw hfin)
        exact h1 V G _ v w hvw hcom hG' (ih _ (hG ▸ hlt) _ rfl)
      · apply h2 V G
        intro v w hvw
        by_contra hno
        refine hA ⟨v, w, hvw, fun x y hvx hwx hvy hwy => ?_⟩
        by_contra hxy
        exact hno ⟨x, y, hxy, hvx, hwx, hvy, hwy⟩
  obtain ⟨S, hS, hcov, hcard⟩ := key _ G rfl
  have hex : ∀ s ∈ S, ∃ H : G.Subgraph,
      Erdos184.IsCycleOrEdge H.coe ∧ H.edgeSet = (s : Set (Sym2 V)) :=
    fun s hs => piece_of_item G s (hS s hs)
  choose f hf using hex
  have hfinC : Finite G.ConnectedComponent :=
    Finite.of_surjective G.connectedComponentMk (fun c => Quot.exists_rep c)
  have hneC : Nonempty G.ConnectedComponent :=
    ⟨G.connectedComponentMk (Classical.arbitrary V)⟩
  have hpos : 0 < Nat.card G.ConnectedComponent := Nat.card_pos
  refine ⟨S.attach.image (fun s => f s.1 s.2), ?_, ?_, ?_⟩
  · intro H hH
    obtain ⟨s, -, rfl⟩ := Finset.mem_image.mp hH
    exact (hf s.1 s.2).1
  · ext e
    simp only [Set.mem_iUnion, exists_prop]
    constructor
    · rintro ⟨H, -, he⟩
      exact H.edgeSet_subset he
    · intro he
      obtain ⟨s, hs, hes⟩ := hcov e he
      refine ⟨f s hs, Finset.mem_image.mpr ⟨⟨s, hs⟩, Finset.mem_attach _ _, rfl⟩, ?_⟩
      rw [(hf s hs).2]
      exact hes
  · have hle : (S.attach.image (fun s => f s.1 s.2)).card ≤ S.card :=
      Finset.card_image_le.trans_eq Finset.card_attach
    have hnat : (S.attach.image (fun s => f s.1 s.2)).card + 1 ≤ Fintype.card V := by omega
    have hreal : (((S.attach.image (fun s => f s.1 s.2)).card + 1 : ℕ) : ℝ) ≤
        (Fintype.card V : ℝ) := by
      exact_mod_cast hnat
    push_cast at hreal
    linarith

end OMA.R_Erdos184_erdos_184_variants_covering_R1
