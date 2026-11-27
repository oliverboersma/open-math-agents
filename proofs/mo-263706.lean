import OMAStatements.S_mo_263706
import Mathlib

namespace MO263706Aux

/-- The 24 edges: the cycle 0, 1, ..., 15 and eight chords. -/
def edgeList : List (ℕ × ℕ) :=
  [(0, 1), (1, 2), (2, 3), (3, 4), (4, 5), (5, 6), (6, 7), (7, 8), (8, 9), (9, 10), (10, 11),
   (11, 12), (12, 13), (13, 14), (14, 15), (15, 0),
   (0, 3), (1, 4), (2, 5), (6, 14), (7, 15), (8, 11), (9, 12), (10, 13)]

def adjB (a b : Fin 16) : Bool :=
  edgeList.contains (a.val, b.val) || edgeList.contains (b.val, a.val)

lemma adjB_symm : ∀ a b : Fin 16, adjB a b = true → adjB b a = true := by
  intro a b h
  unfold adjB at h ⊢
  rw [Bool.or_comm]
  exact h

set_option maxRecDepth 100000 in
lemma adjB_irrefl : ∀ a : Fin 16, ¬ (adjB a a = true) := by decide

/-- The witness graph. -/
def G : SimpleGraph (Fin 16) where
  Adj a b := adjB a b = true
  symm := ⟨fun a b h => adjB_symm a b h⟩
  loopless := ⟨fun a h => adjB_irrefl a h⟩

lemma adj_of {a b : Fin 16} (h : adjB a b = true) : G.Adj a b := h

lemma adjB_of {a b : Fin 16} (h : G.Adj a b) : adjB a b = true := h

set_option maxRecDepth 100000 in
lemma cubicB : ∀ v : Fin 16, (Finset.univ.filter (fun w => adjB v w = true)).card = 3 := by
  decide

lemma cubic (v : Fin 16) : (G.neighborSet v).ncard = 3 := by
  have h : G.neighborSet v = ↑(Finset.univ.filter (fun w => adjB v w = true)) := by
    ext w
    simp only [SimpleGraph.mem_neighborSet, Finset.coe_filter, Finset.mem_univ, true_and]
    exact Iff.rfl
  rw [h, Set.ncard_coe_finset]
  exact cubicB v

/-- The hamiltonian cycle 0, 1, ..., 15, 0. -/
def hamWalk : G.Walk 0 0 :=
  .cons (adj_of (by decide) : G.Adj 0 1) <|
  .cons (adj_of (by decide) : G.Adj 1 2) <|
  .cons (adj_of (by decide) : G.Adj 2 3) <|
  .cons (adj_of (by decide) : G.Adj 3 4) <|
  .cons (adj_of (by decide) : G.Adj 4 5) <|
  .cons (adj_of (by decide) : G.Adj 5 6) <|
  .cons (adj_of (by decide) : G.Adj 6 7) <|
  .cons (adj_of (by decide) : G.Adj 7 8) <|
  .cons (adj_of (by decide) : G.Adj 8 9) <|
  .cons (adj_of (by decide) : G.Adj 9 10) <|
  .cons (adj_of (by decide) : G.Adj 10 11) <|
  .cons (adj_of (by decide) : G.Adj 11 12) <|
  .cons (adj_of (by decide) : G.Adj 12 13) <|
  .cons (adj_of (by decide) : G.Adj 13 14) <|
  .cons (adj_of (by decide) : G.Adj 14 15) <|
  .cons (adj_of (by decide) : G.Adj 15 0) .nil

lemma ham : G.IsHamiltonian := by
  intro _
  refine ⟨0, hamWalk, ?_⟩
  rw [SimpleGraph.Walk.isHamiltonianCycle_iff_isCycle_and_length_eq]
  refine ⟨?_, ?_⟩
  · unfold hamWalk
    rw [SimpleGraph.Walk.cons_isCycle_iff]
    constructor
    · simp [SimpleGraph.Walk.cons_isPath_iff]
    · simp
  · simp [hamWalk]

lemma no7 (a b c d e f g : Fin 2)
    (h1 : a ≠ b) (h2 : b ≠ c) (h3 : c ≠ d) (h4 : d ≠ e) (h5 : e ≠ f) (h6 : f ≠ g) (h7 : g ≠ a) :
    False := by
  have key : ∀ x y : Fin 2, x ≠ y → x.val + y.val = 1 := by decide
  have := key a b h1
  have := key b c h2
  have := key c d h3
  have := key d e h4
  have := key e f h5
  have := key f g h6
  have := key g a h7
  omega

lemma notBip : ¬ G.IsBipartite := by
  rintro ⟨C⟩
  exact no7 (C 6) (C 5) (C 4) (C 3) (C 0) (C 15) (C 14)
    (C.valid (adj_of (by decide) : G.Adj 6 5))
    (C.valid (adj_of (by decide) : G.Adj 5 4))
    (C.valid (adj_of (by decide) : G.Adj 4 3))
    (C.valid (adj_of (by decide) : G.Adj 3 0))
    (C.valid (adj_of (by decide) : G.Adj 0 15))
    (C.valid (adj_of (by decide) : G.Adj 15 14))
    (C.valid (adj_of (by decide) : G.Adj 14 6))

/-- The sum of an edge indicator over all vertices only sees the three neighbours. -/
lemma deg3 (x : Fin 16 → Fin 16 → ℕ) (hx0 : ∀ v w, adjB v w = false → x v w = 0)
    (v a b c : Fin 16)
    (h : (a ≠ b ∧ a ≠ c ∧ b ≠ c) ∧
      ∀ w : Fin 16, w ≠ a → w ≠ b → w ≠ c → adjB v w = false) :
    ∑ w, x v w = x v a + x v b + x v c := by
  obtain ⟨⟨hab, hac, hbc⟩, hrest⟩ := h
  have h3 : ∑ w ∈ ({a, b, c} : Finset (Fin 16)), x v w = x v a + x v b + x v c := by
    rw [Finset.sum_insert (by simp [hab, hac]), Finset.sum_insert (by simp [hbc]),
      Finset.sum_singleton, add_assoc]
  rw [← h3]
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro w _ hw
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hw
  exact hx0 v w (hrest w hw.1 hw.2.1 hw.2.2)

set_option maxRecDepth 100000 in
/-- Arithmetic core: no spanning-minus-one 2-regular connected edge set exists. -/
lemma core (x : Fin 16 → Fin 16 → ℕ) (s : Fin 16 → ℕ)
    (hx0 : ∀ v w, adjB v w = false → x v w = 0)
    (hsym : ∀ v w, x v w = x w v)
    (hx1 : ∀ v w, x v w ≤ 1)
    (hs1 : ∀ v, s v ≤ 1)
    (hdeg : ∀ v, ∑ w, x v w = 2 * s v)
    (htot : ∑ v, s v = 15) :
    (s 0 = 1 → s 8 = 1 → 1 ≤ x 0 15 + x 5 6) →
    (s 0 = 1 → s 8 = 1 → 1 ≤ x 8 7 + x 13 14) → False := by
  have d0 := (deg3 x hx0 0 1 3 15 (by decide)).symm.trans (hdeg 0)
  have d1 := (deg3 x hx0 1 0 2 4 (by decide)).symm.trans (hdeg 1)
  have d2 := (deg3 x hx0 2 1 3 5 (by decide)).symm.trans (hdeg 2)
  have d3 := (deg3 x hx0 3 0 2 4 (by decide)).symm.trans (hdeg 3)
  have d4 := (deg3 x hx0 4 1 3 5 (by decide)).symm.trans (hdeg 4)
  have d5 := (deg3 x hx0 5 2 4 6 (by decide)).symm.trans (hdeg 5)
  have d6 := (deg3 x hx0 6 5 7 14 (by decide)).symm.trans (hdeg 6)
  have d7 := (deg3 x hx0 7 6 8 15 (by decide)).symm.trans (hdeg 7)
  have d8 := (deg3 x hx0 8 7 9 11 (by decide)).symm.trans (hdeg 8)
  have d9 := (deg3 x hx0 9 8 10 12 (by decide)).symm.trans (hdeg 9)
  have d10 := (deg3 x hx0 10 9 11 13 (by decide)).symm.trans (hdeg 10)
  have d11 := (deg3 x hx0 11 8 10 12 (by decide)).symm.trans (hdeg 11)
  have d12 := (deg3 x hx0 12 9 11 13 (by decide)).symm.trans (hdeg 12)
  have d13 := (deg3 x hx0 13 10 12 14 (by decide)).symm.trans (hdeg 13)
  have d14 := (deg3 x hx0 14 6 13 15 (by decide)).symm.trans (hdeg 14)
  have d15 := (deg3 x hx0 15 0 7 14 (by decide)).symm.trans (hdeg 15)
  have pA : s 0 + s 2 + s 4 = s 1 + s 3 + s 5 ∧ x 0 15 = x 5 6 := by
    have e1 := hsym 1 0
    have e2 := hsym 3 0
    have e3 := hsym 1 2
    have e4 := hsym 3 2
    have e5 := hsym 5 2
    have e6 := hsym 3 4
    have e7 := hsym 5 4
    have e8 := hsym 1 4
    have b1 := hx1 0 15
    have b2 := hx1 5 6
    omega
  have pB : s 8 + s 10 + s 12 = s 9 + s 11 + s 13 ∧ x 8 7 = x 13 14 := by
    have e1 := hsym 9 8
    have e2 := hsym 11 8
    have e3 := hsym 9 10
    have e4 := hsym 11 10
    have e5 := hsym 13 10
    have e6 := hsym 9 12
    have e7 := hsym 11 12
    have e8 := hsym 13 12
    have b1 := hx1 8 7
    have b2 := hx1 13 14
    omega
  simp [Fin.sum_univ_succ] at htot
  have t0 := hs1 0
  have t1 := hs1 1
  have t2 := hs1 2
  have t3 := hs1 3
  have t4 := hs1 4
  have t5 := hs1 5
  have t6 := hs1 6
  have t7 := hs1 7
  have t8 := hs1 8
  have t9 := hs1 9
  have t10 := hs1 10
  have t11 := hs1 11
  have t12 := hs1 12
  have t13 := hs1 13
  have t14 := hs1 14
  have t15 := hs1 15
  have hall : s 0 = 1 ∧ s 8 = 1 ∧ s 6 + s 7 + s 14 + s 15 = 3 := by
    omega
  intro hcA hcB
  have cA := hcA hall.1 hall.2.1
  have cB := hcB hall.1 hall.2.1
  have f1 := hsym 15 0
  have f2 := hsym 6 5
  have f3 := hsym 7 8
  have f4 := hsym 14 13
  have g1 := hx1 0 15
  have g2 := hx1 8 7
  have hC := hall.2.2
  have hxA := pA.2
  have hxB := pB.2
  clear hcA hcB pA pB hall
  omega

lemma crossA : ∀ c d : Fin 16, adjB c d = true → c.val < 6 → ¬ d.val < 6 →
    (c = 0 ∧ d = 15) ∨ (c = 5 ∧ d = 6) := by
  decide

lemma crossB : ∀ c d : Fin 16, adjB c d = true → (8 ≤ c.val ∧ c.val ≤ 13) →
    ¬ (8 ≤ d.val ∧ d.val ≤ 13) → (c = 8 ∧ d = 7) ∨ (c = 13 ∧ d = 14) := by
  decide

/-- A walk visiting both a vertex inside `S` and one outside uses an edge leaving `S`. -/
lemma cross {u v : Fin 16} (p : G.Walk u v) (S : Set (Fin 16)) {a b : Fin 16}
    (ha : a ∈ p.support) (hb : b ∈ p.support) (haS : a ∈ S) (hbS : b ∉ S) :
    ∃ c d, c ∈ S ∧ d ∉ S ∧ s(c, d) ∈ p.edges := by
  by_cases hu : u ∈ S
  · obtain ⟨d, hd, h1, h2⟩ := (p.takeUntil b hb).exists_boundary_dart S hu hbS
    refine ⟨d.fst, d.snd, h1, h2, ?_⟩
    apply p.edges_takeUntil_subset_edges hb
    exact List.mem_map_of_mem hd
  · obtain ⟨d, hd, h1, h2⟩ :=
      (p.takeUntil a ha).exists_boundary_dart Sᶜ hu (fun h => h haS)
    refine ⟨d.snd, d.fst, by simpa using h2, h1, ?_⟩
    apply p.edges_takeUntil_subset_edges ha
    have hmem : d.edge ∈ (p.takeUntil a ha).edges := List.mem_map_of_mem hd
    rw [Sym2.eq_swap]
    exact hmem

lemma no15 (v : Fin 16) (p : G.Walk v v) (hc : p.IsCycle) (hlen : p.length = 15) : False := by
  classical
  obtain ⟨x, hx⟩ : ∃ x : Fin 16 → Fin 16 → ℕ,
      ∀ a b, x a b = if p.toSubgraph.Adj a b then 1 else 0 :=
    ⟨fun a b => if p.toSubgraph.Adj a b then 1 else 0, fun _ _ => rfl⟩
  obtain ⟨s, hs⟩ : ∃ s : Fin 16 → ℕ, ∀ a, s a = if a ∈ p.support then 1 else 0 :=
    ⟨fun a => if a ∈ p.support then 1 else 0, fun _ => rfl⟩
  have hxpos : ∀ a b, p.toSubgraph.Adj a b → x a b = 1 := by
    intro a b h
    rw [hx, if_pos h]
  have hx0 : ∀ a b, adjB a b = false → x a b = 0 := by
    intro a b hab
    rw [hx]
    apply if_neg
    intro h
    have h' := adjB_of h.adj_sub
    rw [hab] at h'
    exact Bool.false_ne_true h'
  have hsym : ∀ a b, x a b = x b a := by
    intro a b
    rw [hx a b, hx b a]
    simp only [p.toSubgraph.adj_comm a b]
  have hx1 : ∀ a b, x a b ≤ 1 := by
    intro a b
    rw [hx]
    split_ifs <;> omega
  have hs1 : ∀ a, s a ≤ 1 := by
    intro a
    rw [hs]
    split_ifs <;> omega
  have hdeg : ∀ a, ∑ w, x a w = 2 * s a := by
    intro a
    have hcard : ∑ w, x a w = (p.toSubgraph.neighborSet a).ncard := by
      have hset : p.toSubgraph.neighborSet a
          = ↑(Finset.univ.filter (fun w => p.toSubgraph.Adj a w)) := by
        ext w
        simp [SimpleGraph.Subgraph.mem_neighborSet]
      rw [hset, Set.ncard_coe_finset, Finset.card_filter]
      apply Finset.sum_congr rfl
      intro w _
      exact hx a w
    rw [hcard, hs]
    by_cases ha : a ∈ p.support
    · rw [hc.ncard_neighborSet_toSubgraph_eq_two ha, if_pos ha]
    · have hempty : p.toSubgraph.neighborSet a = ∅ := by
        ext w
        simp only [SimpleGraph.Subgraph.mem_neighborSet, Set.mem_empty_iff_false, iff_false]
        intro h
        exact ha ((SimpleGraph.Walk.mem_verts_toSubgraph p).mp h.fst_mem)
      rw [hempty, Set.ncard_empty, if_neg ha]
  have htot : ∑ a, s a = 15 := by
    have hfilter : (Finset.univ.filter (fun a => a ∈ p.support)) = p.support.tail.toFinset := by
      ext a
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, List.mem_toFinset]
      constructor
      · intro ha
        rcases (SimpleGraph.Walk.mem_support_iff p).mp ha with h | h
        · rw [h]
          exact SimpleGraph.Walk.end_mem_tail_support hc.not_nil
        · exact h
      · exact List.mem_of_mem_tail
    have hcard : (Finset.univ.filter (fun a => a ∈ p.support)).card = 15 := by
      rw [hfilter, List.toFinset_card_of_nodup hc.support_nodup, List.length_tail,
        SimpleGraph.Walk.length_support, hlen]
    rw [← hcard, Finset.card_filter]
    apply Finset.sum_congr rfl
    intro a _
    exact hs a
  have mem_of : ∀ a, s a = 1 → a ∈ p.support := by
    intro a h1
    by_contra hn
    rw [hs, if_neg hn] at h1
    omega
  have hcA : s 0 = 1 → s 8 = 1 → 1 ≤ x 0 15 + x 5 6 := by
    intro h0 h8
    obtain ⟨c, d, hcS, hdS, hcd⟩ := cross p {w | w.val < 6} (mem_of 0 h0) (mem_of 8 h8)
      (by show ((0 : Fin 16) : ℕ) < 6; decide) (by show ¬ ((8 : Fin 16) : ℕ) < 6; decide)
    have hadj : p.toSubgraph.Adj c d := SimpleGraph.Walk.adj_toSubgraph_iff_mem_edges.mpr hcd
    have hG := adjB_of hadj.adj_sub
    have hone := hxpos c d hadj
    rcases crossA c d hG hcS hdS with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · omega
    · omega
  have hcB : s 0 = 1 → s 8 = 1 → 1 ≤ x 8 7 + x 13 14 := by
    intro h0 h8
    obtain ⟨c, d, hcS, hdS, hcd⟩ := cross p {w | 8 ≤ w.val ∧ w.val ≤ 13}
      (mem_of 8 h8) (mem_of 0 h0)
      (by show 8 ≤ ((8 : Fin 16) : ℕ) ∧ ((8 : Fin 16) : ℕ) ≤ 13; decide)
      (by show ¬ (8 ≤ ((0 : Fin 16) : ℕ) ∧ ((0 : Fin 16) : ℕ) ≤ 13); decide)
    have hadj : p.toSubgraph.Adj c d := SimpleGraph.Walk.adj_toSubgraph_iff_mem_edges.mpr hcd
    have hG := adjB_of hadj.adj_sub
    have hone := hxpos c d hadj
    rcases crossB c d hG hcS hdS with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · omega
    · omega
  exact core x s hx0 hsym hx1 hs1 hdeg htot hcA hcB

end MO263706Aux

theorem OMA.solution : type_of% @OMA.S_mo_263706.main := by
  refine ⟨16, MO263706Aux.G, MO263706Aux.cubic, MO263706Aux.ham, ?_, MO263706Aux.notBip⟩
  intro v p hc hlen
  exact MO263706Aux.no15 v p hc hlen
