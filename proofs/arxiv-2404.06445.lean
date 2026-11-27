import OMAStatements.S_arxiv_2404_06445

/-!
# Extremal minimal bipartite matching covered graphs (arXiv 2404.06445), Conjecture 8.9

Source: Mallik, Diwan, Kothari, *Extremal minimal bipartite matching covered graphs*,
arXiv:2404.06445 (v3), Section 8.

Definitions (Section 8 of the source, following Plummer): for a positive integer `k`, a connected
graph of order at least `2k+2` is `k`-extendable if it has a matching of size `k` and each such
matching extends to a perfect matching. A `k`-extendable graph is minimal if deleting any edge
results in a graph that is not `k`-extendable.

Conjecture 8.9 (Main Conjecture). In a minimal `k`-extendable bipartite graph,
`|V_{k+1}| ≥ 2/(2k-1) · (m - n + 2k)`, where `n` is the number of vertices, `m` the number of
edges and `V_{k+1}` the set of vertices of degree `k+1`.
-/

/-! ## Disproof: a 16-vertex counterexample for `k = 3` (our own proof). -/

namespace W2Mdk

open SimpleGraph OMA.S_arxiv_2404_06445

/-- Sides: `0..7` is one colour class (`H_A = {0,1,2}`, `L_A = {3..7}`),
`8..15` the other (`H_B = {8,9,10}`, `L_B = {11..15}`). -/
def side (a : Fin 16) : Bool := a.val < 8

/-- Adjacency: `H_A`–`L_B` complete, `L_A`–`H_B` complete, the matching `i ~ i+8` on
`L_A`–`L_B`, and the single high edge `0 ~ 8`. -/
def adjB (a b : Fin 16) : Bool :=
  (a.val < 3 && 11 ≤ b.val) || (b.val < 3 && 11 ≤ a.val) ||
  (3 ≤ a.val && a.val < 8 && 8 ≤ b.val && b.val < 11) ||
  (3 ≤ b.val && b.val < 8 && 8 ≤ a.val && a.val < 11) ||
  (3 ≤ a.val && a.val < 8 && b.val = a.val + 8) ||
  (3 ≤ b.val && b.val < 8 && a.val = b.val + 8) ||
  (a.val = 0 && b.val = 8) || (a.val = 8 && b.val = 0)

theorem adjB_symm : ∀ a b : Fin 16, adjB a b = true → adjB b a = true := by decide

theorem adjB_irrefl : ∀ a : Fin 16, adjB a a = false := by decide

def G : SimpleGraph (Fin 16) where
  Adj a b := adjB a b = true
  symm := ⟨fun a b h => adjB_symm a b h⟩
  loopless := ⟨fun a h => by
    have h' : adjB a a = true := h
    rw [adjB_irrefl a] at h'
    exact Bool.false_ne_true h'⟩

instance : DecidableRel G.Adj := fun a b => inferInstanceAs (Decidable (adjB a b = true))

/-! ### Subgraphs given by a list of edges -/

def listSub (H : SimpleGraph (Fin 16)) (L : List (Fin 16 × Fin 16))
    (h : ∀ p ∈ L, H.Adj p.1 p.2) : H.Subgraph where
  verts := {v | ∃ p ∈ L, p.1 = v ∨ p.2 = v}
  Adj v w := ∃ p ∈ L, (p.1 = v ∧ p.2 = w) ∨ (p.1 = w ∧ p.2 = v)
  adj_sub := by
    rintro v w ⟨p, hp, (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)⟩
    · exact h p hp
    · exact (h p hp).symm
  edge_vert := by
    rintro v w ⟨p, hp, (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)⟩
    · exact ⟨p, hp, Or.inl rfl⟩
    · exact ⟨p, hp, Or.inr rfl⟩
  symm := ⟨by
    rintro v w ⟨p, hp, h⟩
    exact ⟨p, hp, h.symm⟩⟩

/-- Two listed pairs sharing an endpoint are equal. -/
def DisjL (L : List (Fin 16 × Fin 16)) : Prop :=
  ∀ p ∈ L, ∀ q ∈ L, (p.1 = q.1 ∨ p.1 = q.2 ∨ p.2 = q.1 ∨ p.2 = q.2) → p = q

theorem listSub_isMatching (H : SimpleGraph (Fin 16)) (L : List (Fin 16 × Fin 16))
    (h : ∀ p ∈ L, H.Adj p.1 p.2) (hd : DisjL L) : (listSub H L h).IsMatching := by
  rintro v ⟨p, hp, hv⟩
  have hne : p.1 ≠ p.2 := H.ne_of_adj (h p hp)
  rcases hv with rfl | rfl
  · refine ⟨p.2, ⟨p, hp, Or.inl ⟨rfl, rfl⟩⟩, ?_⟩
    rintro w ⟨q, hq, (⟨h1, rfl⟩ | ⟨rfl, h2⟩)⟩
    · have := hd p hp q hq (Or.inl h1.symm); subst this; rfl
    · have := hd p hp q hq (Or.inr (Or.inl h2.symm)); subst this
      exact absurd h2 hne.symm
  · refine ⟨p.1, ⟨p, hp, Or.inr ⟨rfl, rfl⟩⟩, ?_⟩
    rintro w ⟨q, hq, (⟨h1, rfl⟩ | ⟨rfl, h2⟩)⟩
    · have := hd p hp q hq (Or.inr (Or.inr (Or.inl h1.symm))); subst this
      exact absurd h1 hne
    · have := hd p hp q hq (Or.inr (Or.inr (Or.inr h2.symm))); subst this; rfl

theorem listSub_edgeSet (H : SimpleGraph (Fin 16)) (L : List (Fin 16 × Fin 16))
    (h : ∀ p ∈ L, H.Adj p.1 p.2) :
    (listSub H L h).edgeSet = ↑(L.map (fun p => s(p.1, p.2))).toFinset := by
  ext e
  induction e using Sym2.ind with
  | h v w =>
    simp only [Subgraph.mem_edgeSet, listSub, List.coe_toFinset, List.mem_map, Set.mem_setOf_eq,
      Sym2.eq_iff]

theorem listSub_ncard (H : SimpleGraph (Fin 16)) (L : List (Fin 16 × Fin 16))
    (h : ∀ p ∈ L, H.Adj p.1 p.2) (hd : DisjL L) (hn : L.Nodup) :
    (listSub H L h).edgeSet.ncard = L.length := by
  rw [listSub_edgeSet, Set.ncard_coe_finset, List.toFinset_card_of_nodup, List.length_map]
  refine hn.map_on ?_
  intro p hp q hq hpq
  rcases Sym2.eq_iff.mp hpq with ⟨h1, _⟩ | ⟨h1, _⟩
  · exact hd p hp q hq (Or.inl h1)
  · exact hd p hp q hq (Or.inr (Or.inl h1))

theorem listSub_verts (H : SimpleGraph (Fin 16)) (L : List (Fin 16 × Fin 16))
    (h : ∀ p ∈ L, H.Adj p.1 p.2) (v : Fin 16) :
    v ∈ (listSub H L h).verts ↔ ∃ p ∈ L, p.1 = v ∨ p.2 = v := Iff.rfl

/-! ### Boolean checkers -/

def covers (L : List (Fin 16 × Fin 16)) (v : Fin 16) : Bool :=
  L.any (fun p => p.1 == v || p.2 == v)

theorem covers_iff (L : List (Fin 16 × Fin 16)) (v : Fin 16) :
    covers L v = true ↔ ∃ p ∈ L, p.1 = v ∨ p.2 = v := by
  simp [covers, List.any_eq_true]

def goodList (adj : Fin 16 → Fin 16 → Bool) (L : List (Fin 16 × Fin 16)) : Bool :=
  L.all (fun p => adj p.1 p.2 && L.all (fun q =>
    !(p.1 == q.1 || p.1 == q.2 || p.2 == q.1 || p.2 == q.2) || (p == q)))

theorem goodList_spec (adj : Fin 16 → Fin 16 → Bool) (L : List (Fin 16 × Fin 16))
    (h : goodList adj L = true) : (∀ p ∈ L, adj p.1 p.2 = true) ∧ DisjL L := by
  simp only [goodList, List.all_eq_true, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true',
    beq_iff_eq] at h
  refine ⟨fun p hp => (h p hp).1, ?_⟩
  intro p hp q hq hshare
  rcases (h p hp).2 q hq with h1 | h1
  · simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq] at h1
    tauto
  · exact h1

/-- Backtracking search for a perfect matching between two lists of vertices. -/
def search : List (Fin 16) → List (Fin 16) → Option (List (Fin 16 × Fin 16))
  | [], _ => some []
  | a :: as, bs =>
    (bs.filter (fun b => adjB a b)).findSome?
      (fun b => (search as (bs.erase b)).map (List.cons (a, b)))

/-- The check for one set of removed vertices (given by its indicator `mem`): the search finds a
list of pairs which is a matching of `G` covering exactly the vertices with `mem v = false`. -/
def checkM (mem : Fin 16 → Bool) : Bool :=
  match search ((List.finRange 16).filter (fun a => side a && !mem a))
    ((List.finRange 16).filter (fun a => !side a && !mem a)) with
  | some L => goodList adjB L && (List.finRange 16).all (fun v => covers L v == !mem v)
  | none => false

def Alist : List (Fin 16) := [0, 1, 2, 3, 4, 5, 6, 7]
def Blist : List (Fin 16) := [8, 9, 10, 11, 12, 13, 14, 15]

/-- Kernel check: removing any 3 vertices from each side leaves a graph with a perfect matching. -/
theorem extCheckL : (Alist.sublistsLen 3).all (fun la => (Blist.sublistsLen 3).all
    (fun lb => checkM (fun v => (la ++ lb).contains v))) = true := by
  decide +kernel

theorem checkM_spec (mem : Fin 16 → Bool) (h : checkM mem = true) :
    ∃ L : List (Fin 16 × Fin 16), goodList adjB L = true ∧
      ∀ v, covers L v = true ↔ mem v = false := by
  unfold checkM at h
  split at h
  · rename_i L _
    simp only [Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at h
    refine ⟨L, h.1, fun v => ?_⟩
    rw [h.2 v (List.mem_finRange v)]
    cases mem v <;> simp
  · simp at h

/-! ### Deletion witnesses: for each edge `ab` (keyed with the `side = true` end first), a
3-edge matching `L` of `G - ab`, and sets `S`, `T` with `S` avoiding `L`, every `G - ab`-neighbour
of `S` covered by `L` or in `T`, and `|T| < |S|` (a Hall obstruction). -/

def delTable : List ((Fin 16 × Fin 16) × List (Fin 16 × Fin 16) × List (Fin 16) × List (Fin 16)) := [
  ((0, 8), [(3, 11), (4, 12), (5, 13)], [0, 1, 2], [14, 15]),
  ((0, 11), [(1, 12), (2, 13), (3, 8)], [11], []),
  ((0, 12), [(1, 11), (2, 13), (4, 8)], [12], []),
  ((0, 13), [(1, 11), (2, 12), (5, 8)], [13], []),
  ((0, 14), [(1, 11), (2, 12), (6, 8)], [14], []),
  ((0, 15), [(1, 11), (2, 12), (7, 8)], [15], []),
  ((1, 11), [(0, 8), (2, 12), (3, 9)], [11], []),
  ((1, 12), [(0, 8), (2, 11), (4, 9)], [12], []),
  ((1, 13), [(0, 8), (2, 11), (5, 9)], [13], []),
  ((1, 14), [(0, 8), (2, 11), (6, 9)], [14], []),
  ((1, 15), [(0, 8), (2, 11), (7, 9)], [15], []),
  ((2, 11), [(0, 8), (1, 12), (3, 9)], [11], []),
  ((2, 12), [(0, 8), (1, 11), (4, 9)], [12], []),
  ((2, 13), [(0, 8), (1, 11), (5, 9)], [13], []),
  ((2, 14), [(0, 8), (1, 11), (6, 9)], [14], []),
  ((2, 15), [(0, 8), (1, 11), (7, 9)], [15], []),
  ((3, 8), [(9, 4), (10, 5), (11, 0)], [3], []),
  ((3, 9), [(8, 0), (10, 4), (11, 1)], [3], []),
  ((3, 10), [(8, 0), (9, 4), (11, 1)], [3], []),
  ((3, 11), [(8, 0), (9, 4), (10, 5)], [3], []),
  ((4, 8), [(9, 3), (10, 5), (12, 0)], [4], []),
  ((4, 9), [(8, 0), (10, 3), (12, 1)], [4], []),
  ((4, 10), [(8, 0), (9, 3), (12, 1)], [4], []),
  ((4, 12), [(8, 0), (9, 3), (10, 5)], [4], []),
  ((5, 8), [(9, 3), (10, 4), (13, 0)], [5], []),
  ((5, 9), [(8, 0), (10, 3), (13, 1)], [5], []),
  ((5, 10), [(8, 0), (9, 3), (13, 1)], [5], []),
  ((5, 13), [(8, 0), (9, 3), (10, 4)], [5], []),
  ((6, 8), [(9, 3), (10, 4), (14, 0)], [6], []),
  ((6, 9), [(8, 0), (10, 3), (14, 1)], [6], []),
  ((6, 10), [(8, 0), (9, 3), (14, 1)], [6], []),
  ((6, 14), [(8, 0), (9, 3), (10, 4)], [6], []),
  ((7, 8), [(9, 3), (10, 4), (15, 0)], [7], []),
  ((7, 9), [(8, 0), (10, 3), (15, 1)], [7], []),
  ((7, 10), [(8, 0), (9, 3), (15, 1)], [7], []),
  ((7, 15), [(8, 0), (9, 3), (10, 4)], [7], [])
]


def adjDel (a b x y : Fin 16) : Bool :=
  adjB x y && !((x == a && y == b) || (x == b && y == a))

theorem adjDel_iff (a b x y : Fin 16) :
    adjDel a b x y = true ↔ (G.deleteEdges {s(a, b)}).Adj x y := by
  rw [SimpleGraph.deleteEdges_adj]
  simp only [adjDel, Bool.and_eq_true, Bool.not_eq_true', Bool.or_eq_false_iff,
    Bool.and_eq_false_iff, beq_eq_false_iff_ne, ne_eq, Set.mem_singleton_iff, Sym2.eq_iff]
  change _ ↔ adjB x y = true ∧ _
  tauto

def key (a b : Fin 16) : Fin 16 × Fin 16 := if side a then (a, b) else (b, a)

def delOK (a b : Fin 16) : Bool :=
  match delTable.lookup (key a b) with
  | some (L, S, T) =>
    goodList (adjDel a b) L && L.length == 3 && decide L.Nodup &&
      S.all (fun s => !covers L s) &&
      S.all (fun s => (List.finRange 16).all
        (fun w => !adjDel a b s w || covers L w || T.contains w)) &&
      decide (T.toFinset.card < S.toFinset.card)
  | none => false

/-- Kernel check of all 36 deletion witnesses. -/
theorem delCheck : ∀ a b : Fin 16, adjB a b = true → delOK a b = true := by
  decide +kernel

theorem delOK_spec (a b : Fin 16) (h : delOK a b = true) :
    ∃ (L : List (Fin 16 × Fin 16)) (S T : List (Fin 16)),
      goodList (adjDel a b) L = true ∧ L.length = 3 ∧ L.Nodup ∧
      (∀ s ∈ S, covers L s = false) ∧
      (∀ s ∈ S, ∀ w, adjDel a b s w = true → covers L w = true ∨ w ∈ T) ∧
      T.toFinset.card < S.toFinset.card := by
  unfold delOK at h
  split at h
  · rename_i L S T _
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true,
      Bool.not_eq_true', Bool.or_eq_true, List.contains_iff_mem] at h
    obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
    refine ⟨L, S, T, h1, h2, h3, h4, fun s hs w hw => ?_, h6⟩
    rcases h5 s hs w (List.mem_finRange w) with (h | h) | h
    · simp [hw] at h
    · exact Or.inl h
    · exact Or.inr h
  · simp at h

/-- A Hall obstruction outside a matching `M` prevents extending `M` to a perfect matching. -/
theorem no_ext (H : SimpleGraph (Fin 16)) (M : H.Subgraph) (hM : M.IsMatching)
    (S T : Finset (Fin 16)) (hS : ∀ s ∈ S, s ∉ M.verts)
    (hT : ∀ s ∈ S, ∀ w, H.Adj s w → w ∈ M.verts ∨ w ∈ T) (hlt : T.card < S.card) :
    ¬ ∃ P : H.Subgraph, P.IsPerfectMatching ∧ M ≤ P := by
  rintro ⟨P, hP, hle⟩
  rw [Subgraph.isPerfectMatching_iff] at hP
  choose q hq hq' using hP
  have key : ∀ s ∈ S, q s ∈ T := by
    intro s hs
    rcases hT s hs (q s) (P.adj_sub (hq s)) with h | h
    · exfalso
      obtain ⟨u, hu, -⟩ := hM h
      have h1 : P.Adj (q s) u := hle.2 hu
      have h2 : P.Adj (q s) s := (hq s).symm
      have hus : u = s := (hq' _ _ h1).trans (hq' _ _ h2).symm
      subst hus
      exact hS _ hs (M.edge_vert hu.symm)
    · exact h
  have hle' : S.card ≤ T.card := Finset.card_le_card_of_injOn q (fun s hs => key s hs) (by
    intro s _ s' _ hqq
    have h1 : P.Adj (q s) s := (hq s).symm
    have h2 : P.Adj (q s) s' := by rw [hqq]; exact (hq s').symm
    exact (hq' _ _ h1).trans (hq' _ _ h2).symm)
  omega

theorem not_ext_del (a b : Fin 16) (hab : G.Adj a b) :
    ¬ IsKExtendable (G.deleteEdges {s(a, b)}) 3 := by
  rintro ⟨-, -, -, hext⟩
  obtain ⟨L, S, T, hg, hlen, hnd, hS, hT, hlt⟩ := delOK_spec a b (delCheck a b hab)
  obtain ⟨hadj, hd⟩ := goodList_spec _ L hg
  have hadj' : ∀ p ∈ L, (G.deleteEdges {s(a, b)}).Adj p.1 p.2 :=
    fun p hp => (adjDel_iff a b _ _).mp (hadj p hp)
  have hM := listSub_isMatching _ L hadj' hd
  obtain ⟨P, hP, hle⟩ := hext (listSub _ L hadj') hM (by rw [listSub_ncard _ L hadj' hd hnd, hlen])
  refine no_ext _ (listSub _ L hadj') hM S.toFinset T.toFinset ?_ ?_ hlt ⟨P, hP, hle⟩
  · intro s hs hv
    rw [listSub_verts, ← covers_iff, hS s (List.mem_toFinset.mp hs)] at hv
    exact Bool.false_ne_true hv
  · intro s hs w hw
    rcases hT s (List.mem_toFinset.mp hs) w ((adjDel_iff a b s w).mpr hw) with h | h
    · exact Or.inl ((covers_iff L w).mp h)
    · exact Or.inr (List.mem_toFinset.mpr h)

/-! ### Counting the two colour classes of a matching -/

theorem card_side (H : SimpleGraph (Fin 16)) (c : Fin 16 → Bool)
    (hc : ∀ a b, H.Adj a b → c a ≠ c b) (M : H.Subgraph) (hM : M.IsMatching) :
    {v | v ∈ M.verts ∧ c v = true}.ncard = M.edgeSet.ncard := by
  classical
  refine Set.ncard_congr (fun v hv => s(v, (hM hv.1).choose)) ?_ ?_ ?_
  · intro v hv
    exact Subgraph.mem_edgeSet.mpr (hM hv.1).choose_spec.1
  · intro a b ha hb hab
    rcases Sym2.eq_iff.mp hab with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact h1
    · exfalso
      have hb' := (hM hb.1).choose_spec.1
      have hne := hc _ _ (M.adj_sub hb')
      rw [← h1] at hne
      exact hne (hb.2.trans ha.2.symm)
  · intro e he
    induction e using Sym2.ind with
    | h x y =>
      have hxy : M.Adj x y := Subgraph.mem_edgeSet.mp he
      have hcxy := hc _ _ (M.adj_sub hxy)
      cases hcx : c x
      · have hcy : c y = true := by
          cases hcy : c y
          · rw [hcx, hcy] at hcxy; exact absurd rfl hcxy
          · rfl
        refine ⟨y, ⟨M.edge_vert hxy.symm, hcy⟩, ?_⟩
        have := (hM (M.edge_vert hxy.symm)).choose_spec.2 x hxy.symm
        rw [← this]
        exact Sym2.eq_swap
      · refine ⟨x, ⟨M.edge_vert hxy, hcx⟩, ?_⟩
        have := (hM (M.edge_vert hxy)).choose_spec.2 y hxy
        rw [← this]

theorem side_ne : ∀ a b : Fin 16, adjB a b = true → side a ≠ side b := by decide

theorem hside : ∀ a b, G.Adj a b → side a ≠ side b := fun a b h => side_ne a b h

theorem hside' : ∀ a b, G.Adj a b → (!side a) ≠ (!side b) := by
  intro a b h h'
  exact hside a b h (by simpa using h')

/-! ### `G` is 3-extendable -/

theorem ext3 (M : G.Subgraph) (hM : M.IsMatching) (h3 : M.edgeSet.ncard = 3) :
    ∃ P : G.Subgraph, P.IsPerfectMatching ∧ M ≤ P := by
  classical
  have hAm : ∀ v : Fin 16, v ∈ Alist ↔ side v = true := by decide
  have hBm : ∀ v : Fin 16, v ∈ Blist ↔ side v = false := by decide
  set la := Alist.filter (fun v => decide (v ∈ M.verts)) with hla_def
  set lb := Blist.filter (fun v => decide (v ∈ M.verts)) with hlb_def
  have hla : la ∈ Alist.sublistsLen 3 := by
    rw [List.mem_sublistsLen]
    refine ⟨List.filter_sublist, ?_⟩
    have hnd : la.Nodup := List.Nodup.filter _ (by decide)
    rw [← List.toFinset_card_of_nodup hnd, ← Set.ncard_coe_finset, ← h3,
      ← card_side G side hside M hM]
    congr 1
    ext v
    simp [la, hAm, and_comm]
  have hlb : lb ∈ Blist.sublistsLen 3 := by
    rw [List.mem_sublistsLen]
    refine ⟨List.filter_sublist, ?_⟩
    have hnd : lb.Nodup := List.Nodup.filter _ (by decide)
    rw [← List.toFinset_card_of_nodup hnd, ← Set.ncard_coe_finset, ← h3,
      ← card_side G (fun a => !side a) hside' M hM]
    congr 1
    ext v
    simp [lb, hBm, and_comm]
  have hmem : (fun v => (la ++ lb).contains v) = (fun v => decide (v ∈ M.verts)) := by
    funext v
    rw [Bool.eq_iff_iff]
    simp only [List.contains_iff_mem, List.mem_append, List.mem_filter, hAm, hBm, la, lb,
      decide_eq_true_eq]
    cases side v <;> simp
  have hc : checkM (fun v => (la ++ lb).contains v) = true :=
    List.all_eq_true.mp (List.all_eq_true.mp extCheckL la hla) lb hlb
  rw [hmem] at hc
  obtain ⟨L, hg, hcov⟩ := checkM_spec _ hc
  obtain ⟨hadj, hd⟩ := goodList_spec adjB L hg
  have hadjG : ∀ p ∈ L, G.Adj p.1 p.2 := hadj
  have hN := listSub_isMatching G L hadjG hd
  have hNv : ∀ v, v ∈ (listSub G L hadjG).verts ↔ v ∉ M.verts := by
    intro v
    rw [listSub_verts, ← covers_iff, hcov]
    simp
  refine ⟨M ⊔ listSub G L hadjG, ⟨hM.sup hN ?_, ?_⟩, le_sup_left⟩
  · rw [hM.support_eq_verts, hN.support_eq_verts]
    exact Set.disjoint_left.mpr fun v h1 h2 => (hNv v).mp h2 h1
  · intro v
    rw [Subgraph.verts_sup, Set.mem_union]
    by_cases hv : v ∈ M.verts
    · exact Or.inl hv
    · exact Or.inr ((hNv v).mpr hv)

/-! ### Connectivity, bipartiteness, counts -/

theorem reach (a b : Fin 16) (h : adjB a b = true := by decide) : G.Reachable a b :=
  SimpleGraph.Adj.reachable (G := G) h

theorem connected : G.Connected := by
  rw [connected_iff_exists_forall_reachable]
  refine ⟨0, fun v => ?_⟩
  fin_cases v
  all_goals first
    | exact SimpleGraph.Reachable.refl _
    | exact reach 0 _
    | exact (reach 0 8).trans (reach 8 _)
    | exact ((reach 0 8).trans (reach 8 3)).trans (reach 3 _)
    | exact (reach 0 11).trans (reach 11 _)

theorem bipartite : G.IsBipartite := by
  refine ⟨SimpleGraph.Coloring.mk (fun v => if side v then (0 : Fin 2) else 1) ?_⟩
  intro v w h
  have key : ∀ v w : Fin 16, adjB v w = true →
      (if side v then (0 : Fin 2) else 1) ≠ (if side w then (0 : Fin 2) else 1) := by decide
  exact key v w h

theorem match3 : ∃ M : G.Subgraph, M.IsMatching ∧ M.edgeSet.ncard = 3 := by
  have h : ∀ p ∈ ([(3, 11), (4, 12), (5, 13)] : List (Fin 16 × Fin 16)), G.Adj p.1 p.2 := by
    decide +kernel
  have hd : DisjL ([(3, 11), (4, 12), (5, 13)] : List (Fin 16 × Fin 16)) := by
    unfold DisjL; decide +kernel
  exact ⟨listSub G _ h, listSub_isMatching G _ h hd, by rw [listSub_ncard G _ h hd (by decide +kernel)]; rfl⟩

theorem kext : IsKExtendable G 3 :=
  ⟨connected, by simp [Nat.card_eq_fintype_card], match3, ext3⟩

theorem minimal : IsMinimalKExtendable G 3 := by
  refine ⟨kext, fun e he => ?_⟩
  induction e using Sym2.ind with
  | h a b => exact not_ext_del a b he

theorem card_edges : G.edgeSet.ncard = 36 := by
  rw [← SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset]
  have h := G.sum_degrees_eq_twice_card_edges
  have h72 : ∑ v, G.degree v = 72 := by
    simp only [← SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.neighborFinset_eq_filter]
    decide +kernel
  omega

theorem ncard_nbr (v : Fin 16) :
    (G.neighborSet v).ncard = (Finset.univ.filter (fun w => adjB v w = true)).card := by
  rw [← Set.ncard_coe_finset]
  congr 1
  ext w
  simp [SimpleGraph.mem_neighborSet, G]

theorem card_deg4 : {v : Fin 16 | (G.neighborSet v).ncard = 3 + 1}.ncard = 10 := by
  have : {v : Fin 16 | (G.neighborSet v).ncard = 3 + 1} =
      ↑(Finset.univ.filter (fun v : Fin 16 =>
        (Finset.univ.filter (fun w => adjB v w = true)).card = 4)) := by
    ext v
    simp [ncard_nbr]
  rw [this, Set.ncard_coe_finset]
  decide +kernel

/-- Conjecture 8.9 is false: for `k = 3` the 16-vertex graph above is minimal 3-extendable and
bipartite with 36 edges but only 10 vertices of degree 4, while the bound asks for `52/5`. -/
theorem disproof : ¬ (type_of% @OMA.S_arxiv_2404_06445.main) := by
  intro h
  have := h 3 (by norm_num) (Fin 16) G bipartite minimal
  rw [card_edges, card_deg4] at this
  norm_num at this

end W2Mdk

theorem OMA.disproof : ¬ (type_of% @OMA.S_arxiv_2404_06445.main) :=
  W2Mdk.disproof