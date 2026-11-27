import FormalConjectures.Wikipedia.PetersenColoringConjecture
import Mathlib

/-!
# A 52-vertex counterexample to the Petersen coloring conjecture

Credit: @AkiRA-COM-FP

Follows the 52-vertex counterexample construction of Goedgebeur, Jooken, Macajova,
Mattiolo, Mazzuoccolo, and Ulyanov (arXiv:2608.10028), assembled from three copies
of the 17-vertex 5-pole F (each built from two copies of the 8-vertex Petersen 4-pole W)
around a central vertex.
-/

namespace OMA.PetersenDisproof

open SimpleGraph

private abbrev Vertex := Fin 52
private abbrev Color := Fin 15
private abbrev Star := Color × Color × Color
private abbrev ColorPair := Color × Color

private def starAt : Fin 10 → Star :=
  ![(0, 4, 10), (0, 1, 11), (1, 2, 12), (2, 3, 13), (3, 4, 14),
    (5, 9, 10), (7, 8, 11), (5, 6, 12), (8, 9, 13), (6, 7, 14)]

private def permutations (s : Star) : List Star :=
  let (a, b, c) := s
  [(a, b, c), (a, c, b), (b, a, c), (b, c, a), (c, a, b), (c, b, a)]

private def stars : List Star := (List.ofFn starAt).flatMap permutations

-- The entries completing a star after one or two colors have been fixed.
private def after : Color → List ColorPair :=
  ![[(4, 10), (10, 4), (1, 11), (11, 1)], [(0, 11), (11, 0), (2, 12), (12, 2)], [(1, 12), (12, 1), (3, 13), (13, 3)],
    [(2, 13), (13, 2), (4, 14), (14, 4)], [(0, 10), (10, 0), (3, 14), (14, 3)], [(9, 10), (10, 9), (6, 12), (12, 6)],
    [(5, 12), (12, 5), (7, 14), (14, 7)], [(8, 11), (11, 8), (6, 14), (14, 6)], [(7, 11), (11, 7), (9, 13), (13, 9)],
    [(5, 10), (10, 5), (8, 13), (13, 8)], [(0, 4), (4, 0), (5, 9), (9, 5)], [(0, 1), (1, 0), (7, 8), (8, 7)],
    [(1, 2), (2, 1), (5, 6), (6, 5)], [(2, 3), (3, 2), (8, 9), (9, 8)], [(3, 4), (4, 3), (6, 7), (7, 6)]]

private theorem after_verified :
    stars.all (fun (a, b, c) => (after a).contains (b, c)) = true := by decide +kernel

private def between (a b : Color) : List Color :=
  (after a).filterMap fun (y, z) => if y == b then some z else none

private theorem after_mem {a b c : Color} (h : (a, b, c) ∈ stars) :
    (b, c) ∈ after a := by
  exact List.contains_iff_mem.mp (List.all_eq_true.mp after_verified _ h)

private theorem between_mem {a b c : Color} (h : (a, b, c) ∈ stars) :
    c ∈ between a b := by
  exact List.mem_filterMap.mpr ⟨(b, c), after_mem h, by simp⟩

private structure WPins where
  i₁ : Color
  o₁ : Color
  i₂ : Color
  o₂ : Color
  deriving BEq, ReflBEq, LawfulBEq

-- The order of visits is 1, 2, 0, 6, 4, 3, 7, 5.
private def wRows : List WPins :=
  stars.flatMap fun (a, b, c) =>
    (after b).flatMap fun (d, e) =>
    (after a).flatMap fun (f, i₁) =>
    (after e).flatMap fun (h, o₂) =>
    (between f h).flatMap fun j =>
    (after d).flatMap fun (k, o₁) =>
    (between j k).flatMap fun l =>
    (between c l).map fun i₂ =>
      ⟨i₁, o₁, i₂, o₂⟩

private theorem w_mem {a b c d e f h j k l i₁ o₁ i₂ o₂ : Color}
    (v1 : (a, b, c) ∈ stars) (v2 : (b, d, e) ∈ stars)
    (v0 : (a, f, i₁) ∈ stars) (v6 : (e, h, o₂) ∈ stars)
    (v4 : (f, h, j) ∈ stars) (v3 : (d, k, o₁) ∈ stars)
    (v7 : (j, k, l) ∈ stars) (v5 : (c, l, i₂) ∈ stars) :
    ⟨i₁, o₁, i₂, o₂⟩ ∈ wRows := by
  apply List.mem_flatMap.mpr
  refine ⟨(a, b, c), v1, ?_⟩
  apply List.mem_flatMap.mpr
  refine ⟨(d, e), after_mem v2, ?_⟩
  apply List.mem_flatMap.mpr
  refine ⟨(f, i₁), after_mem v0, ?_⟩
  apply List.mem_flatMap.mpr
  refine ⟨(h, o₂), after_mem v6, ?_⟩
  apply List.mem_flatMap.mpr
  refine ⟨j, between_mem v4, ?_⟩
  apply List.mem_flatMap.mpr
  refine ⟨(k, o₁), after_mem v3, ?_⟩
  apply List.mem_flatMap.mpr
  refine ⟨l, between_mem v7, ?_⟩
  exact List.mem_map.mpr ⟨i₂, between_mem v5, rfl⟩

-- A paired row repeats its two input colors at the corresponding outputs.
-- The input colors can coincide, be adjacent, or be at distance two.
-- An unpaired row uses the four edges beside a common edge, with two at
-- each endpoint of that edge.
private def wBoundary (i : Color) : List WPins :=
  let opposite := (after i).flatMap fun (o, x) =>
    (after x).filterMap fun (b, c) =>
      if b != i && c != i then some ⟨i, o, b, c⟩ else none
  let paired := [i] ++ (after i).map Prod.fst ++ opposite.map WPins.i₂
  (paired.map fun b => ⟨i, i, b, b⟩) ++ opposite

set_option maxRecDepth 10000 in
private theorem wBoundary_verified :
    wRows.all (fun p => (wBoundary p.i₁).contains p) = true := by
  decide +kernel

private theorem w_boundary {p : WPins} (h : p ∈ wRows) : p ∈ wBoundary p.i₁ :=
  List.contains_iff_mem.mp (List.all_eq_true.mp wBoundary_verified p h)

private structure FRow where
  red : ColorPair
  blue : ColorPair
  green : Color

private def fRows : List FRow :=
  (List.ofFn wBoundary).flatMap fun tops =>
    tops.flatMap fun top =>
      (wBoundary top.o₂).flatMap fun bottom =>
        (between top.o₁ bottom.i₂).map fun green =>
          ⟨(top.i₁, bottom.o₂), (top.i₂, bottom.o₁), green⟩

private theorem f_mem {r₁ r₂ b₁ b₂ g left top bottom : Color}
    (ht : ⟨r₁, top, b₁, left⟩ ∈ wRows)
    (hb : ⟨left, b₂, bottom, r₂⟩ ∈ wRows)
    (hg : (top, bottom, g) ∈ stars) :
    ⟨(r₁, r₂), (b₁, b₂), g⟩ ∈ fRows := by
  apply List.mem_flatMap.mpr
  refine ⟨wBoundary r₁, List.mem_ofFn.mpr ⟨r₁, rfl⟩, ?_⟩
  apply List.mem_flatMap.mpr
  refine ⟨⟨r₁, top, b₁, left⟩, w_boundary ht, ?_⟩
  apply List.mem_flatMap.mpr
  refine ⟨⟨left, b₂, bottom, r₂⟩, w_boundary hb, ?_⟩
  exact List.mem_map.mpr ⟨g, between_mem hg, rfl⟩

private def pairIndex (p : ColorPair) : Nat := 15 * p.1.val + p.2.val

private theorem pairIndex_lt (p : ColorPair) : pairIndex p < 225 := by
  have h₁ := p.1.isLt
  have h₂ := p.2.isLt
  unfold pairIndex
  omega

private def edgeIndex (a b : ColorPair) : Nat := 225 * pairIndex a + pairIndex b

-- A row of this bit matrix represents the possible next ordered color pairs.
private def pairMatrix (src dst : FRow → ColorPair) : List FRow → Nat
  | [] => 0
  | r :: rs => (1 <<< edgeIndex (src r) (dst r)) ||| pairMatrix src dst rs

private def pairRow (matrix : Nat) (p : ColorPair) : Nat :=
  (matrix >>> (225 * pairIndex p)) % (2 ^ 225)

private theorem matrix_bit (src dst : FRow → ColorPair) {rows : List FRow}
    {r : FRow} (hr : r ∈ rows) :
    (pairMatrix src dst rows).testBit (edgeIndex (src r) (dst r)) = true := by
  induction rows with
  | nil => simp at hr
  | cons head tail ih =>
    rcases List.mem_cons.mp hr with rfl | h
    · simp only [pairMatrix, Nat.testBit_or, Nat.shiftLeft_eq, Nat.one_mul,
        Nat.testBit_two_pow_self, Bool.true_or]
    · simp only [pairMatrix, Nat.testBit_or, ih h, Bool.or_true]

private theorem row_bit (src dst : FRow → ColorPair) {rows : List FRow}
    {r : FRow} (hr : r ∈ rows) :
    (pairRow (pairMatrix src dst rows) (src r)).testBit (pairIndex (dst r)) = true := by
  simp only [pairRow, Nat.testBit_mod_two_pow, Nat.testBit_shiftRight,
    decide_eq_true (pairIndex_lt _), Bool.true_and]
  exact matrix_bit src dst hr

private def clash (outgoing incoming : Nat) (row : FRow) : Nat :=
  pairRow outgoing row.blue &&& pairRow incoming row.red

private def triangleFree : Bool :=
  let outgoing := pairMatrix FRow.red FRow.blue fRows
  let incoming := pairMatrix FRow.blue FRow.red fRows
  fRows.all fun row => clash outgoing incoming row == 0

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem triangleFree_verified : triangleFree = true := by decide +kernel

private theorem no_ring {a b c : ColorPair} {g₁ g₂ g₃ : Color}
    (h₁ : ⟨a, b, g₁⟩ ∈ fRows) (h₂ : ⟨b, c, g₂⟩ ∈ fRows)
    (h₃ : ⟨c, a, g₃⟩ ∈ fRows) : False := by
  let out := pairMatrix FRow.red FRow.blue fRows
  let inn := pairMatrix FRow.blue FRow.red fRows
  have test : fRows.all (fun row => clash out inn row == 0) = true := triangleFree_verified
  have hz : clash out inn ⟨a, b, g₁⟩ = 0 :=
    beq_iff_eq.mp (List.all_eq_true.mp test ⟨a, b, g₁⟩ h₁)
  have hb : (pairRow out b).testBit (pairIndex c) = true :=
    row_bit FRow.red FRow.blue (rows := fRows) (r := ⟨b, c, g₂⟩) h₂
  have ha : (pairRow inn a).testBit (pairIndex c) = true :=
    row_bit FRow.blue FRow.red (rows := fRows) (r := ⟨c, a, g₃⟩) h₃
  have hf := congrArg (fun n : Nat => n.testBit (pairIndex c)) hz
  change (pairRow out b &&& pairRow inn a).testBit (pairIndex c) = _ at hf
  rw [Nat.testBit_and, hb, ha] at hf
  simp at hf

private def wEdges : List (Vertex × Vertex) :=
  [(0, 1), (1, 2), (2, 3), (0, 4), (1, 5), (2, 6), (3, 7), (4, 6), (5, 7), (4, 7)]

private def shiftEdges (n : Vertex) (es : List (Vertex × Vertex)) :
    List (Vertex × Vertex) :=
  es.map fun (a, b) => (a + n, b + n)

private def fEdges : List (Vertex × Vertex) :=
  wEdges ++ shiftEdges 8 wEdges ++ [(6, 8), (3, 16), (13, 16)]

private def graphEdges : List (Vertex × Vertex) :=
  fEdges ++ shiftEdges 17 fEdges ++ shiftEdges 34 fEdges ++
    [(16, 51), (33, 51), (50, 51), (5, 17), (11, 31),
      (22, 34), (28, 48), (39, 0), (45, 14)]

-- The adjacency table is checked against the construction above.
private def neighbors : Vertex → List Vertex :=
  ![[1, 4, 39], [0, 2, 5], [1, 3, 6], [2, 7, 16],
    [0, 6, 7], [1, 7, 17], [2, 4, 8], [3, 5, 4],
    [9, 12, 6], [8, 10, 13], [9, 11, 14], [10, 15, 31],
    [8, 14, 15], [9, 15, 16], [10, 12, 45], [11, 13, 12],
    [3, 13, 51], [18, 21, 5], [17, 19, 22], [18, 20, 23],
    [19, 24, 33], [17, 23, 24], [18, 24, 34], [19, 21, 25],
    [20, 22, 21], [26, 29, 23], [25, 27, 30], [26, 28, 31],
    [27, 32, 48], [25, 31, 32], [26, 32, 33], [27, 29, 11],
    [28, 30, 29], [20, 30, 51], [35, 38, 22], [34, 36, 39],
    [35, 37, 40], [36, 41, 50], [34, 40, 41], [35, 41, 0],
    [36, 38, 42], [37, 39, 38], [43, 46, 40], [42, 44, 47],
    [43, 45, 48], [44, 49, 14], [42, 48, 49], [43, 49, 50],
    [44, 46, 28], [45, 47, 46], [37, 47, 51], [16, 33, 50]]

private def neighborsSymmetric (u : Vertex) : Bool :=
  (neighbors u).all fun v => (neighbors v).contains u

private theorem neighbors_symmetric : ∀ u : Vertex, neighborsSymmetric u = true := by
  decide +kernel

private theorem neighbors_loopless : ∀ u : Vertex, u ∉ neighbors u := by
  decide +kernel

private def G52 : SimpleGraph Vertex where
  Adj u v := v ∈ neighbors u
  symm := ⟨fun u _ h =>
    List.contains_iff_mem.mp (List.all_eq_true.mp (neighbors_symmetric u) _ h)⟩
  loopless := ⟨neighbors_loopless⟩

private instance : DecidableRel G52.Adj := fun u v =>
  inferInstanceAs (Decidable (v ∈ neighbors u))

private theorem neighbors_card : ∀ u : Vertex, (neighbors u).toFinset.card = 3 := by
  decide +kernel

private theorem cubic (u : Vertex) : G52.degree u = 3 := by
  have h : G52.neighborFinset u = (neighbors u).toFinset := by
    ext v
    rw [SimpleGraph.mem_neighborFinset, List.mem_toFinset]
    rfl
  exact (congrArg Finset.card h).trans (neighbors_card u)

private def neighborsCovered (u : Vertex) : Bool :=
  (neighbors u).all fun v => graphEdges.contains (u, v) || graphEdges.contains (v, u)

set_option maxRecDepth 10000 in
private theorem neighbors_covered : ∀ u : Vertex, neighborsCovered u = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem edges_in_neighbors :
    graphEdges.all (fun (u, v) => (neighbors u).contains v) = true := by
  decide +kernel

private theorem adjacency_iff_edges (u v : Vertex) :
    G52.Adj u v ↔ (u, v) ∈ graphEdges ∨ (v, u) ∈ graphEdges := by
  constructor
  · intro h
    have h' := List.all_eq_true.mp (neighbors_covered u) v h
    simpa only [Bool.or_eq_true, List.contains_iff_mem] using h'
  · intro h
    rcases h with h | h
    · exact List.contains_iff_mem.mp (List.all_eq_true.mp edges_in_neighbors _ h)
    · exact G52.adj_symm (List.contains_iff_mem.mp (List.all_eq_true.mp edges_in_neighbors _ h))

-- Each entry gives the ordered endpoints of an edge and the internal vertices
-- of a path between them in the graph with that edge deleted.
private abbrev Detour := Vertex × Vertex × List Vertex

private def wDetours : List Detour := [
  (0, 1, [4, 6, 2]),
  (1, 2, [0, 4, 6]),
  (2, 3, [1, 5, 7]),
  (0, 4, [1, 2, 6]),
  (1, 5, [0, 4, 7]),
  (2, 6, [1, 0, 4]),
  (3, 7, [2, 1, 5]),
  (4, 6, [0, 1, 2]),
  (5, 7, [1, 0, 4]),
  (4, 7, [0, 1, 5])]

private def shiftDetours (n : Vertex) (ps : List Detour) : List Detour :=
  ps.map fun (u, v, xs) => (u + n, v + n, xs.map fun x => x + n)

private def fDetours : List Detour :=
  wDetours ++ shiftDetours 8 wDetours ++ [
  (6, 8, [2, 3, 16, 13, 9]),
  (3, 16, [2, 6, 8, 9, 13]),
  (13, 16, [9, 8, 6, 2, 3])]

private def detours : List Detour :=
  fDetours ++ shiftDetours 17 fDetours ++ shiftDetours 34 fDetours ++ [
  (16, 51, [3, 2, 1, 0, 39, 41, 37, 50]),
  (33, 51, [20, 19, 18, 17, 5, 7, 3, 16]),
  (50, 51, [37, 36, 35, 34, 22, 24, 20, 33]),
  (5, 17, [1, 0, 39, 35, 34, 22, 18]),
  (11, 31, [10, 14, 45, 44, 48, 28, 27]),
  (22, 34, [18, 17, 5, 1, 0, 39, 35]),
  (28, 48, [27, 31, 11, 10, 14, 45, 44]),
  (39, 0, [35, 34, 22, 18, 17, 5, 1]),
  (45, 14, [44, 48, 28, 27, 31, 11, 10])]

private def pathTest (e : Sym2 Vertex) (u v : Vertex) : List Vertex → Bool
  | [] => decide ((G52.deleteEdges {e}).Adj u v)
  | x :: xs => decide ((G52.deleteEdges {e}).Adj u x) && pathTest e x v xs

private theorem reaches_of_path {e : Sym2 Vertex} {u v : Vertex} (xs : List Vertex)
    (h : pathTest e u v xs = true) : (G52.deleteEdges {e}).Reachable u v := by
  induction xs generalizing u with
  | nil =>
    exact ⟨.cons (of_decide_eq_true h) .nil⟩
  | cons x xs ih =>
    have h' : decide ((G52.deleteEdges {e}).Adj u x) = true ∧
        pathTest e x v xs = true := by
      simpa only [pathTest, Bool.and_eq_true] using h
    obtain ⟨p⟩ := ih h'.2
    exact ⟨.cons (of_decide_eq_true h'.1) p⟩

private def detourTest (d : Detour) : Bool :=
  pathTest s(d.1, d.2.1) d.1 d.2.1 d.2.2

private theorem detours_cover : detours.map (fun d => (d.1, d.2.1)) = graphEdges := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem detours_verified : detours.all detourTest = true := by decide +kernel

private theorem forward_not_bridge {u v : Vertex} (h : (u, v) ∈ graphEdges) :
    ¬G52.IsBridge s(u, v) := by
  rw [← detours_cover] at h
  obtain ⟨⟨a, b, xs⟩, hm, hab⟩ := List.mem_map.mp h
  change (a, b) = (u, v) at hab
  cases hab
  exact fun hb => isBridge_iff.mp hb
    (reaches_of_path xs (List.all_eq_true.mp detours_verified _ hm))

private theorem bridgeless : G52.IsBridgeless := by
  intro edge
  induction edge using Sym2.inductionOn with
  | _ u v =>
    intro he
    have h : G52.Adj u v := G52.mem_edgeSet.mp he
    rcases (adjacency_iff_edges u v).mp h with h | h
    · exact forward_not_bridge h
    · rw [Sym2.eq_swap]
      exact forward_not_bridge h

private def pVertex : Fin 10 → PetersenVertex :=
  ![⟨{0, 1}, by decide⟩, ⟨{2, 3}, by decide⟩, ⟨{0, 4}, by decide⟩,
    ⟨{1, 2}, by decide⟩, ⟨{3, 4}, by decide⟩, ⟨{2, 4}, by decide⟩,
    ⟨{1, 4}, by decide⟩, ⟨{1, 3}, by decide⟩, ⟨{0, 3}, by decide⟩,
    ⟨{0, 2}, by decide⟩]

private def edgeEnds : Color → Fin 10 × Fin 10 :=
  ![(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (5, 7), (7, 9), (9, 6),
    (6, 8), (8, 5), (0, 5), (1, 6), (2, 7), (3, 8), (4, 9)]

private def pEdge (c : Color) : Sym2 PetersenVertex :=
  s(pVertex (edgeEnds c).1, pVertex (edgeEnds c).2)

private theorem pVertex_surjective : ∀ w : PetersenVertex, ∃ i, pVertex i = w := by
  decide +kernel

private theorem pEdge_injective : Function.Injective pEdge := by
  change ∀ a b : Color, pEdge a = pEdge b → a = b
  decide +kernel

private def starColors (s : Star) : List Color := [s.1, s.2.1, s.2.2]

private theorem p_incidence : ∀ i : Fin 10,
    petersenGraph.incidenceFinset (pVertex i) =
      (starColors (starAt i)).toFinset.image pEdge := by
  decide +kernel

private theorem permutation_mem {a b c : Color} {s : Star}
    (ha : a ∈ starColors s) (hb : b ∈ starColors s) (hc : c ∈ starColors s)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    (a, b, c) ∈ permutations s := by
  rcases s with ⟨x, y, z⟩
  simp only [starColors, List.mem_cons, List.not_mem_nil, or_false] at ha hb hc
  rcases ha with rfl | rfl | rfl <;>
    rcases hb with rfl | rfl | rfl <;>
    rcases hc with rfl | rfl | rfl <;>
    simp_all [permutations]

private abbrev Coloring := Sym2 Vertex → Sym2 PetersenVertex

private noncomputable def paint (φ : Coloring) (u v : Vertex) : Color :=
  Function.invFun pEdge (φ s(u, v))

private theorem paint_comm (φ : Coloring) (u v : Vertex) :
    paint φ u v = paint φ v u :=
  congrArg (fun e => Function.invFun pEdge (φ e)) Sym2.eq_swap

private def ValidNeighbors (v a b c : Vertex) : Prop :=
  G52.Adj v a ∧ G52.Adj v b ∧ G52.Adj v c ∧ a ≠ b ∧ a ≠ c ∧ b ≠ c

private instance (v a b c : Vertex) : Decidable (ValidNeighbors v a b c) := by
  unfold ValidNeighbors
  infer_instance

private theorem vertex_star {φ : Coloring}
    (hφ : PetersenColoringConjecture.IsPetersenColoring G52 φ)
    {v a b c : Vertex} (h : ValidNeighbors v a b c) :
    (paint φ v a, paint φ v b, paint φ v c) ∈ stars := by
  obtain ⟨ha, hb, hc, hab, hac, hbc⟩ := h
  obtain ⟨w, hw, hInj⟩ := hφ v
  obtain ⟨i, rfl⟩ := pVertex_surjective w
  have inc (x : Vertex) (hx : G52.Adj v x) : s(v, x) ∈ G52.incidenceFinset v :=
    (G52.mem_incidenceFinset v _).mpr ((G52.mem_incidenceSet v x).mpr hx)
  have code (x : Vertex) (hx : G52.Adj v x) :
      paint φ v x ∈ starColors (starAt i) ∧ pEdge (paint φ v x) = φ s(v, x) := by
    have he : φ s(v, x) ∈ (G52.incidenceFinset v).image φ :=
      Finset.mem_image.mpr ⟨_, inc x hx, rfl⟩
    rw [hw, p_incidence i] at he
    obtain ⟨d, hd, heq⟩ := Finset.mem_image.mp he
    have hpaint : paint φ v x = d := by
      unfold paint
      rw [← heq]
      exact Function.leftInverse_invFun pEdge_injective d
    exact ⟨hpaint ▸ List.mem_toFinset.mp hd, hpaint ▸ heq⟩
  have differ {x y : Vertex} (hx : G52.Adj v x) (hy : G52.Adj v y) (hne : x ≠ y) :
      paint φ v x ≠ paint φ v y := by
    intro heq
    have hval := (code x hx).2.symm.trans ((congrArg pEdge heq).trans (code y hy).2)
    have hs : s(v, x) = s(v, y) := hInj (inc x hx) (inc y hy) hval
    exact hne (Sym2.congr_left.mp (Sym2.eq_swap.trans (hs.trans Sym2.eq_swap)))
  apply List.mem_flatMap.mpr
  refine ⟨starAt i, List.mem_ofFn.mpr ⟨i, rfl⟩, ?_⟩
  exact permutation_mem (code a ha).1 (code b hb).1 (code c hc).1
    (differ ha hb hab) (differ ha hc hac) (differ hb hc hbc)

private def WNeighborhoods (p : Fin 8 → Vertex) (i₁ o₁ i₂ o₂ : Vertex) : Prop :=
  ValidNeighbors (p 1) (p 0) (p 2) (p 5) ∧
  ValidNeighbors (p 2) (p 1) (p 3) (p 6) ∧
  ValidNeighbors (p 0) (p 1) (p 4) i₁ ∧
  ValidNeighbors (p 6) (p 2) (p 4) o₂ ∧
  ValidNeighbors (p 4) (p 0) (p 6) (p 7) ∧
  ValidNeighbors (p 3) (p 2) (p 7) o₁ ∧
  ValidNeighbors (p 7) (p 4) (p 3) (p 5) ∧
  ValidNeighbors (p 5) (p 1) (p 7) i₂

private instance (p : Fin 8 → Vertex) (i₁ o₁ i₂ o₂ : Vertex) :
    Decidable (WNeighborhoods p i₁ o₁ i₂ o₂) := by
  unfold WNeighborhoods
  infer_instance

private theorem colored_w {φ : Coloring}
    (hφ : PetersenColoringConjecture.IsPetersenColoring G52 φ)
    {p : Fin 8 → Vertex} {i₁ o₁ i₂ o₂ : Vertex}
    (h : WNeighborhoods p i₁ o₁ i₂ o₂) :
    ⟨paint φ (p 0) i₁, paint φ (p 3) o₁, paint φ (p 5) i₂, paint φ (p 6) o₂⟩ ∈
      wRows := by
  obtain ⟨h1, h2, h0, h6, h4, h3, h7, h5⟩ := h
  apply w_mem (vertex_star hφ h1)
  · simpa only [paint_comm φ (p 2) (p 1)] using vertex_star hφ h2
  · simpa only [paint_comm φ (p 0) (p 1)] using vertex_star hφ h0
  · simpa only [paint_comm φ (p 6) (p 2)] using vertex_star hφ h6
  · simpa only [paint_comm φ (p 4) (p 0), paint_comm φ (p 4) (p 6)] using
      vertex_star hφ h4
  · simpa only [paint_comm φ (p 3) (p 2)] using vertex_star hφ h3
  · simpa only [paint_comm φ (p 7) (p 4), paint_comm φ (p 7) (p 3)] using
      vertex_star hφ h7
  · simpa only [paint_comm φ (p 5) (p 1), paint_comm φ (p 5) (p 7)] using
      vertex_star hφ h5

private def upper (k : Fin 3) (i : Fin 8) : Vertex :=
  ⟨17 * k.val + i.val, by omega⟩

private def lower (k : Fin 3) (i : Fin 8) : Vertex :=
  ⟨17 * k.val + 8 + i.val, by omega⟩

private def junction (k : Fin 3) : Vertex :=
  ⟨17 * k.val + 16, by omega⟩

private theorem upper_neighbors : ∀ k : Fin 3,
    WNeighborhoods (upper k) (upper (k + 2) 5) (junction k)
      (upper (k + 1) 0) (lower k 0) := by
  decide +kernel

private theorem lower_neighbors : ∀ k : Fin 3,
    WNeighborhoods (lower k) (upper k 6) (lower (k + 1) 6)
      (junction k) (lower (k + 2) 3) := by
  decide +kernel

private theorem junction_neighbors : ∀ k : Fin 3,
    ValidNeighbors (junction k) (upper k 3) (lower k 5) 51 := by
  decide +kernel

private theorem previous_next : ∀ k : Fin 3, k + 1 + 2 = k := by decide

private noncomputable def red (φ : Coloring) (k : Fin 3) : ColorPair :=
  (paint φ (upper k 0) (upper (k + 2) 5), paint φ (lower k 6) (lower (k + 2) 3))

private theorem colored_f {φ : Coloring}
    (hφ : PetersenColoringConjecture.IsPetersenColoring G52 φ) (k : Fin 3) :
    ⟨red φ k, red φ (k + 1), paint φ (junction k) 51⟩ ∈ fRows := by
  have ht := colored_w hφ (upper_neighbors k)
  have hb := colored_w hφ (lower_neighbors k)
  have hg := vertex_star hφ (junction_neighbors k)
  rw [paint_comm φ (lower k 0) (upper k 6)] at hb
  rw [paint_comm φ (junction k) (upper k 3), paint_comm φ (junction k) (lower k 5)] at hg
  have hf := f_mem ht hb hg
  simpa only [red, previous_next, paint_comm φ (upper k 5) (upper (k + 1) 0),
    paint_comm φ (lower k 3) (lower (k + 1) 6)] using hf

private theorem no_coloring {φ : Coloring} :
    ¬PetersenColoringConjecture.IsPetersenColoring G52 φ := by
  intro h
  exact no_ring (colored_f h 0) (colored_f h 1) (colored_f h 2)

end OMA.PetersenDisproof

open OMA.PetersenDisproof in
theorem OMA.disproof : ¬ (type_of% @PetersenColoringConjecture.petersen_coloring_conjecture) := by
  intro h
  obtain ⟨φ, hφ⟩ := h G52 cubic bridgeless
  exact no_coloring hφ