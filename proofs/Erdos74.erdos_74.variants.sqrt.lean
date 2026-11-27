import FormalConjectures.ErdosProblems.«74»

/-!
# Disproof of Erdős Problem 74 (sqrt variant)

We prove that there is no graph `G` of infinite chromatic number whose finite `n`-vertex
subgraphs can all be made bipartite by deleting at most `√n` edges.

The proof is completely self-contained and elementary, working for arbitrary (possibly infinite,
unbounded-degree) graphs via:
1. Short odd-walk transversals `T_L` of size `≤ L^2`,
2. A zero-skip-edge shell filtration `C_j = B_G(C_{j-1}, 1) ∪ T_j`, `A_j = C_j \ C_{j-1}`,
3. The No-Internal-Intersection Lemma and Quotient-Graph Odd-Girth Lemma on stepping paths,
4. Elementary algebraic ball-carving (zero logarithms or external black boxes).
-/

-- Problem: Erdős Problem 74 — sqrt
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/74.lean:142 (declaration Erdos74.erdos_74.variants.sqrt)
-- Credit: @preternatural-tocsin
-- Prove EXACTLY the negation of this target. No sorry, no axiom, no native_decide.

open Erdos74 SimpleGraph

namespace OMA.DisproofErdos74Sqrt

universe u

section WalkAndColoringHelpers

variable {V : Type u} {G : SimpleGraph V}

lemma induce_adj {s : Set V} {a b : {x // x ∈ s}} (h : (G.induce s).Adj a b) : G.Adj a.1 b.1 := h

def walkInduceMap {s : Set V} :
    ∀ {a b : {x // x ∈ s}}, (G.induce s).Walk a b → G.Walk a.1 b.1
  | _, _, .nil => .nil
  | _, _, .cons h p => .cons (induce_adj h) (walkInduceMap p)

lemma walkInduceMap_length {s : Set V} :
    ∀ {a b : {x // x ∈ s}} (p : (G.induce s).Walk a b), (walkInduceMap p).length = p.length
  | _, _, .nil => rfl
  | _, _, .cons _ p => by rw [walkInduceMap, Walk.length_cons, Walk.length_cons, walkInduceMap_length p]

lemma walkInduceMap_support_mem {s : Set V} :
    ∀ {a b : {x // x ∈ s}} (p : (G.induce s).Walk a b), ∀ z ∈ (walkInduceMap p).support, z ∈ s
  | a, _, .nil, z, hz => by
    simp only [walkInduceMap, Walk.support_nil, List.mem_singleton] at hz
    exact hz ▸ a.2
  | a, _, .cons _ q, z, hz => by
    rw [walkInduceMap, Walk.support_cons, List.mem_cons] at hz
    exact hz.elim (fun h => h ▸ a.2) (walkInduceMap_support_mem q z)

lemma mem_support_append_or {a b c : V} {p : G.Walk a b} {q : G.Walk b c} {x : V}
    (hx : x ∈ (p.append q).support) : x ∈ p.support ∨ x ∈ q.support := by
  induction p with
  | nil => exact Or.inr hx
  | cons _ p ih =>
    simp only [Walk.cons_append, Walk.support_cons, List.mem_cons] at hx ⊢
    rcases hx with rfl | h
    · exact Or.inl (Or.inl rfl)
    · exact (ih h).imp_left Or.inr

lemma mem_support_of_reverse {a b : V} {p : G.Walk a b} {x : V}
    (hx : x ∈ p.reverse.support) : x ∈ p.support := by
  rw [Walk.support_reverse, List.mem_reverse] at hx
  exact hx

lemma getVert_cons_succ_symm {a b c : V} (h : G.Adj a b) (q : G.Walk b c) (t : ℕ) :
    q.getVert t = (Walk.cons h q).getVert (t + 1) := by
  simp [Walk.getVert_cons_succ]

def walkDrop : ∀ {a b : V} (p : G.Walk a b) (t : ℕ), t ≤ p.length → G.Walk (p.getVert t) b
  | _, _, p, 0, _ => p.copy (Walk.getVert_zero p).symm rfl
  | _, _, .nil, _ + 1, ht => False.elim (by simp at ht)
  | _, _, .cons h q, t + 1, ht =>
    (walkDrop q t (by simp at ht; omega)).copy (getVert_cons_succ_symm h q t) rfl

lemma walkDrop_length : ∀ {a b : V} (p : G.Walk a b) (t : ℕ) (ht : t ≤ p.length),
    (walkDrop p t ht).length = p.length - t
  | _, _, p, 0, _ => by simp [walkDrop]
  | _, _, .nil, _ + 1, ht => False.elim (by simp at ht)
  | _, _, .cons _ q, t + 1, ht => by
    unfold walkDrop
    rw [Walk.length_copy, Walk.length_cons, Nat.add_sub_add_right]
    exact walkDrop_length q t (by simp at ht; omega)

lemma walkDrop_getVert : ∀ {a b : V} (p : G.Walk a b) (t : ℕ) (ht : t ≤ p.length) (s : ℕ),
    (walkDrop p t ht).getVert s = p.getVert (t + s)
  | _, _, p, 0, _, s => by simp [walkDrop]
  | _, _, .nil, _ + 1, ht, _ => False.elim (by simp at ht)
  | _, _, .cons _ q, t + 1, ht, s => by
    simp only [walkDrop, Nat.succ_add, Walk.getVert_cons_succ]
    exact walkDrop_getVert q t (by simp at ht; omega) s

def walkTake : ∀ {a b : V} (p : G.Walk a b) (t : ℕ), t ≤ p.length → G.Walk a (p.getVert t)
  | _, _, p, 0, _ => Walk.nil.copy rfl (Walk.getVert_zero p).symm
  | _, _, .nil, _ + 1, ht => False.elim (by simp at ht)
  | _, _, .cons h q, t + 1, ht =>
    (Walk.cons h (walkTake q t (by simp at ht; omega))).copy rfl (getVert_cons_succ_symm h q t)

lemma walkTake_length : ∀ {a b : V} (p : G.Walk a b) (t : ℕ) (ht : t ≤ p.length),
    (walkTake p t ht).length = t
  | _, _, _, 0, _ => by simp [walkTake]
  | _, _, .nil, _ + 1, ht => False.elim (by simp at ht)
  | _, _, .cons _ q, t + 1, ht => by
    unfold walkTake
    rw [Walk.length_copy, Walk.length_cons, walkTake_length q t (by simp at ht; omega)]

lemma mem_support_iff_exists_getVert {a b : V} (p : G.Walk a b) (x : V) :
    x ∈ p.support ↔ ∃ t ≤ p.length, p.getVert t = x := by
  induction p with
  | nil =>
    simp only [Walk.support_nil, List.mem_singleton, Walk.length_nil, Nat.le_zero, exists_eq_left,
      Walk.getVert_zero]
    exact eq_comm
  | cons h q ih =>
    simp only [Walk.support_cons, List.mem_cons, Walk.length_cons, ih]
    constructor
    · rintro (rfl | ⟨t, ht, hqt⟩)
      · exact ⟨0, Nat.zero_le _, rfl⟩
      · exact ⟨t + 1, Nat.succ_le_succ ht, hqt⟩
    · rintro ⟨t, ht, hpt⟩
      cases t with
      | zero => exact Or.inl hpt.symm
      | succ k => exact Or.inr ⟨k, Nat.le_of_succ_le_succ ht, hpt⟩

lemma mem_support_tail_iff {a b : V} (p : G.Walk a b) (x : V) :
    x ∈ p.support.tail ↔ ∃ t, 1 ≤ t ∧ t ≤ p.length ∧ p.getVert t = x := by
  cases p with
  | nil => simp
  | cons h q =>
    simp only [Walk.support_cons, List.tail_cons, mem_support_iff_exists_getVert, Walk.length_cons]
    constructor
    · rintro ⟨t, ht, hqt⟩
      exact ⟨t + 1, by omega, Nat.succ_le_succ ht, hqt⟩
    · rintro ⟨t, h1, hle, hpt⟩
      cases t with
      | zero => omega
      | succ k => exact ⟨k, Nat.le_of_succ_le_succ hle, hpt⟩

lemma coloring_two_walk_parity (c : G.Coloring (Fin 2)) :
    ∀ {x y : V} (p : G.Walk x y), (c y : ℕ) % 2 = ((c x : ℕ) + p.length) % 2
  | _, _, .nil => by simp
  | x, z, .cons (v := y) hxy q => by
    have ih := coloring_two_walk_parity c q
    have hne : c x ≠ c y := c.valid hxy
    have hcx : (c x : ℕ) < 2 := (c x).isLt
    have hcy : (c y : ℕ) < 2 := (c y).isLt
    have hne' : (c x : ℕ) ≠ (c y : ℕ) := fun h => hne (Fin.ext h)
    simp only [Walk.length_cons]
    omega

lemma not_colorable_two_of_odd_walk {v : V} (p : G.Walk v v) (hodd : Odd p.length) :
    ¬ G.Colorable 2 := by
  rintro ⟨c⟩
  have h := coloring_two_walk_parity c p
  obtain ⟨k, hk⟩ := hodd
  omega

lemma colorable_two_of_no_odd_walk (hno : ∀ v : V, ∀ p : G.Walk v v, ¬ Odd p.length) :
    G.Colorable 2 := by
  classical
  let rep : G.ConnectedComponent → V := fun c => Classical.choose c.exists_rep
  have hrep : ∀ c, G.connectedComponentMk (rep c) = c :=
    fun c => Classical.choose_spec c.exists_rep
  have hreach : ∀ v : V, G.Reachable (rep (G.connectedComponentMk v)) v := by
    intro v
    exact ConnectedComponent.exact (hrep (G.connectedComponentMk v))
  let walkTo : ∀ v : V, G.Walk (rep (G.connectedComponentMk v)) v :=
    fun v => Classical.choice (hreach v)
  refine ⟨Coloring.mk (fun v => ⟨(walkTo v).length % 2, Nat.mod_lt _ (by norm_num)⟩) ?_⟩
  intro x y hxy hEq
  have hcc : G.connectedComponentMk x = G.connectedComponentMk y :=
    ConnectedComponent.sound (Adj.reachable hxy)
  have hEq' : (walkTo x).length % 2 = (walkTo y).length % 2 := congrArg Fin.val hEq
  let py : G.Walk (rep (G.connectedComponentMk x)) y :=
    (walkTo y).copy (congrArg rep hcc.symm) rfl
  have hpy_len : py.length = (walkTo y).length := Walk.length_copy _ _ _
  let closed : G.Walk (rep (G.connectedComponentMk x)) (rep (G.connectedComponentMk x)) :=
    ((walkTo x).append (.cons hxy .nil)).append py.reverse
  have hlen : closed.length = (walkTo x).length + 1 + (walkTo y).length := by
    simp [closed, Walk.length_append, Walk.length_reverse, hpy_len]
  have hodd : Odd closed.length := by
    rw [hlen]
    refine ⟨(walkTo x).length / 2 + (walkTo y).length / 2 + (walkTo x).length % 2, ?_⟩
    omega
  exact hno _ closed hodd

lemma walk_support_toFinset_card_le [DecidableEq V] {v : V} (p : G.Walk v v) (hlen : 1 ≤ p.length) :
    p.support.toFinset.card ≤ p.length := by
  cases p with
  | nil => simp at hlen
  | cons h q =>
    have hv : v ∈ q.support := Walk.end_mem_support q
    have hset : (Walk.cons h q).support.toFinset = q.support.toFinset := by
      ext x
      simp only [Walk.support_cons, List.mem_toFinset, List.mem_cons]
      exact ⟨fun hx => hx.elim (fun hxv => hxv ▸ hv) id, fun hx => Or.inr hx⟩
    rw [hset]
    calc q.support.toFinset.card ≤ q.support.length := List.toFinset_card_le _
      _ = q.length + 1 := Walk.length_support q
      _ = (Walk.cons h q).length := rfl

lemma colorable_union_sets {s t : Set V} {a b : ℕ}
    (hs : (G.induce s).Colorable a) (ht : (G.induce t).Colorable b) :
    (G.induce (s ∪ t)).Colorable (a + b) := by
  classical
  obtain ⟨cs⟩ := hs
  obtain ⟨ct⟩ := ht
  refine ⟨Coloring.mk (fun x =>
    if hx : x.1 ∈ s then
      ⟨(cs ⟨x.1, hx⟩ : ℕ), Nat.lt_of_lt_of_le (cs ⟨x.1, hx⟩).isLt (Nat.le_add_right a b)⟩
    else
      ⟨a + (ct ⟨x.1, x.2.resolve_left hx⟩ : ℕ), Nat.add_lt_add_left (ct _).isLt a⟩) ?_⟩
  intro x y hxy
  by_cases hx : x.1 ∈ s <;> by_cases hy : y.1 ∈ s
  · simp only [hx, hy, ↓reduceDIte, ne_eq, Fin.mk.injEq]
    have hvalid := cs.valid (show (G.induce s).Adj ⟨x.1, hx⟩ ⟨y.1, hy⟩ from hxy)
    exact fun h => hvalid (Fin.ext h)
  · simp only [hx, hy, ↓reduceDIte, ne_eq, Fin.mk.injEq]
    have hlt := (cs ⟨x.1, hx⟩).isLt
    omega
  · simp only [hx, hy, ↓reduceDIte, ne_eq, Fin.mk.injEq]
    have hlt := (cs ⟨y.1, hy⟩).isLt
    omega
  · simp only [hx, hy, ↓reduceDIte, ne_eq, Fin.mk.injEq]
    have hvalid := ct.valid
      (show (G.induce t).Adj ⟨x.1, x.2.resolve_left hx⟩ ⟨y.1, y.2.resolve_left hy⟩ from hxy)
    intro h
    exact hvalid (Fin.ext (by omega))

lemma colorable_of_subset {s t : Set V} {k : ℕ} (hst : s ⊆ t)
    (ht : (G.induce t).Colorable k) : (G.induce s).Colorable k := by
  obtain ⟨c⟩ := ht
  exact ⟨Coloring.mk (fun x => c ⟨x.1, hst x.2⟩) (fun h => c.valid h)⟩

lemma colorable_of_finset_card (S : Finset V) :
    (G.induce (S : Set V)).Colorable S.card := by
  classical
  let e : {x // x ∈ (S : Set V)} ≃ Fin S.card :=
    (Equiv.subtypeEquivRight (fun x => Finset.mem_coe)).trans (Fintype.equivFinOfCardEq (Fintype.card_coe S))
  exact ⟨Coloring.mk (fun x => e x) (fun hxy hEq => (G.induce (S : Set V)).ne_of_adj hxy (e.injective hEq))⟩

lemma colorable_disjoint_union_family {ι : Type*} (P : ι → Set V) {k : ℕ}
    (hcol : ∀ i, (G.induce (P i)).Colorable k)
    (hno : ∀ i j, i ≠ j → ∀ x ∈ P i, ∀ y ∈ P j, ¬ G.Adj x y) :
    (G.induce (⋃ i, P i)).Colorable k := by
  classical
  let col : ∀ i, (G.induce (P i)).Coloring (Fin k) := fun i => Classical.choice (hcol i)
  let idx : ∀ x : {v // v ∈ ⋃ i, P i}, ι := fun x => Classical.choose (Set.mem_iUnion.mp x.2)
  have hidx : ∀ x : {v // v ∈ ⋃ i, P i}, x.1 ∈ P (idx x) :=
    fun x => Classical.choose_spec (Set.mem_iUnion.mp x.2)
  have hcast : ∀ {a b : ι} (h : a = b) (v : V) (hva : v ∈ P a) (hvb : v ∈ P b),
      col a ⟨v, hva⟩ = col b ⟨v, hvb⟩ := by
    rintro a _ rfl _ _ _
    rfl
  refine ⟨Coloring.mk (fun x => col (idx x) ⟨x.1, hidx x⟩) ?_⟩
  intro x y hxy
  have heq : idx x = idx y := by
    by_contra hne
    exact hno (idx x) (idx y) hne x.1 (hidx x) y.1 (hidx y) hxy
  have hy' : y.1 ∈ P (idx x) := heq ▸ hidx y
  have hvalid := (col (idx x)).valid (show (G.induce (P (idx x))).Adj ⟨x.1, hidx x⟩ ⟨y.1, hy'⟩ from hxy)
  rw [hcast heq.symm y.1 (hidx y) hy']
  exact hvalid

lemma colorable_biUnion_nat_parity (P : ℕ → Set V) {k : ℕ}
    (hcol : ∀ i, (G.induce (P i)).Colorable k)
    (hno : ∀ i j, i + 2 ≤ j → ∀ x ∈ P i, ∀ y ∈ P j, ¬ G.Adj x y) :
    (G.induce (⋃ i, P i)).Colorable (k + k) := by
  have heq : (⋃ i, P i) = (⋃ m : ℕ, P (2 * m)) ∪ (⋃ m : ℕ, P (2 * m + 1)) := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_union]
    constructor
    · rintro ⟨i, hi⟩
      rcases Nat.even_or_odd i with ⟨m, rfl⟩ | ⟨m, rfl⟩
      · exact Or.inl ⟨m, by simpa [two_mul] using hi⟩
      · exact Or.inr ⟨m, hi⟩
    · rintro (⟨m, hm⟩ | ⟨m, hm⟩)
      · exact ⟨2 * m, hm⟩
      · exact ⟨2 * m + 1, hm⟩
  rw [heq]
  apply colorable_union_sets
  · apply colorable_disjoint_union_family (fun m => P (2 * m)) (fun m => hcol (2 * m))
    intro a b hab x hx y hy hxy
    rcases lt_or_gt_of_ne hab with hlt | hgt
    · exact hno (2 * a) (2 * b) (by omega) x hx y hy hxy
    · exact hno (2 * b) (2 * a) (by omega) y hy x hx hxy.symm
  · apply colorable_disjoint_union_family (fun m => P (2 * m + 1)) (fun m => hcol (2 * m + 1))
    intro a b hab x hx y hy hxy
    rcases lt_or_gt_of_ne hab with hlt | hgt
    · exact hno (2 * a + 1) (2 * b + 1) (by omega) x hx y hy hxy
    · exact hno (2 * b + 1) (2 * a + 1) (by omega) y hy x hx hxy.symm

end WalkAndColoringHelpers

section BridgeAndLemmaA

variable {V : Type u} {G : SimpleGraph V}

lemma walk_lift_to_deleteEdges {A : G.Subgraph} {E : Set (Sym2 V)}
    (hA_ind : ∀ u v, u ∈ A.verts → v ∈ A.verts → G.Adj u v → A.Adj u v) :
    ∀ {x y : V} (p : G.Walk x y) (hx : x ∈ A.verts) (hy : y ∈ A.verts),
      (∀ z ∈ p.support, z ∈ A.verts) →
      (∀ e ∈ p.edges, e ∉ E) →
      ∃ q : (A.deleteEdges E).coe.Walk ⟨x, hx⟩ ⟨y, hy⟩, q.length = p.length
  | x, _, .nil, hx, _, _, _ => ⟨.nil, rfl⟩
  | x, z, .cons (v := y) hxy p, hx, hz, hsupp, hedge => by
    have hy : y ∈ A.verts := hsupp y (by simp)
    have hsupp' : ∀ w ∈ p.support, w ∈ A.verts :=
      fun w hw => hsupp w (by simp [hw])
    have hedge' : ∀ e ∈ p.edges, e ∉ E :=
      fun e he => hedge e (by simp [he])
    obtain ⟨q, hqlen⟩ := walk_lift_to_deleteEdges hA_ind p hy hz hsupp' hedge'
    have hnotE : s(x, y) ∉ E := hedge s(x, y) (by simp)
    have hadj : (A.deleteEdges E).coe.Adj ⟨x, hx⟩ ⟨y, hy⟩ := by
      change (A.deleteEdges E).Adj x y
      exact ⟨hA_ind x y hx hy hxy, hnotE⟩
    exact ⟨.cons hadj q, by rw [Walk.length_cons, Walk.length_cons, hqlen]⟩

lemma disjoint_odd_walks_sq_le
    (hG : ∀ n : ℕ, (Erdos74.SimpleGraph.maxSubgraphEdgeDistToBipartite G n : ℝ) ≤ (n : ℝ).sqrt)
    (S : Finset V) {t : ℕ} (w : Fin t → Σ v : V, G.Walk v v)
    (hodd : ∀ i, Odd (w i).2.length)
    (hsupp : ∀ i, ∀ z ∈ (w i).2.support, z ∈ S)
    (hdisj : ∀ i j, i ≠ j → ∀ e, e ∈ (w i).2.edges → e ∉ (w j).2.edges) :
    t ^ 2 ≤ S.card := by
  classical
  let A : G.Subgraph := (⊤ : G.Subgraph).induce (S : Set V)
  have hAverts : A.verts = (S : Set V) := rfl
  have hAfin : A.verts.Finite := S.finite_toSet
  have hAncard : A.verts.ncard = S.card := by
    rw [hAverts, Set.ncard_coe_finset]
  have hAind : ∀ x y, x ∈ A.verts → y ∈ A.verts → G.Adj x y → A.Adj x y :=
    fun x y hx hy hxy => ⟨hx, hy, hxy⟩
  have hmem_inf :
      Erdos74.SimpleGraph.minEdgeDistToBipartite A ∈ Erdos74.SimpleGraph.edgeDistancesToBipartite A :=
    Nat.sInf_mem (Erdos74.SimpleGraph.edgeDistancesToBipartite_nonempty A)
  obtain ⟨E, hEsub, hEbip, hEcard⟩ := hmem_inf
  have hAedge_fin : A.edgeSet.Finite := by
    have hsub : A.edgeSet ⊆ (fun p : V × V => s(p.1, p.2)) '' ((S : Set V) ×ˢ (S : Set V)) := by
      intro e he
      induction e using Sym2.ind with
      | _ x y =>
        have hadj : A.Adj x y := he
        exact ⟨(x, y), ⟨hadj.1, hadj.2.1⟩, rfl⟩
    exact ((S.finite_toSet.prod S.finite_toSet).image _).subset hsub
  have hEfin : E.Finite := hAedge_fin.subset hEsub
  have hhit : ∀ i : Fin t, ∃ e ∈ E, e ∈ (w i).2.edges := by
    intro i
    by_contra hno
    push Not at hno
    have hvi : (w i).1 ∈ A.verts := hsupp i (w i).1 (Walk.start_mem_support (w i).2)
    obtain ⟨q, hqlen⟩ := walk_lift_to_deleteEdges hAind (w i).2 hvi hvi (hsupp i)
      (fun e he hE => hno e hE he)
    have hqodd : Odd q.length := hqlen ▸ hodd i
    exact not_colorable_two_of_odd_walk q hqodd hEbip
  let pick : Fin t → Sym2 V := fun i => Classical.choose (hhit i)
  have hpickE : ∀ i, pick i ∈ E := fun i => (Classical.choose_spec (hhit i)).1
  have hpickW : ∀ i, pick i ∈ (w i).2.edges := fun i => (Classical.choose_spec (hhit i)).2
  have hinj : Function.Injective pick := by
    intro i j hij
    by_contra hne
    have h1 := hpickW i
    rw [hij] at h1
    exact hdisj j i (Ne.symm hne) (pick j) (hpickW j) h1
  have ht_le_E : t ≤ E.ncard := by
    have hsub : Set.range pick ⊆ E := by
      rintro e ⟨i, rfl⟩
      exact hpickE i
    have h1 : (Set.range pick).ncard ≤ E.ncard := Set.ncard_le_ncard hsub hEfin
    have h2 : (Set.range pick).ncard = t := by
      rw [Set.ncard_range_of_injective hinj, Nat.card_eq_fintype_card, Fintype.card_fin]
    omega
  have hmin_le_max :
      Erdos74.SimpleGraph.minEdgeDistToBipartite A ≤
        Erdos74.SimpleGraph.maxSubgraphEdgeDistToBipartite G S.card := by
    apply le_csSup (Erdos74.SimpleGraph.subgraphEdgeDistsToBipartite_bddAbove G S.card)
    exact ⟨A, hAncard, hAfin, rfl⟩
  have ht_le_max : t ≤ Erdos74.SimpleGraph.maxSubgraphEdgeDistToBipartite G S.card := by
    omega
  have ht_real : (t : ℝ) ≤ (S.card : ℝ).sqrt :=
    le_trans (Nat.cast_le.mpr ht_le_max) (hG S.card)
  have hsq_real : ((t ^ 2 : ℕ) : ℝ) ≤ (S.card : ℝ) := by
    have h1 : (t : ℝ) ^ 2 ≤ ((S.card : ℝ).sqrt) ^ 2 := by
      nlinarith [Nat.cast_nonneg (α := ℝ) t, Real.sqrt_nonneg (S.card : ℝ)]
    rw [Real.sq_sqrt (Nat.cast_nonneg _)] at h1
    simpa [Nat.cast_pow] using h1
  exact Nat.cast_le.mp hsq_real

lemma exists_odd_walk_transversal
    (hG : ∀ n : ℕ, (Erdos74.SimpleGraph.maxSubgraphEdgeDistToBipartite G n : ℝ) ≤ (n : ℝ).sqrt)
    (L : ℕ) :
    ∃ T : Finset V, T.card ≤ L ^ 2 ∧
      ∀ v : V, ∀ p : G.Walk v v, Odd p.length → p.length ≤ L → ∃ x ∈ p.support, x ∈ T := by
  classical
  let Pack : ℕ → Prop := fun k =>
    ∃ (w : Fin k → Σ v : V, G.Walk v v),
      (∀ i, Odd (w i).2.length ∧ (w i).2.length ≤ L) ∧
      (∀ i j, i ≠ j → ∀ x, x ∈ (w i).2.support → x ∉ (w j).2.support)
  have hbound : ∀ k, Pack k → k ≤ L := by
    rintro k ⟨w, hlen, hdisj⟩
    let S : Finset V := Finset.univ.biUnion (fun i => (w i).2.support.toFinset)
    have hScard : S.card ≤ k * L := by
      calc S.card ≤ ∑ i : Fin k, (w i).2.support.toFinset.card := Finset.card_biUnion_le
        _ ≤ ∑ _i : Fin k, L := by
            refine Finset.sum_le_sum fun i _ => ?_
            have h1 : 1 ≤ (w i).2.length := by
              obtain ⟨m, hm⟩ := (hlen i).1
              omega
            exact le_trans (walk_support_toFinset_card_le (w i).2 h1) (hlen i).2
        _ = k * L := by simp
    have hsupp : ∀ i, ∀ z ∈ (w i).2.support, z ∈ S := by
      intro i z hz
      exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, List.mem_toFinset.mpr hz⟩
    have hedg : ∀ i j, i ≠ j → ∀ e, e ∈ (w i).2.edges → e ∉ (w j).2.edges := by
      intro i j hij e hei hej
      induction e using Sym2.ind with
      | _ a b =>
        have ha1 : a ∈ (w i).2.support := Walk.fst_mem_support_of_mem_edges (w i).2 hei
        have ha2 : a ∈ (w j).2.support := Walk.fst_mem_support_of_mem_edges (w j).2 hej
        exact hdisj i j hij a ha1 ha2
    have hsq := disjoint_odd_walks_sq_le hG S w (fun i => (hlen i).1) hsupp hedg
    have hkl : k * k ≤ k * L := by
      calc k * k = k ^ 2 := (sq k).symm
        _ ≤ S.card := hsq
        _ ≤ k * L := hScard
    rcases Nat.eq_zero_or_pos k with rfl | hkpos
    · exact Nat.zero_le L
    · exact Nat.le_of_mul_le_mul_left hkl hkpos
  have hP0 : Pack 0 := ⟨Fin.elim0, fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩
  let good : Finset ℕ := (Finset.range (L + 1)).filter Pack
  have hgood_ne : good.Nonempty := ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.succ_pos L), hP0⟩⟩
  let m : ℕ := good.max' hgood_ne
  have hm_mem : m ∈ good := Finset.max'_mem good hgood_ne
  have hm_pack : Pack m := (Finset.mem_filter.mp hm_mem).2
  have hm_le : m ≤ L := Nat.lt_succ_iff.mp (Finset.mem_range.mp (Finset.mem_filter.mp hm_mem).1)
  obtain ⟨w, hlen, hdisj⟩ := hm_pack
  let T : Finset V := Finset.univ.biUnion (fun i => (w i).2.support.toFinset)
  refine ⟨T, ?_, ?_⟩
  · calc T.card ≤ ∑ i : Fin m, (w i).2.support.toFinset.card := Finset.card_biUnion_le
      _ ≤ ∑ _i : Fin m, L := by
          refine Finset.sum_le_sum fun i _ => ?_
          have h1 : 1 ≤ (w i).2.length := by
            obtain ⟨r, hr⟩ := (hlen i).1
            omega
          exact le_trans (walk_support_toFinset_card_le (w i).2 h1) (hlen i).2
      _ = m * L := by simp
      _ ≤ L * L := Nat.mul_le_mul_right L hm_le
      _ = L ^ 2 := (sq L).symm
  · intro u p hpodd hplen
    by_contra hmiss
    push Not at hmiss
    have hPackSucc : Pack (m + 1) := by
      let w' : Fin (m + 1) → Σ v : V, G.Walk v v :=
        fun i => if h : i.1 < m then w ⟨i.1, h⟩ else ⟨u, p⟩
      have hw'_lt : ∀ (i : Fin (m + 1)) (hi : i.1 < m), w' i = w ⟨i.1, hi⟩ :=
        fun i hi => dif_pos hi
      have hw'_ge : ∀ (i : Fin (m + 1)) (hi : ¬ i.1 < m), w' i = ⟨u, p⟩ :=
        fun i hi => dif_neg hi
      refine ⟨w', ?_, ?_⟩
      · intro i
        by_cases hi : i.1 < m
        · rw [hw'_lt i hi]
          exact hlen ⟨i.1, hi⟩
        · rw [hw'_ge i hi]
          exact ⟨hpodd, hplen⟩
      · intro i j hij x hxi hxj
        by_cases hi : i.1 < m <;> by_cases hj : j.1 < m
        · rw [hw'_lt i hi] at hxi
          rw [hw'_lt j hj] at hxj
          have hij' : (⟨i.1, hi⟩ : Fin m) ≠ ⟨j.1, hj⟩ := fun h =>
            hij (Fin.ext (congrArg (fun x : Fin m => x.1) h))
          exact hdisj _ _ hij' x hxi hxj
        · rw [hw'_lt i hi] at hxi
          rw [hw'_ge j hj] at hxj
          have hxT : x ∈ T :=
            Finset.mem_biUnion.mpr ⟨⟨i.1, hi⟩, Finset.mem_univ _, List.mem_toFinset.mpr hxi⟩
          exact hmiss x hxj hxT
        · rw [hw'_ge i hi] at hxi
          rw [hw'_lt j hj] at hxj
          have hxT : x ∈ T :=
            Finset.mem_biUnion.mpr ⟨⟨j.1, hj⟩, Finset.mem_univ _, List.mem_toFinset.mpr hxj⟩
          exact hmiss x hxi hxT
        · exact hij (Fin.ext (by omega))
    have hm1_le : m + 1 ≤ L := hbound (m + 1) hPackSucc
    have hm1_mem : m + 1 ∈ good :=
      Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hm1_le), hPackSucc⟩
    have hm1_le_m : m + 1 ≤ m := Finset.le_max' good (m + 1) hm1_mem
    omega

end BridgeAndLemmaA

section BallCarving

lemma exists_lt_of_prod_lt {r : ℕ} {f g : ℕ → ℝ}
    (hg : ∀ i < r, 0 ≤ g i)
    (hprod : ∏ i ∈ Finset.range r, f i < ∏ i ∈ Finset.range r, g i) :
    ∃ i < r, f i < g i := by
  by_contra h
  push Not at h
  have hge : ∏ i ∈ Finset.range r, g i ≤ ∏ i ∈ Finset.range r, f i :=
    Finset.prod_le_prod (fun i hi => hg i (Finset.mem_range.mp hi))
      (fun i hi => h i (Finset.mem_range.mp hi))
  linarith

lemma ball_carving_step {W : Type u} [Fintype W] (H : SimpleGraph W)
    {r : ℕ} {α : ℝ} (_hr : 1 ≤ r) (hα : 0 ≤ α)
    (hodd : ∀ v : W, ∀ p : H.Walk v v, Odd p.length → 2 * r + 1 < p.length)
    (hgrow : (Fintype.card W : ℝ) < (1 + α) ^ r) :
    ∃ R : Finset W, (H.induce (R : Set W)ᶜ).Colorable 2 ∧
      (R.card : ℝ) ≤ α * (Fintype.card W : ℝ) := by
  classical
  have hstrong : ∀ n : ℕ, ∀ (U : Finset W), U.card = n →
      ∃ R : Finset W, R ⊆ U ∧
        (H.induce ((U \ R : Finset W) : Set W)).Colorable 2 ∧
        (R.card : ℝ) ≤ α * (U.card : ℝ) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro U hUcard
      rcases U.eq_empty_or_nonempty with rfl | ⟨v0, hv0⟩
      · refine ⟨∅, Finset.empty_subset _, ?_, by simp⟩
        exact ⟨Coloring.mk (fun x => False.elim (by simpa using x.2))
          (fun {x} => False.elim (by simpa using x.2))⟩
      · let HU : SimpleGraph {x // x ∈ (U : Set W)} := H.induce (U : Set W)
        let v0' : {x // x ∈ (U : Set W)} := ⟨v0, hv0⟩
        let B : ℕ → Finset W := fun k =>
          U.filter fun w => ∃ hw : w ∈ (U : Set W), ∃ p : HU.Walk v0' ⟨w, hw⟩, p.length ≤ k
        have hB0 : B 0 = {v0} := by
          ext w
          simp only [B, Finset.mem_filter, Finset.mem_singleton]
          constructor
          · rintro ⟨_, hw, p, hp⟩
            have hp0 : p.length = 0 := Nat.eq_zero_of_le_zero hp
            exact congrArg Subtype.val (Walk.eq_of_length_eq_zero hp0).symm
          · rintro rfl
            exact ⟨hv0, hv0, .nil, le_rfl⟩
        have hBmono : ∀ k, B k ⊆ B (k + 1) := by
          intro k w hw
          simp only [B, Finset.mem_filter] at hw ⊢
          obtain ⟨hwU, hw', p, hp⟩ := hw
          exact ⟨hwU, hw', p, Nat.le_succ_of_le hp⟩
        have hBsub : ∀ k, B k ⊆ U := fun k => Finset.filter_subset _ U
        have hBr_le : (B r).card ≤ Fintype.card W :=
          le_trans (Finset.card_le_card (Finset.subset_univ _)) (by simp)
        have hBpos : ∀ k, 0 < (B k).card := by
          intro k
          have hv0Bk : v0 ∈ B k := by
            simp only [B, Finset.mem_filter]
            exact ⟨hv0, hv0, .nil, Nat.zero_le k⟩
          exact Finset.card_pos.mpr ⟨v0, hv0Bk⟩
        have hprod_eq :
            (∏ i ∈ Finset.range r, ((B (i + 1)).card : ℝ)) * ((B 0).card : ℝ) =
              ((B r).card : ℝ) * (∏ i ∈ Finset.range r, ((B i).card : ℝ)) := by
          have ht : ∀ m : ℕ,
              (∏ i ∈ Finset.range m, ((B (i + 1)).card : ℝ)) * ((B 0).card : ℝ) =
                ((B m).card : ℝ) * (∏ i ∈ Finset.range m, ((B i).card : ℝ)) := by
            intro m
            induction m with
            | zero => simp
            | succ k ihk =>
              rw [Finset.prod_range_succ, Finset.prod_range_succ]
              calc (∏ x ∈ Finset.range k, ((B (x + 1)).card : ℝ)) * ((B (k + 1)).card : ℝ) * ((B 0).card : ℝ)
                  = ((∏ x ∈ Finset.range k, ((B (x + 1)).card : ℝ)) * ((B 0).card : ℝ)) * ((B (k + 1)).card : ℝ) := by ring
                _ = (((B k).card : ℝ) * (∏ x ∈ Finset.range k, ((B x).card : ℝ))) * ((B (k + 1)).card : ℝ) := by rw [ihk]
                _ = ((B (k + 1)).card : ℝ) * ((∏ x ∈ Finset.range k, ((B x).card : ℝ)) * ((B k).card : ℝ)) := by ring
          exact ht r
        have hB0card : ((B 0).card : ℝ) = 1 := by simp [hB0]
        have hprod_pos : 0 < ∏ i ∈ Finset.range r, ((B i).card : ℝ) :=
          Finset.prod_pos fun i _ => Nat.cast_pos.mpr (hBpos i)
        have hprod_lt :
            ∏ i ∈ Finset.range r, ((B (i + 1)).card : ℝ) <
              ∏ i ∈ Finset.range r, ((1 + α) * ((B i).card : ℝ)) := by
          rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
          have h1 : ∏ i ∈ Finset.range r, ((B (i + 1)).card : ℝ) =
              ((B r).card : ℝ) * ∏ i ∈ Finset.range r, ((B i).card : ℝ) := by
            simpa [hB0card] using hprod_eq
          rw [h1]
          have hBr_lt : ((B r).card : ℝ) < (1 + α) ^ r :=
            lt_of_le_of_lt (Nat.cast_le.mpr hBr_le) hgrow
          exact mul_lt_mul_of_pos_right hBr_lt hprod_pos
        obtain ⟨i, hi_lt, hi_bound⟩ := exists_lt_of_prod_lt
          (fun k _ => mul_nonneg (by linarith) (Nat.cast_nonneg _))
          hprod_lt
        let R1 : Finset W := B (i + 1) \ B i
        let U' : Finset W := U \ B (i + 1)
        have hU'_lt : U'.card < n := by
          rw [← hUcard]
          apply Finset.card_lt_card
          rw [Finset.ssubset_iff_subset_ne]
          refine ⟨Finset.sdiff_subset, fun heq => ?_⟩
          have hv0B : v0 ∈ B (i + 1) := by
            simp only [B, Finset.mem_filter]
            exact ⟨hv0, hv0, .nil, Nat.zero_le _⟩
          have : v0 ∈ U' := heq ▸ hv0
          exact (Finset.mem_sdiff.mp this).2 hv0B
        obtain ⟨R2, hR2sub, hR2col, hR2card⟩ := ih U'.card hU'_lt U' rfl
        let R : Finset W := R1 ∪ R2
        have hR1sub : R1 ⊆ U := Finset.Subset.trans Finset.sdiff_subset (hBsub (i + 1))
        have hRsub : R ⊆ U := Finset.union_subset hR1sub (Finset.Subset.trans hR2sub Finset.sdiff_subset)
        have hRdisj : Disjoint R1 R2 := by
          rw [Finset.disjoint_left]
          intro x hx1 hx2
          have hxB : x ∈ B (i + 1) := (Finset.mem_sdiff.mp hx1).1
          have hxU' : x ∈ U' := hR2sub hx2
          exact (Finset.mem_sdiff.mp hxU').2 hxB
        have hR1card : (R1.card : ℝ) ≤ α * ((B i).card : ℝ) := by
          have hsub : B i ⊆ B (i + 1) := hBmono i
          have hcard : (B i).card + R1.card = (B (i + 1)).card := by
            rw [Nat.add_comm]
            exact Finset.card_sdiff_add_card_eq_card hsub
          have hcardR : ((B i).card : ℝ) + (R1.card : ℝ) = ((B (i + 1)).card : ℝ) := by
            exact_mod_cast hcard
          linarith
        have hBi_U'_disj : Disjoint (B i) U' := by
          rw [Finset.disjoint_left]
          intro x hx1 hx2
          exact (Finset.mem_sdiff.mp hx2).2 (hBmono i hx1)
        have hBi_U'_sub : B i ∪ U' ⊆ U :=
          Finset.union_subset (hBsub i) Finset.sdiff_subset
        have hRcard : (R.card : ℝ) ≤ α * (U.card : ℝ) := by
          have h1 : R.card = R1.card + R2.card := Finset.card_union_of_disjoint hRdisj
          have h2 : (B i).card + U'.card ≤ U.card := by
            rw [← Finset.card_union_of_disjoint hBi_U'_disj]
            exact Finset.card_le_card hBi_U'_sub
          have h2R : ((B i).card : ℝ) + (U'.card : ℝ) ≤ (U.card : ℝ) := by exact_mod_cast h2
          rw [h1, Nat.cast_add]
          nlinarith
        have hBicol : (H.induce ((B i : Finset W) : Set W)).Colorable 2 := by
          have hex : ∀ x : {w // w ∈ ((B i : Finset W) : Set W)},
              ∃ k : ℕ, ∃ hxU : x.1 ∈ (U : Set W), ∃ p : HU.Walk v0' ⟨x.1, hxU⟩, p.length = k := by
            intro x
            have hxB : x.1 ∈ B i := x.2
            simp only [B, Finset.mem_filter] at hxB
            obtain ⟨_, hxU, p, _⟩ := hxB
            exact ⟨p.length, hxU, p, rfl⟩
          let distX : {w // w ∈ ((B i : Finset W) : Set W)} → ℕ :=
            fun x => Nat.find (hex x)
          have hdist_le : ∀ x, distX x ≤ i := by
            intro x
            have hxB : x.1 ∈ B i := x.2
            simp only [B, Finset.mem_filter] at hxB
            obtain ⟨_, hxU, p, hp⟩ := hxB
            exact le_trans (Nat.find_min' (hex x) ⟨hxU, p, rfl⟩) hp
          refine ⟨Coloring.mk (fun x => ⟨distX x % 2, Nat.mod_lt _ (by norm_num)⟩) ?_⟩
          intro x y hxy hEq
          have hxy' : H.Adj x.1 y.1 := hxy
          have hEq' : distX x % 2 = distX y % 2 := congrArg Fin.val hEq
          obtain ⟨hxU, px, hpx⟩ := Nat.find_spec (hex x)
          obtain ⟨hyU, py, hpy⟩ := Nat.find_spec (hex y)
          let pxH : H.Walk v0 x.1 := walkInduceMap px
          let pyH : H.Walk v0 y.1 := walkInduceMap py
          let closed : H.Walk v0 v0 := (pxH.append (.cons hxy' .nil)).append pyH.reverse
          have hcl_len : closed.length = distX x + 1 + distX y := by
            dsimp only [closed, pxH, pyH, distX]
            rw [Walk.length_append, Walk.length_append, Walk.length_reverse,
              Walk.length_cons, Walk.length_nil, walkInduceMap_length, walkInduceMap_length,
              hpx, hpy]
          have hcl_odd : Odd closed.length := by
            rw [hcl_len]
            refine ⟨distX x / 2 + distX y / 2 + distX x % 2, ?_⟩
            omega
          have hcl_gt := hodd v0 closed hcl_odd
          have hdx := hdist_le x
          have hdy := hdist_le y
          omega
        refine ⟨R, hRsub, ?_, hRcard⟩
        have hunion : ((U \ R : Finset W) : Set W) =
            ⋃ b : Bool, (if b then ((B i : Finset W) : Set W) else ((U' \ R2 : Finset W) : Set W)) := by
          ext x
          simp only [Finset.mem_coe, Finset.mem_sdiff, Set.mem_iUnion, Bool.exists_bool,
            Bool.false_eq_true, ↓reduceIte, R, R1, U', Finset.mem_union]
          constructor
          · rintro ⟨hxU, hxnotR⟩
            by_cases hxBi : x ∈ B i
            · exact Or.inr hxBi
            · left
              have hxnotB1 : x ∉ B (i + 1) := fun h => hxnotR (Or.inl ⟨h, hxBi⟩)
              have hxnotR2 : x ∉ R2 := fun h => hxnotR (Or.inr h)
              exact ⟨⟨hxU, hxnotB1⟩, hxnotR2⟩
          · rintro (⟨⟨hxU, hxnotB1⟩, hxnotR2⟩ | hxBi)
            · refine ⟨hxU, ?_⟩
              rintro (⟨hB1, _⟩ | hR2)
              · exact hxnotB1 hB1
              · exact hxnotR2 hR2
            · refine ⟨hBsub i hxBi, ?_⟩
              rintro (⟨_, hnotBi⟩ | hR2)
              · exact hnotBi hxBi
              · exact (Finset.mem_sdiff.mp (hR2sub hR2)).2 (hBmono i hxBi)
        rw [hunion]
        apply colorable_disjoint_union_family
        · intro b
          cases b
          · exact hR2col
          · exact hBicol
        · intro b1 b2 hne x hx y hy hxy
          have hstep : ∀ a ∈ B i, ∀ b ∈ U' \ R2, ¬ H.Adj a b := by
            intro a ha b hb hab
            have haB : a ∈ B i := ha
            simp only [B, Finset.mem_filter] at haB
            obtain ⟨_, haU, pa, hpa⟩ := haB
            have hbU' : b ∈ U' := (Finset.mem_sdiff.mp hb).1
            have hbU : b ∈ U := (Finset.mem_sdiff.mp hbU').1
            have hbnotB1 : b ∉ B (i + 1) := (Finset.mem_sdiff.mp hbU').2
            have hadjU : HU.Adj ⟨a, haU⟩ ⟨b, hbU⟩ := hab
            have hbB1 : b ∈ B (i + 1) := by
              simp only [B, Finset.mem_filter]
              exact ⟨hbU, hbU, pa.append (.cons hadjU .nil), by simp; omega⟩
            exact hbnotB1 hbB1
          cases b1 <;> cases b2
          · exact hne rfl
          · exact hstep y hy x hx hxy.symm
          · exact hstep x hx y hy hxy
          · exact hne rfl
  obtain ⟨R, _, hcol, hcard⟩ := hstrong (Fintype.card W) Finset.univ rfl
  have heq : ((Finset.univ \ R : Finset W) : Set W) = (R : Set W)ᶜ := by
    ext x
    simp
  rw [heq] at hcol
  exact ⟨R, hcol, by simpa using hcard⟩

lemma colorable_of_ball_carving {W : Type u} [Fintype W] (H : SimpleGraph W)
    {r p : ℕ} {α : ℝ} (hr : 1 ≤ r) (hα : 0 ≤ α)
    (hodd : ∀ v : W, ∀ w : H.Walk v v, Odd w.length → 2 * r + 1 < w.length)
    (hgrow : (Fintype.card W : ℝ) < (1 + α) ^ r)
    (hshrink : α ^ p * (Fintype.card W : ℝ) < 1) :
    H.Colorable (2 * p) := by
  classical
  have hiter : ∀ k : ℕ, ∃ R : Finset W,
      (H.induce (R : Set W)ᶜ).Colorable (2 * k) ∧
      (R.card : ℝ) ≤ α ^ k * (Fintype.card W : ℝ) := by
    intro k
    induction k with
    | zero =>
      refine ⟨Finset.univ, ?_, by simp⟩
      have hemp : ((Finset.univ : Finset W) : Set W)ᶜ = ∅ := by simp
      rw [hemp]
      exact ⟨Coloring.mk (fun x => False.elim x.2) (fun {x} => False.elim x.2)⟩
    | succ k ih =>
      obtain ⟨R, hRcol, hRcard⟩ := ih
      let HR : SimpleGraph {x // x ∈ (R : Set W)} := H.induce (R : Set W)
      have hHRodd : ∀ v : {x // x ∈ (R : Set W)}, ∀ w : HR.Walk v v,
          Odd w.length → 2 * r + 1 < w.length := by
        intro v w hw
        have hlen : (walkInduceMap w).length = w.length := walkInduceMap_length w
        rw [← hlen]
        exact hodd v.1 (walkInduceMap w) (by rw [hlen]; exact hw)
      have hHRcard : Fintype.card {x // x ∈ (R : Set W)} = R.card := by
        simp [Fintype.card_coe]
      have hHRgrow : (Fintype.card {x // x ∈ (R : Set W)} : ℝ) < (1 + α) ^ r := by
        rw [hHRcard]
        exact lt_of_le_of_lt (Nat.cast_le.mpr (le_trans (Finset.card_le_card (Finset.subset_univ _)) (by simp))) hgrow
      obtain ⟨Rsub, hRsubcol, hRsubcard⟩ := ball_carving_step HR hr hα hHRodd hHRgrow
      let R' : Finset W := Rsub.map (Function.Embedding.subtype _)
      have hR'sub : R' ⊆ R := by
        intro x hx
        obtain ⟨y, _, rfl⟩ := Finset.mem_map.mp hx
        exact y.2
      have hR'card : R'.card = Rsub.card := Finset.card_map _
      refine ⟨R', ?_, ?_⟩
      · have hunion : (R' : Set W)ᶜ = (R : Set W)ᶜ ∪ ((R : Set W) \ (R' : Set W)) := by
          ext x
          simp only [Set.mem_compl_iff, Finset.mem_coe, Set.mem_union, Set.mem_sdiff]
          by_cases hxR : x ∈ R
          · simp [hxR]
          · have hxR' : x ∉ R' := fun h => hxR (hR'sub h)
            simp [hxR, hxR']
        rw [hunion, Nat.mul_succ]
        apply colorable_union_sets hRcol
        obtain ⟨c⟩ := hRsubcol
        refine ⟨Coloring.mk (fun x => c ⟨⟨x.1, x.2.1⟩, ?_⟩) ?_⟩
        · intro hxsub
          exact x.2.2 (Finset.mem_map.mpr ⟨⟨x.1, x.2.1⟩, hxsub, rfl⟩)
        · intro x y hxy
          exact c.valid hxy
      · rw [hR'card]
        rw [hHRcard] at hRsubcard
        calc (Rsub.card : ℝ) ≤ α * (R.card : ℝ) := hRsubcard
          _ ≤ α * (α ^ k * (Fintype.card W : ℝ)) := mul_le_mul_of_nonneg_left hRcard hα
          _ = α ^ (k + 1) * (Fintype.card W : ℝ) := by rw [pow_succ']; ring
  obtain ⟨R, hRcol, hRcard⟩ := hiter p
  have hRempty : R = ∅ := by
    have hlt : (R.card : ℝ) < 1 := lt_of_le_of_lt hRcard hshrink
    have hltN : R.card < 1 := by exact_mod_cast hlt
    exact Finset.card_eq_zero.mp (by omega)
  subst hRempty
  obtain ⟨c⟩ := hRcol
  exact ⟨Coloring.mk (fun x => c ⟨x, by simp⟩) (fun hxy => c.valid hxy)⟩

lemma nat_pow19_lt_two_pow_self (j : ℕ) : j ^ 19 < 2 ^ (19 * j) := by
  have h1 : j < 2 ^ j := Nat.lt_two_pow_self
  calc j ^ 19 < (2 ^ j) ^ 19 := Nat.pow_lt_pow_left h1 (by norm_num)
    _ = 2 ^ (19 * j) := by rw [← pow_mul, mul_comm]

lemma colorable_38_of_poly_bound {W : Type u} [Fintype W] (H : SimpleGraph W)
    {j N : ℕ} (hj : 2 ≤ j) (hN : 2 ^ (200 + 20 * j) ≤ N)
    (hcard : Fintype.card W ≤ 256 * j ^ 3 * (N ^ 2) ^ 8)
    (hodd : ∀ v : W, ∀ w : H.Walk v v, Odd w.length → N ^ 2 < (2 * j - 1) * w.length) :
    H.Colorable 38 := by
  have hNpos : 0 < N := lt_of_lt_of_le (by positivity) hN
  have hN_gt1 : 1 < N := by
    have : 2 ^ 200 ≤ N := le_trans (Nat.pow_le_pow_right (by norm_num) (by omega)) hN
    have h2 : 1 < 2 ^ 200 := by norm_num
    omega
  have h256 : 256 * j ^ 3 ≤ N ^ 2 := by
    have hjlt : j < 2 ^ j := Nat.lt_two_pow_self
    have h3 : j ^ 3 < (2 ^ j) ^ 3 := Nat.pow_lt_pow_left hjlt (by norm_num)
    have h1 : 256 * j ^ 3 < 2 ^ (8 + 3 * j) := by
      calc 256 * j ^ 3 < 256 * (2 ^ j) ^ 3 := Nat.mul_lt_mul_of_pos_left h3 (by norm_num)
        _ = 2 ^ 8 * 2 ^ (3 * j) := by rw [← pow_mul, mul_comm j 3]; norm_num
        _ = 2 ^ (8 + 3 * j) := (pow_add 2 8 (3 * j)).symm
    have h2 : 2 ^ (8 + 3 * j) ≤ N :=
      le_trans (Nat.pow_le_pow_right (by norm_num) (by omega)) hN
    have h4 : N ≤ N ^ 2 := Nat.le_self_pow (by norm_num) N
    omega
  have hW_le : Fintype.card W ≤ N ^ 18 := by
    calc Fintype.card W ≤ 256 * j ^ 3 * (N ^ 2) ^ 8 := hcard
      _ ≤ N ^ 2 * (N ^ 2) ^ 8 := Nat.mul_le_mul_right _ h256
      _ = N ^ 18 := by ring
  let r : ℕ := N ^ 2 / (4 * j)
  have h4j_pos : 0 < 4 * j := by omega
  have hN_ge_const : 2 ^ 140 * (6 * j) ^ 19 < N := by
    have hj19 : j ^ 19 < 2 ^ (19 * j) := nat_pow19_lt_two_pow_self j
    have h6 : 6 ^ 19 < 2 ^ 50 := by norm_num
    have hmul : (6 * j) ^ 19 < 2 ^ (50 + 19 * j) := by
      rw [mul_pow]
      calc 6 ^ 19 * j ^ 19 < 2 ^ 50 * 2 ^ (19 * j) :=
            Nat.mul_lt_mul_of_lt_of_lt h6 hj19
        _ = 2 ^ (50 + 19 * j) := (pow_add 2 50 (19 * j)).symm
    have h200 : 2 ^ (190 + 19 * j) ≤ 2 ^ (200 + 20 * j) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    calc 2 ^ 140 * (6 * j) ^ 19 < 2 ^ 140 * 2 ^ (50 + 19 * j) :=
          Nat.mul_lt_mul_of_pos_left hmul (by positivity)
      _ = 2 ^ (190 + 19 * j) := by rw [← pow_add]; ring_nf
      _ ≤ 2 ^ (200 + 20 * j) := h200
      _ ≤ N := hN
  have hN_big : 240 * j < N := by
    have h1 : 240 * j ≤ 2 ^ 140 * (6 * j) ^ 19 := by
      have h6j : 1 ≤ (6 * j) ^ 18 := Nat.one_le_pow _ _ (by omega)
      have h2 : 240 * j ≤ 2 ^ 140 * (6 * j) := by nlinarith [show 40 ≤ 2 ^ 140 by norm_num]
      calc 240 * j ≤ 2 ^ 140 * (6 * j) := h2
        _ ≤ 2 ^ 140 * ((6 * j) * (6 * j) ^ 18) := by
            apply Nat.mul_le_mul_left
            exact Nat.le_mul_of_pos_right _ h6j
        _ = 2 ^ 140 * (6 * j) ^ 19 := by ring
    omega
  have hr_ge : 1 ≤ r := by
    change 1 ≤ N ^ 2 / (4 * j)
    rw [Nat.le_div_iff_mul_le h4j_pos]
    nlinarith
  have hr_odd : ∀ v : W, ∀ w : H.Walk v v, Odd w.length → 2 * r + 1 < w.length := by
    intro v w hw
    have hlt := hodd v w hw
    have h1 : 4 * j * r ≤ N ^ 2 := Nat.mul_div_le (N ^ 2) (4 * j)
    have h4 : 2 * j ≤ r := by
      have hmul : (2 * j) * (4 * j) ≤ N ^ 2 := by nlinarith
      exact (Nat.le_div_iff_mul_le h4j_pos).mpr hmul
    have h2 : (2 * j - 1) * (2 * r + 1) ≤ N ^ 2 := by
      have h3 : (2 * j - 1) * (2 * r + 1) + 2 * r = 4 * j * r + (2 * j - 1) := by
        zify [show 1 ≤ 2 * j by omega]
        ring
      omega
    by_contra hle
    push Not at hle
    have hmul : (2 * j - 1) * w.length ≤ (2 * j - 1) * (2 * r + 1) :=
      Nat.mul_le_mul_left _ hle
    omega
  have hr_sub_ge : N ^ 2 ≤ (6 * j) * (r - 19) := by
    have hdiv_ge : N ^ 2 < 4 * j * (r + 1) := by
      have hmod := Nat.div_add_mod (N ^ 2) (4 * j)
      have hlt := Nat.mod_lt (N ^ 2) h4j_pos
      have hexp : 4 * j * (r + 1) = 4 * j * r + 4 * j := by ring
      change 4 * j * r + N ^ 2 % (4 * j) = N ^ 2 at hmod
      omega
    have hr_big : 60 ≤ r := by
      have hmul : 60 * (4 * j) ≤ N ^ 2 := by nlinarith
      exact (Nat.le_div_iff_mul_le h4j_pos).mpr hmul
    have hstep : 4 * j * (r + 1) ≤ 6 * j * (r - 19) := by
      zify [show 19 ≤ r by omega]
      nlinarith
    omega
  let α : ℝ := (1 : ℝ) / (N : ℝ)
  have hα_nonneg : 0 ≤ α := by positivity
  have hN_posR : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr hNpos
  have hshrink : α ^ 19 * (Fintype.card W : ℝ) < 1 := by
    have hW_R : (Fintype.card W : ℝ) ≤ (N : ℝ) ^ 18 := by exact_mod_cast hW_le
    calc α ^ 19 * (Fintype.card W : ℝ) ≤ α ^ 19 * (N : ℝ) ^ 18 :=
          mul_le_mul_of_nonneg_left hW_R (by positivity)
      _ = (1 : ℝ) / (N : ℝ) := by
          dsimp [α]
          field_simp
      _ < 1 := by
          rw [div_lt_one hN_posR]
          exact_mod_cast hN_gt1
  have hgrow : (Fintype.card W : ℝ) < (1 + α) ^ r := by
    have h19_le_r : 19 ≤ r := by
      have hmul : 19 * (4 * j) ≤ N ^ 2 := by nlinarith
      exact (Nat.le_div_iff_mul_le h4j_pos).mpr hmul
    have hbinom : ((r.choose 19 : ℕ) : ℝ) * α ^ 19 ≤ (1 + α) ^ r := by
      rw [add_comm, add_pow]
      have hmem : 19 ∈ Finset.range (r + 1) := Finset.mem_range.mpr (by omega)
      have hle := Finset.single_le_sum (f := fun k => α ^ k * 1 ^ (r - k) * (r.choose k : ℝ))
        (fun k _ => by positivity) hmem
      simpa [mul_comm] using hle
    have hchoose_lb : (r - 19) ^ 19 ≤ Nat.factorial 19 * r.choose 19 := by
      have hdesc : Nat.descFactorial r 19 = Nat.factorial 19 * r.choose 19 := by
        rw [Nat.descFactorial_eq_factorial_mul_choose]
      rw [← hdesc]
      have hgen : ∀ k : ℕ, (r - k) ^ k ≤ Nat.descFactorial r k := by
        intro k
        induction k with
        | zero => simp
        | succ k ih =>
          rw [Nat.descFactorial_succ, pow_succ']
          have h1 : (r - (k + 1)) ^ k ≤ (r - k) ^ k :=
            Nat.pow_le_pow_left (by omega) k
          have h2 : r - (k + 1) ≤ r - k := by omega
          exact Nat.mul_le_mul h2 (le_trans h1 ih)
      exact hgen 19
    have hfact19 : Nat.factorial 19 ≤ 2 ^ 140 := by norm_num [Nat.factorial]
    have hstrictN : Nat.factorial 19 * (6 * j) ^ 19 < N := by
      have h1 : Nat.factorial 19 * (6 * j) ^ 19 ≤ 2 ^ 140 * (6 * j) ^ 19 :=
        Nat.mul_le_mul_right _ hfact19
      exact lt_of_le_of_lt h1 hN_ge_const
    have hnum_lt : N ^ 18 * N ^ 19 < r.choose 19 := by
      have h1 : (N ^ 2) ^ 19 ≤ (6 * j) ^ 19 * (r - 19) ^ 19 := by
        rw [← mul_pow]
        exact Nat.pow_le_pow_left hr_sub_ge 19
      have h2 : (N ^ 2) ^ 19 ≤ (6 * j) ^ 19 * (Nat.factorial 19 * r.choose 19) :=
        le_trans h1 (Nat.mul_le_mul_left _ hchoose_lb)
      have h3 : N ^ 37 * (Nat.factorial 19 * (6 * j) ^ 19) < N ^ 38 := by
        calc N ^ 37 * (Nat.factorial 19 * (6 * j) ^ 19) < N ^ 37 * N :=
              Nat.mul_lt_mul_of_pos_left hstrictN (by positivity)
          _ = N ^ 38 := by ring
      have h4 : N ^ 38 = (N ^ 2) ^ 19 := by ring
      have h5 : (6 * j) ^ 19 * (Nat.factorial 19 * r.choose 19) =
          (Nat.factorial 19 * (6 * j) ^ 19) * r.choose 19 := by ring
      have h6 : N ^ 37 * (Nat.factorial 19 * (6 * j) ^ 19) <
          (Nat.factorial 19 * (6 * j) ^ 19) * r.choose 19 := by
        omega
      have h7 : N ^ 37 < r.choose 19 := by
        rw [mul_comm] at h6
        exact Nat.lt_of_mul_lt_mul_left h6
      simpa [show N ^ 18 * N ^ 19 = N ^ 37 by ring] using h7
    have hnum_ltR : ((N : ℝ) ^ 18) * ((N : ℝ) ^ 19) < (r.choose 19 : ℝ) := by
      exact_mod_cast hnum_lt
    have hW_R : (Fintype.card W : ℝ) ≤ (N : ℝ) ^ 18 := by exact_mod_cast hW_le
    have hlt_binom : (N : ℝ) ^ 18 < (r.choose 19 : ℝ) * α ^ 19 := by
      dsimp [α]
      rw [one_div, inv_pow, ← div_eq_mul_inv, lt_div_iff₀ (by positivity)]
      exact hnum_ltR
    exact lt_of_le_of_lt hW_R (lt_of_lt_of_le hlt_binom hbinom)
  simpa using colorable_of_ball_carving H hr_ge hα_nonneg hr_odd hgrow hshrink

end BallCarving

section ShellDecomposition

variable {V : Type u} {G : SimpleGraph V}

def scaleN (k : ℕ) : ℕ := 2 ^ (220 + 20 * k)
def scaleL (k : ℕ) : ℕ := (scaleN k) ^ 2

lemma scaleL_succ (k : ℕ) : scaleL (k + 1) = 2 ^ 40 * scaleL k := by
  dsimp only [scaleL, scaleN]
  have h1 : 220 + 20 * (k + 1) = 20 + (220 + 20 * k) := by omega
  rw [h1, pow_add, mul_pow]
  ring

lemma scaleL_sum_sq_le (m : ℕ) (hm : 1 ≤ m) :
    ∑ k ∈ Finset.Icc 1 m, (scaleL k) ^ 2 ≤ 2 * (scaleL m) ^ 2 := by
  induction m with
  | zero => omega
  | succ k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp; omega
    · have hIcc : Finset.Icc 1 (k + 1) = insert (k + 1) (Finset.Icc 1 k) := by
        ext x
        simp only [Finset.mem_Icc, Finset.mem_insert]
        omega
      have hnot : k + 1 ∉ Finset.Icc 1 k := by simp
      rw [hIcc, Finset.sum_insert hnot]
      have ih' := ih hk
      have hstep : 2 * (scaleL k) ^ 2 ≤ (scaleL (k + 1)) ^ 2 := by
        rw [scaleL_succ k, mul_pow]
        have hbig : 2 ≤ (2 ^ 40) ^ 2 := by norm_num
        exact Nat.mul_le_mul_right _ hbig
      omega

lemma scaleN_pred_ge {j : ℕ} (hj : 2 ≤ j) :
    2 ^ (200 + 20 * j) ≤ scaleN (j - 1) := by
  dsimp only [scaleN]
  apply Nat.pow_le_pow_right (by norm_num)
  omega

lemma scaleL_gt_two_j {j : ℕ} (hj : 2 ≤ j) : 2 * j ≤ scaleL (j - 1) := by
  have h1 : 2 ^ (200 + 20 * j) ≤ scaleN (j - 1) := scaleN_pred_ge hj
  have h2 : j < 2 ^ j := Nat.lt_two_pow_self
  have h3 : 2 * j < 2 ^ (200 + 20 * j) := by
    calc 2 * j < 2 * 2 ^ j := by omega
      _ = 2 ^ (1 + j) := by rw [pow_add, pow_one]
      _ ≤ 2 ^ (200 + 20 * j) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h4 : scaleN (j - 1) ≤ scaleL (j - 1) := Nat.le_self_pow (by norm_num) _
  omega

lemma exists_shortest_odd_walk_distinct {W : Type u} {H : SimpleGraph W}
    (hex : ∃ v : W, ∃ p : H.Walk v v, Odd p.length) :
    ∃ (ℓ : ℕ) (v : W) (p : H.Walk v v),
      Odd ℓ ∧ p.length = ℓ ∧ 3 ≤ ℓ ∧
      ∀ a b : ℕ, a < b → b < ℓ → p.getVert a ≠ p.getVert b := by
  classical
  have hexL : ∃ ℓ : ℕ, Odd ℓ ∧ ∃ v : W, ∃ p : H.Walk v v, p.length = ℓ := by
    obtain ⟨v, p, hp⟩ := hex
    exact ⟨p.length, hp, v, p, rfl⟩
  let ℓ : ℕ := Nat.find hexL
  have hℓ_spec := Nat.find_spec hexL
  obtain ⟨hℓ_odd, v, p, hplen⟩ := hℓ_spec
  have hℓ_ge3 : 3 ≤ ℓ := by
    obtain ⟨k, hk⟩ := hℓ_odd
    rcases Nat.eq_zero_or_pos k with rfl | hkpos
    · have h1 : p.length = 1 := by omega
      cases p with
      | nil => simp at h1
      | cons hadj q =>
        simp only [Walk.length_cons] at h1
        have hq0 : q.length = 0 := by omega
        have heq := Walk.eq_of_length_eq_zero hq0
        exact False.elim (H.ne_of_adj hadj heq.symm)
    · omega
  refine ⟨ℓ, v, p, hℓ_odd, hplen, hℓ_ge3, ?_⟩
  intro a b hab hb heq
  have ha_le : a ≤ p.length := by omega
  have hb_le : b ≤ p.length := by omega
  let p_mid_raw := walkTake (walkDrop p a ha_le) (b - a) (by rw [walkDrop_length]; omega)
  have hmid_end : (walkDrop p a ha_le).getVert (b - a) = p.getVert b := by
    rw [walkDrop_getVert]
    congr 1
    omega
  let p_mid : H.Walk (p.getVert a) (p.getVert a) :=
    p_mid_raw.copy rfl (hmid_end.trans heq.symm)
  have hmid_len : p_mid.length = b - a := by
    dsimp only [p_mid, p_mid_raw]
    rw [Walk.length_copy, walkTake_length]
  let p_pre : H.Walk v (p.getVert a) := walkTake p a ha_le
  let p_suf : H.Walk (p.getVert a) v := (walkDrop p b hb_le).copy heq.symm rfl
  let p_out : H.Walk v v := p_pre.append p_suf
  have hout_len : p_out.length = a + (ℓ - b) := by
    dsimp only [p_out, p_pre, p_suf, ℓ]
    rw [Walk.length_append, walkTake_length, Walk.length_copy, walkDrop_length, hplen]
  have hsum : p_mid.length + p_out.length = ℓ := by omega
  rcases Nat.even_or_odd p_mid.length with hme | hmo
  · have hou : Odd p_out.length := by
      obtain ⟨r, hr⟩ := hme
      obtain ⟨s, hs⟩ := hℓ_odd
      refine ⟨s - r, ?_⟩
      omega
    have hmin := Nat.find_min hexL (show p_out.length < ℓ by omega)
    exact hmin ⟨hou, v, p_out, rfl⟩
  · have hmin := Nat.find_min hexL (show p_mid.length < ℓ by omega)
    exact hmin ⟨hmo, p.getVert a, p_mid, rfl⟩

lemma pigeonhole_disjoint_finsets [DecidableEq V] {M : ℕ}
    (B : Fin (M + 1) → Finset V) (U : Finset V)
    (hdisj : ∀ i j, i ≠ j → Disjoint (B i) (B j))
    (hcard : U.card < M + 1) :
    ∃ i : Fin (M + 1), Disjoint (B i) U := by
  classical
  by_contra hall
  push Not at hall
  have hhit : ∀ i : Fin (M + 1), ∃ x ∈ B i, x ∈ U := by
    intro i
    have h := hall i
    rw [Finset.disjoint_left] at h
    push Not at h
    exact h
  let f : Fin (M + 1) → V := fun i => Classical.choose (hhit i)
  have hfB : ∀ i, f i ∈ B i := fun i => (Classical.choose_spec (hhit i)).1
  have hfU : ∀ i, f i ∈ U := fun i => (Classical.choose_spec (hhit i)).2
  have hinj : Function.Injective f := by
    intro i j hij
    by_contra hne
    have h1 := hfB i
    rw [hij] at h1
    exact Finset.disjoint_left.mp (hdisj j i (Ne.symm hne)) (hfB j) h1
  have hle : M + 1 ≤ U.card := by
    have hsub : (Finset.univ.image f) ⊆ U := by
      intro x hx
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
      exact hfU i
    have h1 := Finset.card_le_card hsub
    rw [Finset.card_image_of_injective _ hinj, Finset.card_fin] at h1
    exact h1
  omega

def shells (T : ℕ → Finset V) : ℕ → Set V
  | 0 => ∅
  | j + 1 => shells T j ∪ {v | ∃ u ∈ shells T j, G.Adj u v} ∪ (T (j + 1) : Set V)

def annulus (T : ℕ → Finset V) (j : ℕ) : Set V :=
  shells (G := G) T j \ shells (G := G) T (j - 1)

lemma shells_mono (T : ℕ → Finset V) : ∀ {i j}, i ≤ j → shells (G := G) T i ⊆ shells (G := G) T j := by
  intro i j hij
  induction hij with
  | refl => exact Set.Subset.rfl
  | @step m _ ih =>
    intro x hx
    exact Or.inl (Or.inl (ih hx))

lemma annulus_no_skip (T : ℕ → Finset V) {i j : ℕ} (hij : i + 2 ≤ j)
    {x y : V} (hx : x ∈ annulus (G := G) T i) (hy : y ∈ annulus (G := G) T j) :
    ¬ G.Adj x y := by
  intro hxy
  have hxC : x ∈ shells (G := G) T i := hx.1
  have hyC1 : y ∈ shells (G := G) T (i + 1) := Or.inl (Or.inr ⟨x, hxC, hxy⟩)
  have hyCj : y ∈ shells (G := G) T (j - 1) := shells_mono T (by omega) hyC1
  exact hy.2 hyCj

lemma annulus_disjoint (T : ℕ → Finset V) {i j : ℕ} (hij : i ≠ j)
    {x : V} (hxi : x ∈ annulus (G := G) T i) (hxj : x ∈ annulus (G := G) T j) : False := by
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · exact hxj.2 (shells_mono T (by omega) hxi.1)
  · exact hxi.2 (shells_mono T (by omega) hxj.1)

lemma mem_shells_iff (T : ℕ → Finset V) :
    ∀ (j : ℕ) (v : V), v ∈ shells (G := G) T j ↔
      ∃ k, 1 ≤ k ∧ k ≤ j ∧ ∃ u ∈ T k, ∃ p : G.Walk u v, p.length ≤ j - k := by
  intro j
  induction j with
  | zero =>
    intro v
    simp [shells]
  | succ j ih =>
    intro v
    simp only [shells, Set.mem_union, Set.mem_ofPred_eq, Finset.mem_coe]
    constructor
    · rintro ((hv | ⟨u, hu, huv⟩) | hv)
      · obtain ⟨k, hk1, hkj, u0, hu0, p, hp⟩ := (ih v).mp hv
        exact ⟨k, hk1, by omega, u0, hu0, p, by omega⟩
      · obtain ⟨k, hk1, hkj, u0, hu0, p, hp⟩ := (ih u).mp hu
        exact ⟨k, hk1, by omega, u0, hu0, p.append (.cons huv .nil), by simp; omega⟩
      · exact ⟨j + 1, by omega, le_rfl, v, hv, .nil, by simp⟩
    · rintro ⟨k, hk1, hkj, u0, hu0, p, hp⟩
      rcases eq_or_lt_of_le hkj with rfl | hlt
      · have hp0 : p.length = 0 := by omega
        have heq := Walk.eq_of_length_eq_zero hp0
        exact Or.inr (heq ▸ hu0)
      · rcases Nat.eq_zero_or_pos p.length with hp0 | hppos
        · refine Or.inl (Or.inl ((ih v).mpr ⟨k, hk1, by omega, u0, hu0, p, by omega⟩))
        · rcases hrev : p.reverse with _ | ⟨hvw, q⟩
          · have hlen := Walk.length_reverse p
            rw [hrev] at hlen
            simp at hlen
            omega
          · have hqlen : q.length = p.length - 1 := by
              have hlen := Walk.length_reverse p
              rw [hrev, Walk.length_cons] at hlen
              omega
            have hw : _ ∈ shells (G := G) T j :=
              (ih _).mpr ⟨k, hk1, by omega, u0, hu0, q.reverse, by simp [hqlen]; omega⟩
            exact Or.inl (Or.inr ⟨_, hw, hvw.symm⟩)

lemma exists_stepping_path [DecidableEq V] (T : ℕ → Finset V) {j : ℕ} (hj : 2 ≤ j)
    {v : V} (hvA : v ∈ annulus (G := G) T j) (hvnotT : v ∉ T j) :
    let S : Finset V := (Finset.Icc 1 (j - 1)).biUnion T
    ∃ (m : ℕ) (u : V) (p : G.Walk u v),
      1 ≤ m ∧ m < j ∧ u ∈ S ∧ p.length = j - m ∧
      (∀ t ≤ p.length, p.getVert t ∈ annulus (G := G) T (m + t)) ∧
      (∀ t, 1 ≤ t → t ≤ p.length → p.getVert t ∉ S) := by
  intro S
  obtain ⟨k, hk1, hkj, w0, hw0, pfull, hpfull_le⟩ := (mem_shells_iff T j v).mp hvA.1
  have hkl : k < j := by
    by_contra hge
    have hkeq : k = j := by omega
    subst hkeq
    have hp0 : pfull.length = 0 := by omega
    exact hvnotT ((Walk.eq_of_length_eq_zero hp0) ▸ hw0)
  have hpfull_eq : pfull.length = j - k := by
    by_contra hne
    have hlt : pfull.length ≤ (j - 1) - k := by omega
    have hvC : v ∈ shells (G := G) T (j - 1) :=
      (mem_shells_iff T (j - 1) v).mpr ⟨k, hk1, by omega, w0, hw0, pfull, hlt⟩
    exact hvA.2 hvC
  have hstep_A : ∀ t (ht : t ≤ pfull.length), pfull.getVert t ∈ annulus (G := G) T (k + t) := by
    intro t ht
    refine ⟨?_, ?_⟩
    · exact (mem_shells_iff T (k + t) _).mpr
        ⟨k, hk1, by omega, w0, hw0, walkTake pfull t ht, by rw [walkTake_length]; omega⟩
    · intro hprev
      obtain ⟨k', hk'1, hk'le, u', hu', q', hq'⟩ := (mem_shells_iff T (k + t - 1) _).mp hprev
      let psuf := walkDrop pfull t ht
      let hcomb := q'.append psuf
      have hvC : v ∈ shells (G := G) T (j - 1) :=
        (mem_shells_iff T (j - 1) v).mpr
          ⟨k', hk'1, by omega, u', hu', hcomb, by
            dsimp only [hcomb, psuf]
            rw [Walk.length_append, walkDrop_length, hpfull_eq]
            omega⟩
      exact hvA.2 hvC
  have hS_sub_C : ∀ x ∈ S, x ∈ shells (G := G) T (j - 1) := by
    intro x hx
    obtain ⟨r, hr, hxr⟩ := Finset.mem_biUnion.mp hx
    simp only [Finset.mem_Icc] at hr
    exact (mem_shells_iff T (j - 1) x).mpr ⟨r, hr.1, hr.2, x, hxr, .nil, by simp⟩
  let hits : Finset ℕ := (Finset.range (pfull.length + 1)).filter (fun t => pfull.getVert t ∈ S)
  have h0_mem : 0 ∈ hits := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.succ_pos _), ?_⟩
    simp only [Walk.getVert_zero]
    exact Finset.mem_biUnion.mpr ⟨k, Finset.mem_Icc.mpr ⟨hk1, by omega⟩, hw0⟩
  let t0 : ℕ := hits.max' ⟨0, h0_mem⟩
  have ht0_mem : t0 ∈ hits := Finset.max'_mem hits ⟨0, h0_mem⟩
  have ht0_le : t0 ≤ pfull.length := Nat.lt_succ_iff.mp (Finset.mem_range.mp (Finset.mem_filter.mp ht0_mem).1)
  have ht0_S : pfull.getVert t0 ∈ S := (Finset.mem_filter.mp ht0_mem).2
  have ht0_lt : t0 < pfull.length := by
    by_contra hge
    have heq : t0 = pfull.length := by omega
    have hvS : v ∈ S := by
      have hgv : pfull.getVert pfull.length = v := Walk.getVert_length pfull
      rw [← hgv, ← heq]
      exact ht0_S
    exact hvA.2 (hS_sub_C v hvS)
  refine ⟨k + t0, pfull.getVert t0, walkDrop pfull t0 ht0_le, by omega, by omega, ht0_S, ?_, ?_, ?_⟩
  · rw [walkDrop_length, hpfull_eq]
    omega
  · intro t ht
    rw [walkDrop_length] at ht
    rw [walkDrop_getVert]
    have h1 := hstep_A (t0 + t) (by omega)
    simpa [Nat.add_assoc] using h1
  · intro t h1 hle hmemS
    rw [walkDrop_length] at hle
    rw [walkDrop_getVert] at hmemS
    have hmem : t0 + t ∈ hits :=
      Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hmemS⟩
    have hle_max : t0 + t ≤ t0 := Finset.le_max' hits (t0 + t) hmem
    omega

def shellS [DecidableEq V] (T : ℕ → Finset V) (j : ℕ) : Finset V :=
  (Finset.Icc 1 (j - 1)).biUnion T

def annulusPrime (G : SimpleGraph V) (T : ℕ → Finset V) (j : ℕ) : Set V :=
  annulus (G := G) T j \ (T j : Set V)

lemma shellS_card_le [DecidableEq V] (T : ℕ → Finset V)
    (hT_card : ∀ k, (T k).card ≤ (scaleL k) ^ 2) {j : ℕ} (hj : 2 ≤ j) :
    (shellS T j).card ≤ 2 * (scaleL (j - 1)) ^ 2 := by
  calc (shellS T j).card ≤ ∑ k ∈ Finset.Icc 1 (j - 1), (T k).card := Finset.card_biUnion_le
    _ ≤ ∑ k ∈ Finset.Icc 1 (j - 1), (scaleL k) ^ 2 := Finset.sum_le_sum fun k _ => hT_card k
    _ ≤ 2 * (scaleL (j - 1)) ^ 2 := scaleL_sum_sq_le (j - 1) (by omega)

lemma mem_shellS_of_mem_T_pred [DecidableEq V] (T : ℕ → Finset V) {j : ℕ} (hj : 2 ≤ j)
    {x : V} (hx : x ∈ T (j - 1)) : x ∈ shellS T j :=
  Finset.mem_biUnion.mpr ⟨j - 1, Finset.mem_Icc.mpr ⟨by omega, le_rfl⟩, hx⟩

lemma piece0_colorable_38
    (T : ℕ → Finset V)
    (hT_card : ∀ k, (T k).card ≤ (scaleL k) ^ 2)
    (hT_hit : ∀ k v (p : G.Walk v v), Odd p.length → p.length ≤ scaleL k → ∃ x ∈ p.support, x ∈ T k)
    {j : ℕ} (hj : 2 ≤ j) :
    (G.induce (annulus (G := G) T j ∩ (T j : Set V))).Colorable 38 := by
  classical
  let L : ℕ := scaleL (j - 1)
  let N : ℕ := scaleN (j - 1)
  have hL_eq : L = N ^ 2 := rfl
  have hN_ge : 2 ^ (200 + 20 * j) ≤ N := scaleN_pred_ge hj
  let F0 : Finset V := (T j).filter (fun x => x ∈ annulus (G := G) T j)
  have hF0_eq : (F0 : Set V) = annulus (G := G) T j ∩ (T j : Set V) := by
    ext x
    simp only [F0, Finset.mem_coe, Finset.mem_filter, Set.mem_inter_iff]
    tauto
  rw [← hF0_eq]
  apply colorable_38_of_poly_bound (j := j) (N := N) _ hj hN_ge
  · have hcard_eq : Fintype.card {x // x ∈ (F0 : Set V)} = F0.card :=
      Fintype.card_of_subtype F0 (fun _ => Finset.mem_coe.symm)
    rw [hcard_eq]
    have hcard0 : F0.card ≤ (scaleL j) ^ 2 :=
      le_trans (Finset.card_le_card (Finset.filter_subset _ _)) (hT_card j)
    have hscale : scaleL j = 2 ^ 40 * L := by
      have h1 : j = (j - 1) + 1 := by omega
      rw [h1, scaleL_succ]
    have h280 : (2 ^ 40) ^ 2 ≤ L ^ 6 := by
      have h1 : (2 ^ 40) ^ 2 ≤ N := by
        calc (2 ^ 40) ^ 2 = 2 ^ 80 := by norm_num
          _ ≤ 2 ^ (200 + 20 * j) := Nat.pow_le_pow_right (by norm_num) (by omega)
          _ ≤ N := hN_ge
      have h2 : N ≤ L := by rw [hL_eq]; exact Nat.le_self_pow (by norm_num) N
      exact le_trans (le_trans h1 h2) (Nat.le_self_pow (by norm_num) L)
    calc F0.card ≤ (2 ^ 40 * L) ^ 2 := by rw [← hscale]; exact hcard0
      _ = (2 ^ 40) ^ 2 * L ^ 2 := mul_pow _ _ _
      _ ≤ L ^ 6 * L ^ 2 := Nat.mul_le_mul_right _ h280
      _ = 1 * L ^ 8 := by ring
      _ ≤ (256 * j ^ 3) * L ^ 8 := Nat.mul_le_mul_right _ (Nat.mul_pos (by omega) (by positivity))
  · intro v w hw
    have hhit := hT_hit (j - 1) v.1 (walkInduceMap w) (by rw [walkInduceMap_length]; exact hw)
    by_contra hle
    push Not at hle
    have hlen_le : (walkInduceMap w).length ≤ L := by
      rw [walkInduceMap_length]
      have h1 : 1 ≤ 2 * j - 1 := by omega
      calc w.length = 1 * w.length := (one_mul _).symm
        _ ≤ (2 * j - 1) * w.length := Nat.mul_le_mul_right _ h1
        _ ≤ L := hle
    obtain ⟨x, hxsupp, hxT⟩ := hhit hlen_le
    have hxF0 : x ∈ F0 := Finset.mem_coe.mp (walkInduceMap_support_mem w x hxsupp)
    have hxA : x ∈ annulus (G := G) T j := (Finset.mem_filter.mp hxF0).2
    have hxC : x ∈ shells (G := G) T (j - 1) :=
      (mem_shells_iff T (j - 1) x).mpr ⟨j - 1, by omega, le_rfl, x, hxT, .nil, by simp⟩
    exact hxA.2 hxC

structure StepChoice [DecidableEq V] (G : SimpleGraph V) (T : ℕ → Finset V) (j : ℕ) where
  mU : {x // x ∈ annulusPrime G T j} → ℕ
  u0 : {x // x ∈ annulusPrime G T j} → V
  P : ∀ v, G.Walk (u0 v) v.1
  hspec : ∀ v,
    1 ≤ mU v ∧ mU v < j ∧ u0 v ∈ shellS T j ∧ (P v).length = j - mU v ∧
    (∀ t ≤ (P v).length, (P v).getVert t ∈ annulus (G := G) T (mU v + t)) ∧
    (∀ t, 1 ≤ t → t ≤ (P v).length → (P v).getVert t ∉ shellS T j)

noncomputable def mkStepChoice [DecidableEq V] (T : ℕ → Finset V) {j : ℕ} (hj : 2 ≤ j) :
    StepChoice G T j where
  mU v := Classical.choose (exists_stepping_path (G := G) T hj v.2.1 v.2.2)
  u0 v := Classical.choose (Classical.choose_spec (exists_stepping_path (G := G) T hj v.2.1 v.2.2))
  P v := Classical.choose (Classical.choose_spec (Classical.choose_spec (exists_stepping_path (G := G) T hj v.2.1 v.2.2)))
  hspec v := Classical.choose_spec (Classical.choose_spec (Classical.choose_spec (exists_stepping_path (G := G) T hj v.2.1 v.2.2)))

def StepChoice.intVerts [DecidableEq V] {T : ℕ → Finset V} {j : ℕ}
    (sc : StepChoice G T j) (v : {x // x ∈ annulusPrime G T j}) : Finset V :=
  (sc.P v).support.tail.toFinset

lemma StepChoice.intVerts_mem [DecidableEq V] {T : ℕ → Finset V} {j : ℕ}
    (sc : StepChoice G T j) (v : {x // x ∈ annulusPrime G T j}) (x : V) :
    x ∈ sc.intVerts v ↔ ∃ t, 1 ≤ t ∧ t ≤ (sc.P v).length ∧ (sc.P v).getVert t = x := by
  simp only [StepChoice.intVerts, List.mem_toFinset, mem_support_tail_iff]

lemma StepChoice.intVerts_card [DecidableEq V] {T : ℕ → Finset V} {j : ℕ}
    (sc : StepChoice G T j) (v : {x // x ∈ annulusPrime G T j}) :
    (sc.intVerts v).card ≤ j - 1 := by
  have hlen := (sc.hspec v).2.2.2.1
  have hm1 := (sc.hspec v).1
  have h1 : (sc.P v).support.tail.length = (sc.P v).length := by
    rw [List.length_tail, Walk.length_support]
    omega
  calc (sc.intVerts v).card ≤ (sc.P v).support.tail.length := List.toFinset_card_le _
    _ = (sc.P v).length := h1
    _ ≤ j - 1 := by omega

lemma StepChoice.intVerts_notS [DecidableEq V] {T : ℕ → Finset V} {j : ℕ}
    (sc : StepChoice G T j) (v : {x // x ∈ annulusPrime G T j}) (x : V)
    (hx : x ∈ sc.intVerts v) : x ∉ shellS T j := by
  obtain ⟨t, h1, hle, rfl⟩ := (sc.intVerts_mem v x).mp hx
  exact (sc.hspec v).2.2.2.2.2 t h1 hle

lemma no_internal_intersection [DecidableEq V] {T : ℕ → Finset V} {j : ℕ}
    (sc : StepChoice G T j)
    (hT_hit : ∀ k v (p : G.Walk v v), Odd p.length → p.length ≤ scaleL k → ∃ x ∈ p.support, x ∈ T k)
    (hj : 2 ≤ j) (a b : {x // x ∈ annulusPrime G T j}) (hab : G.Adj a.1 b.1) :
    Disjoint (sc.intVerts a) (sc.intVerts b) := by
  have h2j_le_L : 2 * j ≤ scaleL (j - 1) := scaleL_gt_two_j hj
  rw [Finset.disjoint_left]
  intro z hza hzb
  obtain ⟨ta, hta1, hta_le, hza_eq⟩ := (sc.intVerts_mem a z).mp hza
  obtain ⟨tb, htb1, htb_le, hzb_eq⟩ := (sc.intVerts_mem b z).mp hzb
  have hzaA : z ∈ annulus (G := G) T (sc.mU a + ta) := hza_eq ▸ (sc.hspec a).2.2.2.2.1 ta hta_le
  have hzbA : z ∈ annulus (G := G) T (sc.mU b + tb) := hzb_eq ▸ (sc.hspec b).2.2.2.2.1 tb htb_le
  have hm_eq : sc.mU a + ta = sc.mU b + tb := by
    by_contra hne
    exact annulus_disjoint T hne hzaA hzbA
  let qa : G.Walk z a.1 := (walkDrop (sc.P a) ta hta_le).copy hza_eq rfl
  let qb : G.Walk z b.1 := (walkDrop (sc.P b) tb htb_le).copy hzb_eq rfl
  let closed : G.Walk z z := (qa.append (.cons hab .nil)).append qb.reverse
  have hqa_len : qa.length = j - (sc.mU a + ta) := by
    simp [qa, Walk.length_copy, walkDrop_length, (sc.hspec a).2.2.2.1]
    omega
  have hqb_len : qb.length = j - (sc.mU a + ta) := by
    simp [qb, Walk.length_copy, walkDrop_length, (sc.hspec b).2.2.2.1]
    omega
  have hcl_len : closed.length = 2 * (j - (sc.mU a + ta)) + 1 := by
    simp only [closed, Walk.length_append, Walk.length_reverse, Walk.length_cons, Walk.length_nil,
      hqa_len, hqb_len]
    omega
  have hcl_odd : Odd closed.length := ⟨j - (sc.mU a + ta), hcl_len⟩
  have hcl_le : closed.length ≤ scaleL (j - 1) := by omega
  obtain ⟨x, hxsupp, hxT⟩ := hT_hit (j - 1) z closed hcl_odd hcl_le
  have hx_notS : x ∉ shellS T j := by
    have hqa_notS : ∀ y ∈ qa.support, y ∉ shellS T j := by
      intro y hy
      have hy' : y ∈ (walkDrop (sc.P a) ta hta_le).support := by
        simpa [qa, Walk.support_copy] using hy
      obtain ⟨s, hs, hys⟩ := (mem_support_iff_exists_getVert _ y).mp hy'
      rw [walkDrop_length] at hs
      rw [walkDrop_getVert] at hys
      rw [← hys]
      exact (sc.hspec a).2.2.2.2.2 (ta + s) (by omega) (by omega)
    have hqb_notS : ∀ y ∈ qb.support, y ∉ shellS T j := by
      intro y hy
      have hy' : y ∈ (walkDrop (sc.P b) tb htb_le).support := by
        simpa [qb, Walk.support_copy] using hy
      obtain ⟨s, hs, hys⟩ := (mem_support_iff_exists_getVert _ y).mp hy'
      rw [walkDrop_length] at hs
      rw [walkDrop_getVert] at hys
      rw [← hys]
      exact (sc.hspec b).2.2.2.2.2 (tb + s) (by omega) (by omega)
    rcases mem_support_append_or hxsupp with hx1 | hx2
    · rcases mem_support_append_or hx1 with hqa | hcons
      · exact hqa_notS x hqa
      · simp only [Walk.support_cons, Walk.support_nil, List.mem_cons, List.not_mem_nil, or_false] at hcons
        rcases hcons with rfl | rfl
        · exact hqa_notS a.1 (Walk.end_mem_support qa)
        · exact hqb_notS b.1 (Walk.end_mem_support qb)
    · exact hqb_notS x (mem_support_of_reverse hx2)
  exact hx_notS (mem_shellS_of_mem_T_pred T hj hxT)

lemma quotient_colorable_38 [DecidableEq V] {T : ℕ → Finset V} {j : ℕ}
    (sc : StepChoice G T j)
    (hT_hit : ∀ k v (p : G.Walk v v), Odd p.length → p.length ≤ scaleL k → ∃ x ∈ p.support, x ∈ T k)
    (hj : 2 ≤ j) (Z : Finset V)
    (hZ_notS : ∀ z ∈ Z, z ∉ shellS T j)
    (hZ_card : Z.card ≤ 256 * j ^ 3 * (scaleL (j - 1)) ^ 8) :
    (G.induce {v : V | ∃ hv : v ∈ annulusPrime G T j, ∃ z ∈ Z, z ∈ sc.intVerts ⟨v, hv⟩}).Colorable 38 := by
  classical
  let N : ℕ := scaleN (j - 1)
  have hN_ge : 2 ^ (200 + 20 * j) ≤ N := scaleN_pred_ge hj
  let AZ : Set V := {v : V | ∃ hv : v ∈ annulusPrime G T j, ∃ z ∈ Z, z ∈ sc.intVerts ⟨v, hv⟩}
  let zPick : {v // v ∈ AZ} → {z // z ∈ Z} := fun v =>
    let hz := Classical.choose v.2.choose_spec
    ⟨hz, (Classical.choose_spec v.2.choose_spec).1⟩
  have hzPick_int : ∀ v : {v // v ∈ AZ}, (zPick v).1 ∈ sc.intVerts ⟨v.1, v.2.choose⟩ :=
    fun v => (Classical.choose_spec v.2.choose_spec).2
  let QZ : SimpleGraph {z // z ∈ Z} := {
    Adj := fun z1 z2 => ∃ a b : {v // v ∈ AZ}, G.Adj a.1 b.1 ∧ zPick a = z1 ∧ zPick b = z2
    symm := ⟨by rintro z1 z2 ⟨a, b, hab, ha, hb⟩; exact ⟨b, a, hab.symm, hb, ha⟩⟩
    loopless := ⟨by
      rintro z ⟨a, b, hab, ha, hb⟩
      have hza : z.1 ∈ sc.intVerts ⟨a.1, a.2.choose⟩ := ha ▸ hzPick_int a
      have hzb : z.1 ∈ sc.intVerts ⟨b.1, b.2.choose⟩ := hb ▸ hzPick_int b
      exact Finset.disjoint_left.mp (no_internal_intersection sc hT_hit hj ⟨a.1, a.2.choose⟩ ⟨b.1, b.2.choose⟩ hab) hza hzb⟩
  }
  let mZ : {z // z ∈ Z} → ℕ := fun z =>
    if h : ∃ m ≤ j, z.1 ∈ annulus (G := G) T m then Classical.choose h else 0
  have hmZ_eq : ∀ (z : {z // z ∈ Z}) (m : ℕ), m ≤ j → z.1 ∈ annulus (G := G) T m → mZ z = m := by
    intro z m hm hzA
    have hex : ∃ m' ≤ j, z.1 ∈ annulus (G := G) T m' := ⟨m, hm, hzA⟩
    have hspec := Classical.choose_spec hex
    simp only [mZ, hex, ↓reduceDIte]
    by_contra hne
    exact annulus_disjoint T hne hspec.2 hzA
  have hQZ_lift : ∀ {z1 z2 : {z // z ∈ Z}} (w : QZ.Walk z1 z2),
      ∃ q : G.Walk z1.1 z2.1,
        (∀ x ∈ q.support, x ∉ shellS T j) ∧
        q.length % 2 = (mZ z1 + mZ z2 + w.length) % 2 ∧
        q.length ≤ (2 * j - 1) * w.length := by
    intro z1 z2 w
    induction w with
    | @nil z =>
      refine ⟨.nil, ?_, by simp; omega, by simp⟩
      intro x hx
      simp only [Walk.support_nil, List.mem_singleton] at hx
      exact hx ▸ hZ_notS z.1 z.2
    | @cons z1 z2 z3 h12 w' ih =>
      obtain ⟨a, b, hab, haZ, hbZ⟩ := h12
      obtain ⟨q', hq'S, hq'par, hq'len⟩ := ih
      have hza : z1.1 ∈ sc.intVerts ⟨a.1, a.2.choose⟩ := haZ ▸ hzPick_int a
      have hzb : z2.1 ∈ sc.intVerts ⟨b.1, b.2.choose⟩ := hbZ ▸ hzPick_int b
      obtain ⟨ta, hta1, hta_le, hza_eq⟩ := (sc.intVerts_mem ⟨a.1, a.2.choose⟩ z1.1).mp hza
      obtain ⟨tb, htb1, htb_le, hzb_eq⟩ := (sc.intVerts_mem ⟨b.1, b.2.choose⟩ z2.1).mp hzb
      have hzaA : z1.1 ∈ annulus (G := G) T (sc.mU ⟨a.1, a.2.choose⟩ + ta) :=
        hza_eq ▸ (sc.hspec ⟨a.1, a.2.choose⟩).2.2.2.2.1 ta hta_le
      have hzbA : z2.1 ∈ annulus (G := G) T (sc.mU ⟨b.1, b.2.choose⟩ + tb) :=
        hzb_eq ▸ (sc.hspec ⟨b.1, b.2.choose⟩).2.2.2.2.1 tb htb_le
      have hma_le : sc.mU ⟨a.1, a.2.choose⟩ + ta ≤ j := by
        have := (sc.hspec ⟨a.1, a.2.choose⟩).2.2.2.1; omega
      have hmb_le : sc.mU ⟨b.1, b.2.choose⟩ + tb ≤ j := by
        have := (sc.hspec ⟨b.1, b.2.choose⟩).2.2.2.1; omega
      have hmZ1 : mZ z1 = sc.mU ⟨a.1, a.2.choose⟩ + ta := hmZ_eq z1 _ hma_le hzaA
      have hmZ2 : mZ z2 = sc.mU ⟨b.1, b.2.choose⟩ + tb := hmZ_eq z2 _ hmb_le hzbA
      let qa : G.Walk z1.1 a.1 := (walkDrop (sc.P ⟨a.1, a.2.choose⟩) ta hta_le).copy hza_eq rfl
      let qb : G.Walk z2.1 b.1 := (walkDrop (sc.P ⟨b.1, b.2.choose⟩) tb htb_le).copy hzb_eq rfl
      let qstep : G.Walk z1.1 z2.1 := (qa.append (.cons hab .nil)).append qb.reverse
      have hqa_len : qa.length = j - mZ z1 := by
        rw [hmZ1]
        simp [qa, Walk.length_copy, walkDrop_length, (sc.hspec ⟨a.1, a.2.choose⟩).2.2.2.1]
        omega
      have hqb_len : qb.length = j - mZ z2 := by
        rw [hmZ2]
        simp [qb, Walk.length_copy, walkDrop_length, (sc.hspec ⟨b.1, b.2.choose⟩).2.2.2.1]
        omega
      have hqstep_len : qstep.length = (j - mZ z1) + 1 + (j - mZ z2) := by
        simp [qstep, Walk.length_append, Walk.length_reverse, hqa_len, hqb_len]
      have hmZ1_ge1 : 1 ≤ mZ z1 := by omega
      have hmZ2_ge1 : 1 ≤ mZ z2 := by omega
      have hqstep_le : qstep.length ≤ 2 * j - 1 := by omega
      have hqstep_notS : ∀ x ∈ qstep.support, x ∉ shellS T j := by
        have hqa_notS : ∀ y ∈ qa.support, y ∉ shellS T j := by
          intro y hy
          have hy' : y ∈ (walkDrop (sc.P ⟨a.1, a.2.choose⟩) ta hta_le).support := by
            simpa [qa, Walk.support_copy] using hy
          obtain ⟨s, hs, hys⟩ := (mem_support_iff_exists_getVert _ y).mp hy'
          rw [walkDrop_length] at hs
          rw [walkDrop_getVert] at hys
          rw [← hys]
          exact (sc.hspec ⟨a.1, a.2.choose⟩).2.2.2.2.2 (ta + s) (by omega) (by omega)
        have hqb_notS : ∀ y ∈ qb.support, y ∉ shellS T j := by
          intro y hy
          have hy' : y ∈ (walkDrop (sc.P ⟨b.1, b.2.choose⟩) tb htb_le).support := by
            simpa [qb, Walk.support_copy] using hy
          obtain ⟨s, hs, hys⟩ := (mem_support_iff_exists_getVert _ y).mp hy'
          rw [walkDrop_length] at hs
          rw [walkDrop_getVert] at hys
          rw [← hys]
          exact (sc.hspec ⟨b.1, b.2.choose⟩).2.2.2.2.2 (tb + s) (by omega) (by omega)
        intro x hx
        rcases mem_support_append_or hx with h1 | h2
        · rcases mem_support_append_or h1 with hqa | hcons
          · exact hqa_notS x hqa
          · simp only [Walk.support_cons, Walk.support_nil, List.mem_cons, List.not_mem_nil, or_false] at hcons
            rcases hcons with rfl | rfl
            · exact hqa_notS a.1 (Walk.end_mem_support qa)
            · exact hqb_notS b.1 (Walk.end_mem_support qb)
        · exact hqb_notS x (mem_support_of_reverse h2)
      refine ⟨qstep.append q', ?_, ?_, ?_⟩
      · intro x hx
        rcases mem_support_append_or hx with h1 | h2
        · exact hqstep_notS x h1
        · exact hq'S x h2
      · rw [Walk.length_append, Walk.length_cons, hqstep_len]
        omega
      · rw [Walk.length_append, Walk.length_cons]
        calc qstep.length + q'.length ≤ (2 * j - 1) + (2 * j - 1) * w'.length := Nat.add_le_add hqstep_le hq'len
          _ = (2 * j - 1) * (w'.length + 1) := by ring
  have hQZ_col : QZ.Colorable 38 := by
    apply colorable_38_of_poly_bound QZ hj hN_ge
    · rw [Fintype.card_coe]
      exact hZ_card
    · intro z w hw
      obtain ⟨q, hqS, hqpar, hqlen⟩ := hQZ_lift w
      have hqodd : Odd q.length := by
        obtain ⟨r, hr⟩ := hw
        refine ⟨q.length / 2, ?_⟩
        omega
      by_contra hle
      push Not at hle
      have hqle : q.length ≤ scaleL (j - 1) := le_trans hqlen hle
      obtain ⟨x, hxsupp, hxT⟩ := hT_hit (j - 1) z.1 q hqodd hqle
      exact hqS x hxsupp (mem_shellS_of_mem_T_pred T hj hxT)
  obtain ⟨c⟩ := hQZ_col
  refine ⟨Coloring.mk (fun v => c (zPick v)) ?_⟩
  intro a b hab
  exact c.valid ⟨a, b, hab, rfl, rfl⟩

lemma exists_piece1_clean [DecidableEq V]
    (hG : ∀ n : ℕ, (Erdos74.SimpleGraph.maxSubgraphEdgeDistToBipartite G n : ℝ) ≤ (n : ℝ).sqrt)
    {T : ℕ → Finset V} {j : ℕ}
    (sc : StepChoice G T j)
    (hT_card : ∀ k, (T k).card ≤ (scaleL k) ^ 2)
    (hj : 2 ≤ j) :
    ∃ X : Finset V,
      (∀ z ∈ X, z ∉ shellS T j) ∧
      X.card ≤ 256 * j ^ 3 * (scaleL (j - 1)) ^ 8 ∧
      ∀ a b : {x // x ∈ annulusPrime G T j},
        a.1 ∉ ({v : V | ∃ hv : v ∈ annulusPrime G T j, ∃ z ∈ X, z ∈ sc.intVerts ⟨v, hv⟩} : Set V) →
        b.1 ∉ ({v : V | ∃ hv : v ∈ annulusPrime G T j, ∃ z ∈ X, z ∈ sc.intVerts ⟨v, hv⟩} : Set V) →
        sc.u0 a = sc.u0 b → ¬ G.Adj a.1 b.1 := by
  classical
  let L : ℕ := scaleL (j - 1)
  have h2j_le_L : 2 * j ≤ L := scaleL_gt_two_j hj
  have hS_card : (shellS T j).card ≤ 2 * L ^ 2 := shellS_card_le T hT_card hj
  let PackX : V → ℕ → Prop := fun u k =>
    ∃ (ab : Fin k → {x // x ∈ annulusPrime G T j} × {x // x ∈ annulusPrime G T j}),
      (∀ i, sc.u0 (ab i).1 = u ∧ sc.u0 (ab i).2 = u ∧ G.Adj (ab i).1.1 (ab i).2.1) ∧
      (∀ i1 i2, i1 ≠ i2 →
        Disjoint (sc.intVerts (ab i1).1 ∪ sc.intVerts (ab i1).2)
                 (sc.intVerts (ab i2).1 ∪ sc.intVerts (ab i2).2))
  have hPackX_bound : ∀ u k, PackX u k → k ≤ 2 * j - 1 := by
    rintro u k ⟨ab, hab, hdisj⟩
    let cyc : Fin k → Σ v : V, G.Walk v v := fun i =>
      ⟨u, (((sc.P (ab i).1).copy (hab i).1 rfl).append (.cons (hab i).2.2 .nil)).append
            (((sc.P (ab i).2).copy (hab i).2.1 rfl).reverse)⟩
    let Uset : Finset V := insert u (Finset.univ.biUnion fun i => sc.intVerts (ab i).1 ∪ sc.intVerts (ab i).2)
    have hUcard : Uset.card ≤ 1 + k * (2 * (j - 1)) := by
      calc Uset.card ≤ (Finset.univ.biUnion fun i => sc.intVerts (ab i).1 ∪ sc.intVerts (ab i).2).card + 1 :=
            Finset.card_insert_le _ _
        _ = 1 + (Finset.univ.biUnion fun i => sc.intVerts (ab i).1 ∪ sc.intVerts (ab i).2).card := Nat.add_comm _ _
        _ ≤ 1 + ∑ i : Fin k, (sc.intVerts (ab i).1 ∪ sc.intVerts (ab i).2).card :=
            Nat.add_le_add_left Finset.card_biUnion_le 1
        _ ≤ 1 + ∑ _i : Fin k, (2 * (j - 1)) := by
            refine Nat.add_le_add_left (Finset.sum_le_sum fun i _ => ?_) 1
            have h1 := sc.intVerts_card (ab i).1
            have h2 := sc.intVerts_card (ab i).2
            have hu := Finset.card_union_le (sc.intVerts (ab i).1) (sc.intVerts (ab i).2)
            omega
        _ = 1 + k * (2 * (j - 1)) := by simp
    have hodd : ∀ i, Odd (cyc i).2.length := by
      intro i
      have hm1 : (sc.P (ab i).1).getVert 0 = u := by simp [(hab i).1]
      have hm2 : (sc.P (ab i).2).getVert 0 = u := by simp [(hab i).2.1]
      have hA1 : u ∈ annulus (G := G) T (sc.mU (ab i).1) := by
        simpa [hm1] using (sc.hspec (ab i).1).2.2.2.2.1 0 (Nat.zero_le _)
      have hA2 : u ∈ annulus (G := G) T (sc.mU (ab i).2) := by
        simpa [hm2] using (sc.hspec (ab i).2).2.2.2.2.1 0 (Nat.zero_le _)
      have hmeq : sc.mU (ab i).1 = sc.mU (ab i).2 := by
        by_contra hne
        exact annulus_disjoint T hne hA1 hA2
      have hlen1 := (sc.hspec (ab i).1).2.2.2.1
      have hlen2 := (sc.hspec (ab i).2).2.2.2.1
      refine ⟨j - sc.mU (ab i).1, ?_⟩
      simp only [cyc, Walk.length_append, Walk.length_reverse, Walk.length_cons, Walk.length_nil,
        Walk.length_copy, hlen1, hlen2, hmeq]
      omega
    have hsupp_sub : ∀ i, ∀ z ∈ (cyc i).2.support, z = u ∨ z ∈ sc.intVerts (ab i).1 ∪ sc.intVerts (ab i).2 := by
      intro i z hz
      have hP_sub : ∀ (v : {x // x ∈ annulusPrime G T j}) (hv : sc.u0 v = u) (y : V),
          y ∈ ((sc.P v).copy hv rfl).support → y = u ∨ y ∈ sc.intVerts v := by
        intro v hv y hy
        have hy' : y ∈ (sc.P v).support := by simpa [Walk.support_copy] using hy
        obtain ⟨t, ht, hyt⟩ := (mem_support_iff_exists_getVert (sc.P v) y).mp hy'
        cases t with
        | zero =>
          simp only [Walk.getVert_zero] at hyt
          exact Or.inl (hyt.symm.trans hv)
        | succ t' =>
          exact Or.inr ((sc.intVerts_mem v y).mpr ⟨t' + 1, by omega, ht, hyt⟩)
      rcases mem_support_append_or hz with h1 | h2
      · rcases mem_support_append_or h1 with hpa | hcons
        · exact (hP_sub _ (hab i).1 z hpa).imp_right (Finset.mem_union_left _)
        · simp only [Walk.support_cons, Walk.support_nil, List.mem_cons, List.not_mem_nil, or_false] at hcons
          rcases hcons with rfl | rfl
          · exact (hP_sub _ (hab i).1 _ (Walk.end_mem_support _)).imp_right (Finset.mem_union_left _)
          · exact (hP_sub _ (hab i).2.1 _ (Walk.end_mem_support _)).imp_right (Finset.mem_union_right _)
      · exact (hP_sub _ (hab i).2.1 z (mem_support_of_reverse h2)).imp_right (Finset.mem_union_right _)
    have hsupp : ∀ i, ∀ z ∈ (cyc i).2.support, z ∈ Uset := by
      intro i z hz
      rcases hsupp_sub i z hz with rfl | hmem
      · exact Finset.mem_insert_self z _
      · exact Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hmem⟩)
    have hedg : ∀ i1 i2, i1 ≠ i2 → ∀ e, e ∈ (cyc i1).2.edges → e ∉ (cyc i2).2.edges := by
      intro i1 i2 hne e he1 he2
      induction e using Sym2.ind with
      | _ x y =>
        have hxy : G.Adj x y := Walk.adj_of_mem_edges (cyc i1).2 he1
        have hxy_ne : x ≠ y := G.ne_of_adj hxy
        have hx1 := hsupp_sub i1 x (Walk.fst_mem_support_of_mem_edges (cyc i1).2 he1)
        have hy1 := hsupp_sub i1 y (Walk.snd_mem_support_of_mem_edges (cyc i1).2 he1)
        have hx2 := hsupp_sub i2 x (Walk.fst_mem_support_of_mem_edges (cyc i2).2 he2)
        have hy2 := hsupp_sub i2 y (Walk.snd_mem_support_of_mem_edges (cyc i2).2 he2)
        rcases hx1 with rfl | hx1'
        · have hyne : y ≠ x := hxy_ne.symm
          exact Finset.disjoint_left.mp (hdisj i1 i2 hne) (hy1.resolve_left hyne) (hy2.resolve_left hyne)
        · have hxne : x ≠ u := by
            rintro rfl
            rcases Finset.mem_union.mp hx1' with h | h
            · exact sc.intVerts_notS _ x h ((hab i1).1 ▸ (sc.hspec (ab i1).1).2.2.1)
            · exact sc.intVerts_notS _ x h ((hab i1).2.1 ▸ (sc.hspec (ab i1).2).2.2.1)
          exact Finset.disjoint_left.mp (hdisj i1 i2 hne) hx1' (hx2.resolve_left hxne)
    have hsq := disjoint_odd_walks_sq_le hG Uset cyc hodd hsupp hedg
    have h1 : k ^ 2 ≤ 1 + k * (2 * (j - 1)) := le_trans hsq hUcard
    by_contra hgt
    have hge : 2 * j ≤ k := by omega
    have hjm : 2 * (j - 1) + 2 = 2 * j := by omega
    have hmul : k * (2 * (j - 1)) + k * 2 = k * (2 * j) := by rw [← Nat.mul_add, hjm]
    nlinarith
  let maxPackX : V → ℕ := fun u =>
    let good := (Finset.range (2 * j)).filter (PackX u)
    have hne : good.Nonempty := ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),
      ⟨Fin.elim0, fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩⟩⟩
    good.max' hne
  have hmaxX_pack : ∀ u, PackX u (maxPackX u) := by
    intro u
    let good := (Finset.range (2 * j)).filter (PackX u)
    have hne : good.Nonempty := ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),
      ⟨Fin.elim0, fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩⟩⟩
    exact (Finset.mem_filter.mp (Finset.max'_mem good hne)).2
  have hmaxX_le : ∀ u, maxPackX u ≤ 2 * j - 1 := fun u => hPackX_bound u _ (hmaxX_pack u)
  let abX : ∀ u, Fin (maxPackX u) → {x // x ∈ annulusPrime G T j} × {x // x ∈ annulusPrime G T j} :=
    fun u => Classical.choose (hmaxX_pack u)
  have habX_spec : ∀ u,
      (∀ i, sc.u0 (abX u i).1 = u ∧ sc.u0 (abX u i).2 = u ∧ G.Adj (abX u i).1.1 (abX u i).2.1) ∧
      (∀ i1 i2, i1 ≠ i2 →
        Disjoint (sc.intVerts (abX u i1).1 ∪ sc.intVerts (abX u i1).2)
                 (sc.intVerts (abX u i2).1 ∪ sc.intVerts (abX u i2).2)) :=
    fun u => Classical.choose_spec (hmaxX_pack u)
  let Xu : V → Finset V := fun u =>
    Finset.univ.biUnion fun i : Fin (maxPackX u) => sc.intVerts (abX u i).1 ∪ sc.intVerts (abX u i).2
  let X : Finset V := (shellS T j).biUnion Xu
  refine ⟨X, ?_, ?_, ?_⟩
  · intro z hz
    obtain ⟨u, _, hzu⟩ := Finset.mem_biUnion.mp hz
    obtain ⟨i, _, hzi⟩ := Finset.mem_biUnion.mp hzu
    rcases Finset.mem_union.mp hzi with h1 | h2
    · exact sc.intVerts_notS _ z h1
    · exact sc.intVerts_notS _ z h2
  · have hXu_card : ∀ u, (Xu u).card ≤ 4 * j ^ 2 := by
      intro u
      calc (Xu u).card ≤ ∑ i : Fin (maxPackX u), (sc.intVerts (abX u i).1 ∪ sc.intVerts (abX u i).2).card :=
            Finset.card_biUnion_le
        _ ≤ ∑ _i : Fin (maxPackX u), (2 * (j - 1)) := by
            refine Finset.sum_le_sum fun i _ => ?_
            have h1 := sc.intVerts_card (abX u i).1
            have h2 := sc.intVerts_card (abX u i).2
            have hu := Finset.card_union_le (sc.intVerts (abX u i).1) (sc.intVerts (abX u i).2)
            omega
        _ = maxPackX u * (2 * (j - 1)) := by simp
        _ ≤ (2 * j - 1) * (2 * (j - 1)) := Nat.mul_le_mul_right _ (hmaxX_le u)
        _ ≤ (2 * j) * (2 * j) := Nat.mul_le_mul (by omega) (by omega)
        _ = 4 * j ^ 2 := by ring
    have hX1 : X.card ≤ 8 * j ^ 2 * L ^ 2 := by
      calc X.card ≤ ∑ u ∈ shellS T j, (Xu u).card := Finset.card_biUnion_le
        _ ≤ ∑ _u ∈ shellS T j, (4 * j ^ 2) := Finset.sum_le_sum fun u _ => hXu_card u
        _ = (shellS T j).card * (4 * j ^ 2) := by simp
        _ ≤ (2 * L ^ 2) * (4 * j ^ 2) := Nat.mul_le_mul_right _ hS_card
        _ = 8 * j ^ 2 * L ^ 2 := by ring
    have hL1 : 1 ≤ L := by omega
    have hL2 : L ^ 2 ≤ L ^ 8 := Nat.pow_le_pow_right hL1 (by norm_num)
    have hj2 : 8 * j ^ 2 ≤ 256 * j ^ 3 := by nlinarith
    exact le_trans hX1 (Nat.mul_le_mul hj2 hL2)
  · intro a b ha hb hu_eq hab
    let u := sc.u0 a
    have ha_disj : Disjoint (sc.intVerts a) (Xu u) := by
      rw [Finset.disjoint_left]
      intro z hza hzu
      exact ha ⟨a.2, z, Finset.mem_biUnion.mpr ⟨u, (sc.hspec a).2.2.1, hzu⟩, hza⟩
    have hb_disj : Disjoint (sc.intVerts b) (Xu u) := by
      rw [Finset.disjoint_left]
      intro z hzb hzu
      exact hb ⟨b.2, z, Finset.mem_biUnion.mpr ⟨u, (sc.hspec a).2.2.1, hzu⟩, hzb⟩
    have hPackSucc : PackX u (maxPackX u + 1) := by
      let ab' : Fin (maxPackX u + 1) → {x // x ∈ annulusPrime G T j} × {x // x ∈ annulusPrime G T j} :=
        fun i => if h : i.1 < maxPackX u then abX u ⟨i.1, h⟩ else (a, b)
      refine ⟨ab', ?_, ?_⟩
      · intro i
        by_cases hi : i.1 < maxPackX u
        · simp only [ab', hi, ↓reduceDIte]
          exact (habX_spec u).1 ⟨i.1, hi⟩
        · simp only [ab', hi, ↓reduceDIte]
          exact ⟨rfl, hu_eq.symm, hab⟩
      · intro i1 i2 hne
        by_cases h1 : i1.1 < maxPackX u <;> by_cases h2 : i2.1 < maxPackX u
        · simp only [ab', h1, h2, ↓reduceDIte]
          exact (habX_spec u).2 ⟨i1.1, h1⟩ ⟨i2.1, h2⟩
            (fun h => hne (Fin.ext (congrArg (fun x : Fin (maxPackX u) => x.1) h)))
        · simp only [ab', h1, h2, ↓reduceDIte]
          have hsub : sc.intVerts (abX u ⟨i1.1, h1⟩).1 ∪ sc.intVerts (abX u ⟨i1.1, h1⟩).2 ⊆ Xu u := by
            intro z hz
            exact Finset.mem_biUnion.mpr ⟨⟨i1.1, h1⟩, Finset.mem_univ _, hz⟩
          exact Disjoint.mono_left hsub (Finset.disjoint_union_right.mpr ⟨ha_disj.symm, hb_disj.symm⟩)
        · simp only [ab', h1, h2, ↓reduceDIte]
          have hsub : sc.intVerts (abX u ⟨i2.1, h2⟩).1 ∪ sc.intVerts (abX u ⟨i2.1, h2⟩).2 ⊆ Xu u := by
            intro z hz
            exact Finset.mem_biUnion.mpr ⟨⟨i2.1, h2⟩, Finset.mem_univ _, hz⟩
          exact Disjoint.mono_right hsub (Finset.disjoint_union_left.mpr ⟨ha_disj, hb_disj⟩)
        · exact False.elim (hne (Fin.ext (by omega)))
    have hle1 : maxPackX u + 1 ≤ 2 * j - 1 := hPackX_bound u _ hPackSucc
    let good := (Finset.range (2 * j)).filter (PackX u)
    have hmem : maxPackX u + 1 ∈ good :=
      Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hPackSucc⟩
    have hle_max : maxPackX u + 1 ≤ maxPackX u := Finset.le_max' good (maxPackX u + 1) hmem
    omega

def PackPair [DecidableEq V] {T : ℕ → Finset V} {j : ℕ}
    (sc : StepChoice G T j) (Aclean : Set V) (u w : V) (k : ℕ) : Prop :=
  ∃ (ab : Fin k → {x // x ∈ annulusPrime G T j} × {x // x ∈ annulusPrime G T j}),
    (∀ i, (ab i).1.1 ∈ Aclean ∧ (ab i).2.1 ∈ Aclean ∧
          sc.u0 (ab i).1 = u ∧ sc.u0 (ab i).2 = w ∧ G.Adj (ab i).1.1 (ab i).2.1) ∧
    (∀ i1 i2, i1 ≠ i2 →
      Disjoint (sc.intVerts (ab i1).1 ∪ sc.intVerts (ab i1).2)
               (sc.intVerts (ab i2).1 ∪ sc.intVerts (ab i2).2))

lemma packPair_symm [DecidableEq V] {T : ℕ → Finset V} {j : ℕ}
    {sc : StepChoice G T j} {Aclean : Set V} {u w : V} {k : ℕ}
    (h : PackPair sc Aclean u w k) : PackPair sc Aclean w u k := by
  obtain ⟨ab, hab, hdisj⟩ := h
  refine ⟨fun i => ((ab i).2, (ab i).1), ?_, ?_⟩
  · intro i
    obtain ⟨h1, h2, h3, h4, h5⟩ := hab i
    exact ⟨h2, h1, h4, h3, h5.symm⟩
  · intro i1 i2 hne
    simpa only [Finset.union_comm] using hdisj i1 i2 hne

def auxGraphQS [DecidableEq V] {T : ℕ → Finset V} {j : ℕ}
    (sc : StepChoice G T j) (Aclean : Set V) (M : ℕ) : SimpleGraph {u // u ∈ shellS T j} where
  Adj u w := u ≠ w ∧ PackPair sc Aclean u.1 w.1 (M + 1)
  symm := ⟨fun _ _ h => ⟨h.1.symm, packPair_symm h.2⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

lemma qs_lift_one_cycle [DecidableEq V] {T : ℕ → Finset V} {j : ℕ}
    (sc : StepChoice G T j) (Aclean : Set V) (M : ℕ)
    {ℓ : ℕ} {u_start : {u // u ∈ shellS T j}}
    (pQ : (auxGraphQS sc Aclean M).Walk u_start u_start)
    (hℓ_odd : Odd ℓ) (hplen : pQ.length = ℓ)
    (used : Finset V) (hused_lt : used.card + 2 * (j - 1) * ℓ < M + 1) :
    ∃ (q : G.Walk u_start.1 u_start.1) (intQ : Finset V),
      Odd q.length ∧
      intQ.card ≤ 2 * (j - 1) * ℓ ∧
      Disjoint intQ used ∧
      (∀ x ∈ intQ, x ∉ shellS T j) ∧
      (∀ x ∈ q.support, x ∈ shellS T j ∨ x ∈ intQ) ∧
      (∀ e ∈ q.edges, ∃ x ∈ intQ, x ∈ e) := by
  classical
  let mS : {u // u ∈ shellS T j} → ℕ := fun u =>
    if h : ∃ m ≤ j, u.1 ∈ annulus (G := G) T m then Classical.choose h else 0
  have hmS_eq : ∀ (u : {u // u ∈ shellS T j}) (m : ℕ), m ≤ j → u.1 ∈ annulus (G := G) T m → mS u = m := by
    intro u m hm huA
    have hex : ∃ m' ≤ j, u.1 ∈ annulus (G := G) T m' := ⟨m, hm, huA⟩
    have hspec := Classical.choose_spec hex
    simp only [mS, hex, ↓reduceDIte]
    by_contra hne
    exact annulus_disjoint T hne hspec.2 huA
  have hseg : ∀ (k : ℕ), k ≤ ℓ →
      ∃ (q : G.Walk u_start.1 (pQ.getVert k).1) (intQ : Finset V),
        intQ.card ≤ 2 * (j - 1) * k ∧
        Disjoint intQ used ∧
        (∀ x ∈ intQ, x ∉ shellS T j) ∧
        (∀ x ∈ q.support, x ∈ shellS T j ∨ x ∈ intQ) ∧
        (∀ e ∈ q.edges, ∃ x ∈ intQ, x ∈ e) ∧
        q.length % 2 = (mS u_start + mS (pQ.getVert k) + k) % 2 := by
    intro k
    induction k with
    | zero =>
      intro _
      let q0 : G.Walk u_start.1 (pQ.getVert 0).1 :=
        Walk.nil.copy rfl (congrArg Subtype.val (Walk.getVert_zero pQ).symm)
      refine ⟨q0, ∅, by simp, Finset.disjoint_empty_left _, by simp, ?_, ?_, ?_⟩
      · intro x hx
        have hx' : x ∈ (Walk.nil (G := G) (u := u_start.1)).support := by
          simpa [q0, Walk.support_copy] using hx
        simp only [Walk.support_nil, List.mem_singleton] at hx'
        exact Or.inl (hx' ▸ u_start.2)
      · intro e he
        simp [q0, Walk.edges_copy] at he
      · have h0 : q0.length = 0 := by simp [q0]
        rw [h0, Walk.getVert_zero]
        omega
    | succ k ih =>
      intro hk_le
      obtain ⟨q, intQ, hintQ_card, hintQ_disj, hintQ_notS, hq_supp, hq_edg, hq_par⟩ := ih (by omega)
      let u1 := pQ.getVert k
      let u2 := pQ.getVert (k + 1)
      have hadjQ : (auxGraphQS sc Aclean M).Adj u1 u2 := Walk.adj_getVert_succ pQ (by omega)
      obtain ⟨ab, hab, hdisj_ab⟩ := hadjQ.2
      let B : Fin (M + 1) → Finset V := fun i => sc.intVerts (ab i).1 ∪ sc.intVerts (ab i).2
      have hcard_lt : (used ∪ intQ).card < M + 1 := by
        have hu := Finset.card_union_le used intQ
        have hstep : 2 * (j - 1) * k ≤ 2 * (j - 1) * ℓ := Nat.mul_le_mul_left _ (by omega)
        omega
      obtain ⟨idx, hidx_disj⟩ := pigeonhole_disjoint_finsets B (used ∪ intQ) hdisj_ab hcard_lt
      let a := (ab idx).1
      let b := (ab idx).2
      have ha_u : sc.u0 a = u1.1 := (hab idx).2.2.1
      have hb_u : sc.u0 b = u2.1 := (hab idx).2.2.2.1
      have hab_adj : G.Adj a.1 b.1 := (hab idx).2.2.2.2
      let pa : G.Walk u1.1 a.1 := (sc.P a).copy ha_u rfl
      let pb : G.Walk u2.1 b.1 := (sc.P b).copy hb_u rfl
      let qstep : G.Walk u1.1 u2.1 := (pa.append (.cons hab_adj .nil)).append pb.reverse
      have hm1 : mS u1 = sc.mU a := by
        have hA1 : u1.1 ∈ annulus (G := G) T (sc.mU a) := by
          have h0 := (sc.hspec a).2.2.2.2.1 0 (Nat.zero_le _)
          simpa [Walk.getVert_zero, ha_u] using h0
        exact hmS_eq u1 (sc.mU a) (by have := (sc.hspec a).2.1; omega) hA1
      have hm2 : mS u2 = sc.mU b := by
        have hA2 : u2.1 ∈ annulus (G := G) T (sc.mU b) := by
          have h0 := (sc.hspec b).2.2.2.2.1 0 (Nat.zero_le _)
          simpa [Walk.getVert_zero, hb_u] using h0
        exact hmS_eq u2 (sc.mU b) (by have := (sc.hspec b).2.1; omega) hA2
      have hpa_len : pa.length = j - mS u1 := by
        rw [hm1]; simp [pa, Walk.length_copy, (sc.hspec a).2.2.2.1]
      have hpb_len : pb.length = j - mS u2 := by
        rw [hm2]; simp [pb, Walk.length_copy, (sc.hspec b).2.2.2.1]
      have hqstep_len : qstep.length = (j - mS u1) + 1 + (j - mS u2) := by
        simp [qstep, Walk.length_append, Walk.length_reverse, hpa_len, hpb_len]
      have hm1_le : mS u1 ≤ j := by rw [hm1]; have := (sc.hspec a).2.1; omega
      have hm2_le : mS u2 ≤ j := by rw [hm2]; have := (sc.hspec b).2.1; omega
      have hBcard : (B idx).card ≤ 2 * (j - 1) := by
        dsimp only [B]
        have h1 := sc.intVerts_card a
        have h2 := sc.intVerts_card b
        have hu := Finset.card_union_le (sc.intVerts a) (sc.intVerts b)
        dsimp only [a, b] at h1 h2 hu
        omega
      have hB_notS : ∀ x ∈ B idx, x ∉ shellS T j := by
        intro x hx
        rcases Finset.mem_union.mp hx with h1 | h2
        · exact sc.intVerts_notS a x h1
        · exact sc.intVerts_notS b x h2
      have hP_supp : ∀ (v : {x // x ∈ annulusPrime G T j}) (u : {x // x ∈ shellS T j}) (hu : sc.u0 v = u.1) (x : V),
          x ∈ ((sc.P v).copy hu rfl).support → x = u.1 ∨ x ∈ sc.intVerts v := by
        intro v u hu x hx
        have hx' : x ∈ (sc.P v).support := by simpa [Walk.support_copy] using hx
        obtain ⟨r, hr, hxr⟩ := (mem_support_iff_exists_getVert (sc.P v) x).mp hx'
        cases r with
        | zero => simp only [Walk.getVert_zero] at hxr; exact Or.inl (hxr.symm.trans hu)
        | succ r' => exact Or.inr ((sc.intVerts_mem v x).mpr ⟨r' + 1, by omega, hr, hxr⟩)
      have hqstep_supp : ∀ x ∈ qstep.support, x ∈ shellS T j ∨ x ∈ B idx := by
        intro x hx
        rcases mem_support_append_or hx with h1 | h2
        · rcases mem_support_append_or h1 with hpa | hcons
          · rcases hP_supp a u1 ha_u x hpa with rfl | hmem
            · exact Or.inl u1.2
            · exact Or.inr (Finset.mem_union_left _ hmem)
          · simp only [Walk.support_cons, Walk.support_nil, List.mem_cons, List.not_mem_nil, or_false] at hcons
            rcases hcons with rfl | rfl
            · have ha_int : a.1 ∈ sc.intVerts a := (sc.intVerts_mem a a.1).mpr
                ⟨(sc.P a).length, by have := (sc.hspec a).2.1; have := (sc.hspec a).2.2.2.1; omega, le_rfl, Walk.getVert_length (sc.P a)⟩
              exact Or.inr (Finset.mem_union_left _ ha_int)
            · have hb_int : b.1 ∈ sc.intVerts b := (sc.intVerts_mem b b.1).mpr
                ⟨(sc.P b).length, by have := (sc.hspec b).2.1; have := (sc.hspec b).2.2.2.1; omega, le_rfl, Walk.getVert_length (sc.P b)⟩
              exact Or.inr (Finset.mem_union_right _ hb_int)
        · rcases hP_supp b u2 hb_u x (mem_support_of_reverse h2) with rfl | hmem
          · exact Or.inl u2.2
          · exact Or.inr (Finset.mem_union_right _ hmem)
      have hqstep_edg : ∀ e ∈ qstep.edges, ∃ x ∈ B idx, x ∈ e := by
        have hP_edg : ∀ (v : {x // x ∈ annulusPrime G T j}) (u : {x // x ∈ shellS T j}) (hu : sc.u0 v = u.1) (e : Sym2 V),
            e ∈ ((sc.P v).copy hu rfl).edges → ∃ x ∈ sc.intVerts v, x ∈ e := by
          intro v u hu e he
          have he' : e ∈ (sc.P v).edges := by simpa [Walk.edges_copy] using he
          induction e using Sym2.ind with
          | _ x y =>
            have hxy : G.Adj x y := Walk.adj_of_mem_edges (sc.P v) he'
            have hne : x ≠ y := G.ne_of_adj hxy
            have hx := hP_supp v u hu x (by simpa [Walk.support_copy] using Walk.fst_mem_support_of_mem_edges (sc.P v) he')
            have hy := hP_supp v u hu y (by simpa [Walk.support_copy] using Walk.snd_mem_support_of_mem_edges (sc.P v) he')
            rcases hx with rfl | hx'
            · exact ⟨y, hy.resolve_left hne.symm, by simp⟩
            · exact ⟨x, hx', by simp⟩
        intro e he
        rw [Walk.edges_append, List.mem_append] at he
        rcases he with h1 | h2
        · rw [Walk.edges_append, List.mem_append] at h1
          rcases h1 with hpa | hcons
          · obtain ⟨x, hx, hxe⟩ := hP_edg a u1 ha_u e hpa
            exact ⟨x, Finset.mem_union_left _ hx, hxe⟩
          · simp only [Walk.edges_cons, Walk.edges_nil, List.mem_singleton] at hcons
            have ha_int : a.1 ∈ sc.intVerts a := (sc.intVerts_mem a a.1).mpr
              ⟨(sc.P a).length, by have := (sc.hspec a).2.1; have := (sc.hspec a).2.2.2.1; omega, le_rfl, Walk.getVert_length (sc.P a)⟩
            exact ⟨a.1, Finset.mem_union_left _ ha_int, by rw [hcons]; simp⟩
        · rw [Walk.edges_reverse, List.mem_reverse] at h2
          obtain ⟨x, hx, hxe⟩ := hP_edg b u2 hb_u e h2
          exact ⟨x, Finset.mem_union_right _ hx, hxe⟩
      refine ⟨q.append qstep, intQ ∪ B idx, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · calc (intQ ∪ B idx).card ≤ intQ.card + (B idx).card := Finset.card_union_le _ _
          _ ≤ 2 * (j - 1) * k + 2 * (j - 1) := Nat.add_le_add hintQ_card hBcard
          _ = 2 * (j - 1) * (k + 1) := by ring
      · exact Finset.disjoint_union_left.mpr ⟨hintQ_disj, (Finset.disjoint_union_right.mp hidx_disj).1⟩
      · intro x hx
        rcases Finset.mem_union.mp hx with h1 | h2
        · exact hintQ_notS x h1
        · exact hB_notS x h2
      · intro x hx
        rcases mem_support_append_or hx with h1 | h2
        · exact (hq_supp x h1).imp_right (Finset.mem_union_left _)
        · exact (hqstep_supp x h2).imp_right (Finset.mem_union_right _)
      · intro e he
        rw [Walk.edges_append, List.mem_append] at he
        rcases he with h1 | h2
        · obtain ⟨x, hx, hxe⟩ := hq_edg e h1
          exact ⟨x, Finset.mem_union_left _ hx, hxe⟩
        · obtain ⟨x, hx, hxe⟩ := hqstep_edg e h2
          exact ⟨x, Finset.mem_union_right _ hx, hxe⟩
      · dsimp only [u1, u2] at hqstep_len hm1_le hm2_le
        rw [Walk.length_append, hqstep_len]
        omega
  obtain ⟨q, intQ, hintQ_card, hintQ_disj, hintQ_notS, hq_supp, hq_edg, hq_par⟩ := hseg ℓ le_rfl
  have hend : pQ.getVert ℓ = u_start := by
    rw [← hplen]
    exact Walk.getVert_length pQ
  let qcl : G.Walk u_start.1 u_start.1 := q.copy rfl (congrArg Subtype.val hend)
  have hqcl_odd : Odd qcl.length := by
    rw [Walk.length_copy]
    have hm_end : mS (pQ.getVert ℓ) = mS u_start := congrArg mS hend
    rw [hm_end] at hq_par
    obtain ⟨r, hr⟩ := hℓ_odd
    refine ⟨q.length / 2, ?_⟩
    omega
  refine ⟨qcl, intQ, hqcl_odd, hintQ_card, hintQ_disj, hintQ_notS, ?_, ?_⟩
  · intro x hx
    exact hq_supp x (by simpa [qcl, Walk.support_copy] using hx)
  · intro e he
    exact hq_edg e (by simpa [qcl, Walk.edges_copy] using he)

lemma qs_colorable_two [DecidableEq V]
    (hG : ∀ n : ℕ, (Erdos74.SimpleGraph.maxSubgraphEdgeDistToBipartite G n : ℝ) ≤ (n : ℝ).sqrt)
    {T : ℕ → Finset V} {j : ℕ}
    (sc : StepChoice G T j) (Aclean : Set V) (hj : 2 ≤ j) :
    (auxGraphQS sc Aclean (6 * j ^ 2 * (shellS T j).card ^ 2 + 1)).Colorable 2 := by
  classical
  let s : ℕ := (shellS T j).card
  let M : ℕ := 6 * j ^ 2 * s ^ 2 + 1
  apply colorable_two_of_no_odd_walk
  intro u0_init p_init hp_odd
  obtain ⟨ℓ, u_start, pQ, hℓ_odd, hplen, hℓ_ge3, hdistinct⟩ :=
    exists_shortest_odd_walk_distinct ⟨u0_init, p_init, hp_odd⟩
  have hℓ_le_s : ℓ ≤ s := by
    let f : Fin ℓ → {u // u ∈ shellS T j} := fun i => pQ.getVert i.1
    have hinj : Function.Injective f := by
      intro a b hab
      by_contra hne
      rcases lt_or_gt_of_ne (fun h => hne (Fin.ext h)) with hlt | hgt
      · exact hdistinct a.1 b.1 hlt b.isLt hab
      · exact hdistinct b.1 a.1 hgt a.isLt hab.symm
    have hcard := Fintype.card_le_of_injective f hinj
    simpa [s, Fintype.card_coe] using hcard
  have hs_ge3 : 3 ≤ s := le_trans hℓ_ge3 hℓ_le_s
  let t : ℕ := 3 * j * s
  have hiter_cyc : ∀ r : ℕ, r ≤ t →
      ∃ (w : Fin r → Σ v : V, G.Walk v v) (intR : Fin r → Finset V),
        (∀ i, Odd (w i).2.length) ∧
        (∀ i, (intR i).card ≤ 2 * (j - 1) * ℓ) ∧
        (∀ i1 i2, i1 ≠ i2 → Disjoint (intR i1) (intR i2)) ∧
        (∀ i, ∀ x ∈ intR i, x ∉ shellS T j) ∧
        (∀ i, ∀ x ∈ (w i).2.support, x ∈ shellS T j ∨ x ∈ intR i) ∧
        (∀ i, ∀ e ∈ (w i).2.edges, ∃ x ∈ intR i, x ∈ e) := by
    intro r
    induction r with
    | zero =>
      intro _
      exact ⟨Fin.elim0, Fin.elim0, fun i => Fin.elim0 i, fun i => Fin.elim0 i,
        fun i => Fin.elim0 i, fun i => Fin.elim0 i, fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩
    | succ r ih =>
      intro hr_le
      obtain ⟨w, intR, hodd, hcardR, hdisjR, hnotSR, hsuppR, hedgR⟩ := ih (by omega)
      let used : Finset V := Finset.univ.biUnion intR
      have hused_card : used.card ≤ r * (2 * (j - 1) * ℓ) := by
        calc used.card ≤ ∑ i : Fin r, (intR i).card := Finset.card_biUnion_le
          _ ≤ ∑ _i : Fin r, (2 * (j - 1) * ℓ) := Finset.sum_le_sum fun i _ => hcardR i
          _ = r * (2 * (j - 1) * ℓ) := by simp
      have hused_lt : used.card + 2 * (j - 1) * ℓ < M + 1 := by
        have h1 : used.card + 2 * (j - 1) * ℓ ≤ (r + 1) * (2 * (j - 1) * ℓ) := by
          calc used.card + 2 * (j - 1) * ℓ ≤ r * (2 * (j - 1) * ℓ) + 2 * (j - 1) * ℓ :=
                Nat.add_le_add_right hused_card _
            _ = (r + 1) * (2 * (j - 1) * ℓ) := by ring
        have h2 : (r + 1) * (2 * (j - 1) * ℓ) ≤ t * (2 * (j - 1) * s) :=
          Nat.mul_le_mul hr_le (Nat.mul_le_mul_left _ hℓ_le_s)
        have h3 : t * (2 * (j - 1) * s) < M + 1 := by
          dsimp only [t, M]
          have hle : 3 * j * s * (2 * (j - 1) * s) ≤ 6 * j ^ 2 * s ^ 2 := by
            calc 3 * j * s * (2 * (j - 1) * s) ≤ 3 * j * s * (2 * j * s) :=
                  Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (by omega)))
              _ = 6 * j ^ 2 * s ^ 2 := by ring
          omega
        omega
      obtain ⟨q, intQ, hq_odd, hq_card, hq_disj, hq_notS, hq_supp, hq_edg⟩ :=
        qs_lift_one_cycle sc Aclean M pQ hℓ_odd hplen used hused_lt
      let w' : Fin (r + 1) → Σ v : V, G.Walk v v :=
        fun i => if h : i.1 < r then w ⟨i.1, h⟩ else ⟨u_start.1, q⟩
      let intR' : Fin (r + 1) → Finset V :=
        fun i => if h : i.1 < r then intR ⟨i.1, h⟩ else intQ
      have hw'_lt : ∀ (i : Fin (r + 1)) (hi : i.1 < r), w' i = w ⟨i.1, hi⟩ := fun i hi => dif_pos hi
      have hw'_ge : ∀ (i : Fin (r + 1)) (hi : ¬ i.1 < r), w' i = ⟨u_start.1, q⟩ := fun i hi => dif_neg hi
      have hi'_lt : ∀ (i : Fin (r + 1)) (hi : i.1 < r), intR' i = intR ⟨i.1, hi⟩ := fun i hi => dif_pos hi
      have hi'_ge : ∀ (i : Fin (r + 1)) (hi : ¬ i.1 < r), intR' i = intQ := fun i hi => dif_neg hi
      refine ⟨w', intR', ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro i
        by_cases hi : i.1 < r
        · rw [hw'_lt i hi]; exact hodd ⟨i.1, hi⟩
        · rw [hw'_ge i hi]; exact hq_odd
      · intro i
        by_cases hi : i.1 < r
        · rw [hi'_lt i hi]; exact hcardR ⟨i.1, hi⟩
        · rw [hi'_ge i hi]; exact hq_card
      · intro i1 i2 hne
        by_cases h1 : i1.1 < r <;> by_cases h2 : i2.1 < r
        · rw [hi'_lt i1 h1, hi'_lt i2 h2]
          exact hdisjR _ _ (fun h => hne (Fin.ext (congrArg (fun x : Fin r => x.1) h)))
        · rw [hi'_lt i1 h1, hi'_ge i2 h2]
          exact Disjoint.mono_left (Finset.subset_biUnion_of_mem intR (Finset.mem_univ _)) hq_disj.symm
        · rw [hi'_ge i1 h1, hi'_lt i2 h2]
          exact Disjoint.mono_right (Finset.subset_biUnion_of_mem intR (Finset.mem_univ _)) hq_disj
        · exact False.elim (hne (Fin.ext (by omega)))
      · intro i
        by_cases hi : i.1 < r
        · rw [hi'_lt i hi]; exact hnotSR ⟨i.1, hi⟩
        · rw [hi'_ge i hi]; exact hq_notS
      · intro i
        by_cases hi : i.1 < r
        · rw [hw'_lt i hi, hi'_lt i hi]; exact hsuppR ⟨i.1, hi⟩
        · rw [hw'_ge i hi, hi'_ge i hi]; exact hq_supp
      · intro i
        by_cases hi : i.1 < r
        · rw [hw'_lt i hi, hi'_lt i hi]; exact hedgR ⟨i.1, hi⟩
        · rw [hw'_ge i hi, hi'_ge i hi]; exact hq_edg
  obtain ⟨w, intR, hodd, hcardR, hdisjR, hnotSR, hsuppR, hedgR⟩ := hiter_cyc t le_rfl
  let Uall : Finset V := shellS T j ∪ Finset.univ.biUnion intR
  have hUall_card : Uall.card < t ^ 2 := by
    have h1 : Uall.card ≤ s + t * (2 * (j - 1) * ℓ) := by
      calc Uall.card ≤ (shellS T j).card + (Finset.univ.biUnion intR).card := Finset.card_union_le _ _
        _ ≤ s + ∑ i : Fin t, (intR i).card := Nat.add_le_add_left Finset.card_biUnion_le s
        _ ≤ s + ∑ _i : Fin t, (2 * (j - 1) * ℓ) := Nat.add_le_add_left (Finset.sum_le_sum fun i _ => hcardR i) s
        _ = s + t * (2 * (j - 1) * ℓ) := by simp
    have h2 : t * (2 * (j - 1) * ℓ) ≤ 6 * j ^ 2 * s ^ 2 := by
      have hle1 : 2 * (j - 1) * ℓ ≤ 2 * j * s := Nat.mul_le_mul (by omega) hℓ_le_s
      calc t * (2 * (j - 1) * ℓ) ≤ t * (2 * j * s) := Nat.mul_le_mul_left t hle1
        _ = 6 * j ^ 2 * s ^ 2 := by dsimp only [t]; ring
    have h3 : t ^ 2 = 9 * j ^ 2 * s ^ 2 := by dsimp only [t]; ring
    have hs_lt : s < 3 * j ^ 2 * s ^ 2 := by
      have h1 : 1 ≤ 3 * j ^ 2 := by nlinarith
      have h2 : s < s ^ 2 := by nlinarith
      have h3' : s ^ 2 ≤ 3 * j ^ 2 * s ^ 2 := Nat.le_mul_of_pos_left _ (by omega)
      omega
    have hsum : 3 * j ^ 2 * s ^ 2 + 6 * j ^ 2 * s ^ 2 = 9 * j ^ 2 * s ^ 2 := by ring
    omega
  have hUall_supp : ∀ i, ∀ z ∈ (w i).2.support, z ∈ Uall := by
    intro i z hz
    rcases hsuppR i z hz with hS | hI
    · exact Finset.mem_union_left _ hS
    · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hI⟩)
  have hUall_edg : ∀ i1 i2, i1 ≠ i2 → ∀ e, e ∈ (w i1).2.edges → e ∉ (w i2).2.edges := by
    intro i1 i2 hne e he1 he2
    obtain ⟨x, hx1, hxe⟩ := hedgR i1 e he1
    have hx_supp2 : x ∈ (w i2).2.support := by
      induction e using Sym2.ind with
      | _ a b =>
        simp only [Sym2.mem_iff] at hxe
        rcases hxe with rfl | rfl
        · exact Walk.fst_mem_support_of_mem_edges (w i2).2 he2
        · exact Walk.snd_mem_support_of_mem_edges (w i2).2 he2
    rcases hsuppR i2 x hx_supp2 with hxS | hx2
    · exact hnotSR i1 x hx1 hxS
    · exact Finset.disjoint_left.mp (hdisjR i1 i2 hne) hx1 hx2
  have hsq := disjoint_odd_walks_sq_le hG Uall w hodd hUall_supp hUall_edg
  omega

lemma exists_piece2_bip [DecidableEq V]
    (hG : ∀ n : ℕ, (Erdos74.SimpleGraph.maxSubgraphEdgeDistToBipartite G n : ℝ) ≤ (n : ℝ).sqrt)
    {T : ℕ → Finset V} {j : ℕ}
    (sc : StepChoice G T j)
    (hT_card : ∀ k, (T k).card ≤ (scaleL k) ^ 2)
    (hj : 2 ≤ j) (Aclean : Set V)
    (hAclean_sub : Aclean ⊆ annulusPrime G T j)
    (hclean_indep : ∀ a b : {x // x ∈ annulusPrime G T j},
      a.1 ∈ Aclean → b.1 ∈ Aclean → sc.u0 a = sc.u0 b → ¬ G.Adj a.1 b.1) :
    ∃ Y : Finset V,
      (∀ z ∈ Y, z ∉ shellS T j) ∧
      Y.card ≤ 256 * j ^ 3 * (scaleL (j - 1)) ^ 8 ∧
      (G.induce (Aclean \ {v : V | ∃ hv : v ∈ annulusPrime G T j, ∃ z ∈ Y, z ∈ sc.intVerts ⟨v, hv⟩})).Colorable 2 := by
  classical
  let L : ℕ := scaleL (j - 1)
  let s : ℕ := (shellS T j).card
  let M : ℕ := 6 * j ^ 2 * s ^ 2 + 1
  have hS_card : s ≤ 2 * L ^ 2 := shellS_card_le T hT_card hj
  let maxPair : V → V → ℕ := fun u w =>
    let good := (Finset.range (M + 2)).filter (PackPair sc Aclean u w)
    have hne : good.Nonempty := ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),
      ⟨Fin.elim0, fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩⟩⟩
    good.max' hne
  have hmaxPair_pack : ∀ u w, PackPair sc Aclean u w (maxPair u w) := by
    intro u w
    let good := (Finset.range (M + 2)).filter (PackPair sc Aclean u w)
    have hne : good.Nonempty := ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),
      ⟨Fin.elim0, fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩⟩⟩
    exact (Finset.mem_filter.mp (Finset.max'_mem good hne)).2
  let abP : ∀ u w, Fin (maxPair u w) → {x // x ∈ annulusPrime G T j} × {x // x ∈ annulusPrime G T j} :=
    fun u w => Classical.choose (hmaxPair_pack u w)
  have habP_spec : ∀ u w,
      (∀ i, (abP u w i).1.1 ∈ Aclean ∧ (abP u w i).2.1 ∈ Aclean ∧
            sc.u0 (abP u w i).1 = u ∧ sc.u0 (abP u w i).2 = w ∧ G.Adj (abP u w i).1.1 (abP u w i).2.1) ∧
      (∀ i1 i2, i1 ≠ i2 →
        Disjoint (sc.intVerts (abP u w i1).1 ∪ sc.intVerts (abP u w i1).2)
                 (sc.intVerts (abP u w i2).1 ∪ sc.intVerts (abP u w i2).2)) :=
    fun u w => Classical.choose_spec (hmaxPair_pack u w)
  let Ypair : V × V → Finset V := fun uw =>
    if PackPair sc Aclean uw.1 uw.2 (M + 1) then ∅
    else Finset.univ.biUnion fun i : Fin (maxPair uw.1 uw.2) =>
      sc.intVerts (abP uw.1 uw.2 i).1 ∪ sc.intVerts (abP uw.1 uw.2 i).2
  let Y : Finset V := (shellS T j ×ˢ shellS T j).biUnion Ypair
  refine ⟨Y, ?_, ?_, ?_⟩
  · intro z hz
    obtain ⟨uw, _, hzuw⟩ := Finset.mem_biUnion.mp hz
    dsimp only [Ypair] at hzuw
    split_ifs at hzuw with h
    · simp at hzuw
    · obtain ⟨i, _, hzi⟩ := Finset.mem_biUnion.mp hzuw
      rcases Finset.mem_union.mp hzi with h1 | h2
      · exact sc.intVerts_notS _ z h1
      · exact sc.intVerts_notS _ z h2
  · have hYpair_card : ∀ uw : V × V, (Ypair uw).card ≤ 2 * (j - 1) * M := by
      intro uw
      dsimp only [Ypair]
      split_ifs with h
      · simp
      · have hleM : maxPair uw.1 uw.2 ≤ M := by
          let good := (Finset.range (M + 2)).filter (PackPair sc Aclean uw.1 uw.2)
          have hne : good.Nonempty := ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),
            ⟨Fin.elim0, fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩⟩⟩
          have hlt : maxPair uw.1 uw.2 < M + 2 :=
            Finset.mem_range.mp (Finset.mem_filter.mp (Finset.max'_mem good hne)).1
          have hneM1 : maxPair uw.1 uw.2 ≠ M + 1 := fun heq => h (heq ▸ hmaxPair_pack uw.1 uw.2)
          omega
        calc (Finset.univ.biUnion fun i : Fin (maxPair uw.1 uw.2) =>
                sc.intVerts (abP uw.1 uw.2 i).1 ∪ sc.intVerts (abP uw.1 uw.2 i).2).card
            ≤ ∑ i : Fin (maxPair uw.1 uw.2), (sc.intVerts (abP uw.1 uw.2 i).1 ∪ sc.intVerts (abP uw.1 uw.2 i).2).card :=
              Finset.card_biUnion_le
          _ ≤ ∑ _i : Fin (maxPair uw.1 uw.2), (2 * (j - 1)) := by
              refine Finset.sum_le_sum fun i _ => ?_
              have h1 := sc.intVerts_card (abP uw.1 uw.2 i).1
              have h2 := sc.intVerts_card (abP uw.1 uw.2 i).2
              have hu := Finset.card_union_le (sc.intVerts (abP uw.1 uw.2 i).1) (sc.intVerts (abP uw.1 uw.2 i).2)
              omega
          _ = maxPair uw.1 uw.2 * (2 * (j - 1)) := by simp
          _ ≤ M * (2 * (j - 1)) := Nat.mul_le_mul_right _ hleM
          _ = 2 * (j - 1) * M := by ring
    calc Y.card ≤ ∑ uw ∈ shellS T j ×ˢ shellS T j, (Ypair uw).card := Finset.card_biUnion_le
      _ ≤ ∑ _uw ∈ shellS T j ×ˢ shellS T j, (2 * (j - 1) * M) := Finset.sum_le_sum fun uw _ => hYpair_card uw
      _ = s ^ 2 * (2 * (j - 1) * M) := by simp [s, sq]
      _ ≤ 256 * j ^ 3 * L ^ 8 := by
          rcases Nat.eq_zero_or_pos s with hs0 | hspos
          · simp [hs0]
          · have hM_le : M ≤ 7 * j ^ 2 * s ^ 2 := by
              have h1 : 1 ≤ j ^ 2 * s ^ 2 := Nat.mul_pos (by positivity) (by positivity)
              have hsum : 6 * j ^ 2 * s ^ 2 + j ^ 2 * s ^ 2 = 7 * j ^ 2 * s ^ 2 := by ring
              dsimp only [M]
              omega
            have hs4 : s ^ 4 ≤ 16 * L ^ 8 := by
              have h1 : s ^ 4 ≤ (2 * L ^ 2) ^ 4 := Nat.pow_le_pow_left hS_card 4
              calc s ^ 4 ≤ (2 * L ^ 2) ^ 4 := h1
                _ = 16 * L ^ 8 := by ring
            calc s ^ 2 * (2 * (j - 1) * M)
                ≤ s ^ 2 * (2 * j * (7 * j ^ 2 * s ^ 2)) := by
                  apply Nat.mul_le_mul_left
                  exact Nat.mul_le_mul (by omega) hM_le
              _ = 14 * j ^ 3 * s ^ 4 := by ring
              _ ≤ 14 * j ^ 3 * (16 * L ^ 8) := Nat.mul_le_mul_left _ hs4
              _ = 224 * (j ^ 3 * L ^ 8) := by ring
              _ ≤ 256 * (j ^ 3 * L ^ 8) := Nat.mul_le_mul_right _ (by omega)
              _ = 256 * j ^ 3 * L ^ 8 := by ring
  · obtain ⟨cQ⟩ := qs_colorable_two hG sc Aclean hj
    refine ⟨Coloring.mk (fun v => cQ ⟨sc.u0 ⟨v.1, hAclean_sub v.2.1⟩, (sc.hspec ⟨v.1, hAclean_sub v.2.1⟩).2.2.1⟩) ?_⟩
    intro a b hab
    let a' : {x // x ∈ annulusPrime G T j} := ⟨a.1, hAclean_sub a.2.1⟩
    let b' : {x // x ∈ annulusPrime G T j} := ⟨b.1, hAclean_sub b.2.1⟩
    have hu_ne : sc.u0 a' ≠ sc.u0 b' := fun heq => hclean_indep a' b' a.2.1 b.2.1 heq hab
    have hpack : PackPair sc Aclean (sc.u0 a') (sc.u0 b') (M + 1) := by
      by_contra hnot
      let uw : V × V := (sc.u0 a', sc.u0 b')
      have huw_mem : uw ∈ shellS T j ×ˢ shellS T j :=
        Finset.mem_product.mpr ⟨(sc.hspec a').2.2.1, (sc.hspec b').2.2.1⟩
      have hdisj_a : Disjoint (sc.intVerts a') (Ypair uw) := by
        rw [Finset.disjoint_left]
        intro z hza hzy
        exact a.2.2 ⟨a'.2, z, Finset.mem_biUnion.mpr ⟨uw, huw_mem, hzy⟩, hza⟩
      have hdisj_b : Disjoint (sc.intVerts b') (Ypair uw) := by
        rw [Finset.disjoint_left]
        intro z hzb hzy
        exact b.2.2 ⟨b'.2, z, Finset.mem_biUnion.mpr ⟨uw, huw_mem, hzy⟩, hzb⟩
      have hYpair_eq : Ypair uw = Finset.univ.biUnion fun i : Fin (maxPair uw.1 uw.2) =>
          sc.intVerts (abP uw.1 uw.2 i).1 ∪ sc.intVerts (abP uw.1 uw.2 i).2 := by
        simp [Ypair, uw, hnot]
      have hPackSucc : PackPair sc Aclean uw.1 uw.2 (maxPair uw.1 uw.2 + 1) := by
        let ab' : Fin (maxPair uw.1 uw.2 + 1) → {x // x ∈ annulusPrime G T j} × {x // x ∈ annulusPrime G T j} :=
          fun i => if h : i.1 < maxPair uw.1 uw.2 then abP uw.1 uw.2 ⟨i.1, h⟩ else (a', b')
        refine ⟨ab', ?_, ?_⟩
        · intro i
          by_cases hi : i.1 < maxPair uw.1 uw.2
          · simp only [ab', hi, ↓reduceDIte]
            exact (habP_spec uw.1 uw.2).1 ⟨i.1, hi⟩
          · simp only [ab', hi, ↓reduceDIte]
            exact ⟨a.2.1, b.2.1, rfl, rfl, hab⟩
        · intro i1 i2 hne
          by_cases h1 : i1.1 < maxPair uw.1 uw.2 <;> by_cases h2 : i2.1 < maxPair uw.1 uw.2
          · simp only [ab', h1, h2, ↓reduceDIte]
            exact (habP_spec uw.1 uw.2).2 ⟨i1.1, h1⟩ ⟨i2.1, h2⟩
              (fun h => hne (Fin.ext (congrArg (fun x : Fin (maxPair uw.1 uw.2) => x.1) h)))
          · simp only [ab', h1, h2, ↓reduceDIte]
            have hsub : sc.intVerts (abP uw.1 uw.2 ⟨i1.1, h1⟩).1 ∪ sc.intVerts (abP uw.1 uw.2 ⟨i1.1, h1⟩).2 ⊆ Ypair uw := by
              rw [hYpair_eq]
              intro z hz
              exact Finset.mem_biUnion.mpr ⟨⟨i1.1, h1⟩, Finset.mem_univ _, hz⟩
            exact Disjoint.mono_left hsub (Finset.disjoint_union_right.mpr ⟨hdisj_a.symm, hdisj_b.symm⟩)
          · simp only [ab', h1, h2, ↓reduceDIte]
            have hsub : sc.intVerts (abP uw.1 uw.2 ⟨i2.1, h2⟩).1 ∪ sc.intVerts (abP uw.1 uw.2 ⟨i2.1, h2⟩).2 ⊆ Ypair uw := by
              rw [hYpair_eq]
              intro z hz
              exact Finset.mem_biUnion.mpr ⟨⟨i2.1, h2⟩, Finset.mem_univ _, hz⟩
            exact Disjoint.mono_right hsub (Finset.disjoint_union_left.mpr ⟨hdisj_a, hdisj_b⟩)
          · exact False.elim (hne (Fin.ext (by omega)))
      have hleM : maxPair uw.1 uw.2 ≤ M := by
        let good := (Finset.range (M + 2)).filter (PackPair sc Aclean uw.1 uw.2)
        have hne : good.Nonempty := ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),
          ⟨Fin.elim0, fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩⟩⟩
        have hlt : maxPair uw.1 uw.2 < M + 2 :=
          Finset.mem_range.mp (Finset.mem_filter.mp (Finset.max'_mem good hne)).1
        have hneM1 : maxPair uw.1 uw.2 ≠ M + 1 := fun heq => hnot (heq ▸ hmaxPair_pack uw.1 uw.2)
        omega
      let good := (Finset.range (M + 2)).filter (PackPair sc Aclean uw.1 uw.2)
      have hmem : maxPair uw.1 uw.2 + 1 ∈ good :=
        Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hPackSucc⟩
      have hle_max : maxPair uw.1 uw.2 + 1 ≤ maxPair uw.1 uw.2 :=
        Finset.le_max' good (maxPair uw.1 uw.2 + 1) hmem
      omega
    exact cQ.valid ⟨fun h => hu_ne (congrArg Subtype.val h), hpack⟩

lemma annulus_colorable_116
    (hG : ∀ n : ℕ, (Erdos74.SimpleGraph.maxSubgraphEdgeDistToBipartite G n : ℝ) ≤ (n : ℝ).sqrt)
    (T : ℕ → Finset V)
    (hT_card : ∀ k, (T k).card ≤ (scaleL k) ^ 2)
    (hT_hit : ∀ k v (p : G.Walk v v), Odd p.length → p.length ≤ scaleL k → ∃ x ∈ p.support, x ∈ T k)
    {j : ℕ} (hj : 2 ≤ j) :
    (G.induce (annulus (G := G) T j)).Colorable 116 := by
  classical
  let sc := mkStepChoice (G := G) T hj
  let A0 : Set V := annulus (G := G) T j ∩ (T j : Set V)
  have hA0_col : (G.induce A0).Colorable 38 := piece0_colorable_38 T hT_card hT_hit hj
  obtain ⟨X, hX_notS, hX_card, hclean_indep⟩ := exists_piece1_clean hG sc hT_card hj
  let AX : Set V := {v : V | ∃ hv : v ∈ annulusPrime G T j, ∃ z ∈ X, z ∈ sc.intVerts ⟨v, hv⟩}
  have hAX_col : (G.induce AX).Colorable 38 := quotient_colorable_38 sc hT_hit hj X hX_notS hX_card
  let Aclean : Set V := annulusPrime G T j \ AX
  obtain ⟨Y, hY_notS, hY_card, hAbip_col⟩ :=
    exists_piece2_bip hG sc hT_card hj Aclean Set.sdiff_subset (fun a b ha hb => hclean_indep a b ha.2 hb.2)
  let AY : Set V := {v : V | ∃ hv : v ∈ annulusPrime G T j, ∃ z ∈ Y, z ∈ sc.intVerts ⟨v, hv⟩}
  have hAY_col : (G.induce AY).Colorable 38 := quotient_colorable_38 sc hT_hit hj Y hY_notS hY_card
  have hsub_all : annulus (G := G) T j ⊆ ((A0 ∪ AX) ∪ AY) ∪ (Aclean \ AY) := by
    intro x hx
    by_cases hxT : x ∈ T j
    · exact Or.inl (Or.inl (Or.inl ⟨hx, hxT⟩))
    · have hx' : x ∈ annulusPrime G T j := ⟨hx, hxT⟩
      by_cases hxX : x ∈ AX
      · exact Or.inl (Or.inl (Or.inr hxX))
      · by_cases hxY : x ∈ AY
        · exact Or.inl (Or.inr hxY)
        · exact Or.inr ⟨⟨hx', hxX⟩, hxY⟩
  apply colorable_of_subset hsub_all
  have h1 := colorable_union_sets hA0_col hAX_col
  have h2 := colorable_union_sets h1 hAY_col
  exact colorable_union_sets h2 hAbip_col

lemma finite_chromatic_of_sqrt_bound
    (hG : ∀ n : ℕ, (Erdos74.SimpleGraph.maxSubgraphEdgeDistToBipartite G n : ℝ) ≤ (n : ℝ).sqrt) :
    ∃ K : ℕ, G.Colorable K := by
  classical
  let T : ℕ → Finset V := fun k => Classical.choose (exists_odd_walk_transversal hG (scaleL k))
  have hT_card : ∀ k, (T k).card ≤ (scaleL k) ^ 2 :=
    fun k => (Classical.choose_spec (exists_odd_walk_transversal hG (scaleL k))).1
  have hT_hit : ∀ k v (p : G.Walk v v), Odd p.length → p.length ≤ scaleL k → ∃ x ∈ p.support, x ∈ T k :=
    fun k => (Classical.choose_spec (exists_odd_walk_transversal hG (scaleL k))).2
  let Vhi : Set V := ⋃ i : ℕ, annulus (G := G) T (i + 2)
  have hVhi_col : (G.induce Vhi).Colorable (116 + 116) := by
    apply colorable_biUnion_nat_parity (fun i => annulus (G := G) T (i + 2))
    · intro i
      exact annulus_colorable_116 hG T hT_card hT_hit (by omega)
    · intro a b hab x hx y hy
      exact annulus_no_skip T (by omega) hx hy
  let Vrest : Set V := (⋃ j : ℕ, shells (G := G) T j)ᶜ
  have hVrest_col : (G.induce Vrest).Colorable 2 := by
    apply colorable_two_of_no_odd_walk
    intro v p hp_odd
    let pG : G.Walk v.1 v.1 := walkInduceMap p
    have hpG_odd : Odd pG.length := by rw [walkInduceMap_length]; exact hp_odd
    have hleL : pG.length ≤ scaleL (pG.length + 1) := by
      have h1 : pG.length < 2 ^ pG.length := Nat.lt_two_pow_self
      have h2 : 2 ^ pG.length ≤ scaleN (pG.length + 1) := by
        dsimp only [scaleN]
        exact Nat.pow_le_pow_right (by norm_num) (by omega)
      have h3 : scaleN (pG.length + 1) ≤ scaleL (pG.length + 1) := Nat.le_self_pow (by norm_num) _
      omega
    obtain ⟨x, hxsupp, hxT⟩ := hT_hit (pG.length + 1) v.1 pG hpG_odd hleL
    have hx_rest : x ∈ Vrest := walkInduceMap_support_mem p x hxsupp
    have hx_shell : x ∈ shells (G := G) T (pG.length + 1) :=
      (mem_shells_iff T (pG.length + 1) x).mpr ⟨pG.length + 1, by omega, le_rfl, x, hxT, .nil, by simp⟩
    exact hx_rest (Set.mem_iUnion.mpr ⟨pG.length + 1, hx_shell⟩)
  have hT1_col : (G.induce (T 1 : Set V)).Colorable (T 1).card := colorable_of_finset_card (T 1)
  have hcov : (Set.univ : Set V) ⊆ (T 1 : Set V) ∪ (Vhi ∪ Vrest) := by
    intro v _
    by_cases hmem : v ∈ ⋃ j : ℕ, shells (G := G) T j
    · obtain ⟨j0, hj0⟩ := Set.mem_iUnion.mp hmem
      have hex : ∃ j : ℕ, v ∈ shells (G := G) T j := ⟨j0, hj0⟩
      let jmin := Nat.find hex
      have hjmin : v ∈ shells (G := G) T jmin := Nat.find_spec hex
      have hjmin_pos : 1 ≤ jmin := by
        by_contra h0
        have hjeq : jmin = 0 := by omega
        rw [hjeq] at hjmin
        exact hjmin
      rcases eq_or_lt_of_le hjmin_pos with h1 | hge2
      · left
        have hvC1 : v ∈ shells (G := G) T 1 := h1 ▸ hjmin
        simpa [shells] using hvC1
      · right; left
        refine Set.mem_iUnion.mpr ⟨jmin - 2, ?_⟩
        have hjeq : jmin - 2 + 2 = jmin := by omega
        rw [hjeq]
        refine ⟨hjmin, ?_⟩
        exact Nat.find_min hex (by omega)
    · exact Or.inr (Or.inr hmem)
  have hcol_union : (G.induce ((T 1 : Set V) ∪ (Vhi ∪ Vrest))).Colorable ((T 1).card + ((116 + 116) + 2)) :=
    colorable_union_sets hT1_col (colorable_union_sets hVhi_col hVrest_col)
  have hcol_univ : (G.induce (Set.univ : Set V)).Colorable ((T 1).card + ((116 + 116) + 2)) :=
    colorable_of_subset hcov hcol_union
  obtain ⟨c⟩ := hcol_univ
  exact ⟨(T 1).card + ((116 + 116) + 2), ⟨Coloring.mk (fun v => c ⟨v, trivial⟩) (fun h => c.valid h)⟩⟩

end ShellDecomposition

end OMA.DisproofErdos74Sqrt

theorem OMA.disproof : ¬ (type_of% @Erdos74.erdos_74.variants.sqrt) := by
  rintro ⟨V, G, hchi, hG⟩
  obtain ⟨K, hcol⟩ := OMA.DisproofErdos74Sqrt.finite_chromatic_of_sqrt_bound hG
  have hle : G.chromaticNumber ≤ K := hcol.chromaticNumber_le
  rw [hchi] at hle
  exact not_le_of_gt (WithTop.coe_lt_top K) hle
