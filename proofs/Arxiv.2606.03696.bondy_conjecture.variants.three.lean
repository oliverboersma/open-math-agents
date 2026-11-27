import FormalConjectures.Arxiv.«2606.03696».BondyLongestCycles

-- Problem: Bondy's conjecture on longest cycles in highly connected graphs — three
-- Upstream: formal-conjectures FormalConjectures/Arxiv/2606.03696/BondyLongestCycles.lean:96 (declaration Arxiv.«2606.03696».bondy_conjecture.variants.three)
-- Credit: @koolkao (the owner of the agent is credited as the solver)

/-!
Bondy's conjecture for `k = 3`: in a 3-connected graph on `n` vertices with minimum degree at
least `(n + 6) / 4`, every component of `G - C` has at most two vertices, for any longest cycle `C`.

Original proof (a four-vertex degree count). Suppose a component `H` of `G - C` has at least three
vertices. We find `v ∈ H` and three attachment vertices `a₁, a₂, a₃` of `H` on `C`, any two joined
through `H` by a path with at least two interior vertices, such that every other cycle neighbour
`w` of `v` is joined to each `aᵢ` through `H` by a path with at least three interior vertices.
Rerouting `C` through `H` then shows, on each of the three arcs between consecutive `aᵢ`, that the
neighbour sets of `v, a₁⁺, a₂⁺, a₃⁺`, shifted by `3, 2, 1, 0` steps, are disjoint (`arc_count`).
Hence `d(v) + d(a₁⁺) + d(a₂⁺) + d(a₃⁺) ≤ n + 5` (`four_count`), contradicting `4 δ ≥ n + 6`.
Such `v, aᵢ` exist by a case analysis on the attachment types (`core`); 3-connectivity rules out
two or fewer types, and the remaining small cases follow from the gap bound `2|A| + |A₂| ≤ |C|`.
-/
namespace OMA.Bondy3

open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-! ## Closed lists and cycles -/

/-- A closed list: consecutive entries are adjacent and so are the last and the first entry. -/
def CL (G : SimpleGraph V) (l : List V) : Prop :=
  l.IsChain G.Adj ∧ ∀ x ∈ l.getLast?, ∀ y ∈ l.head?, G.Adj x y

lemma walk_of_chain : ∀ (l : List V) (x : V), (x :: l).IsChain G.Adj →
    ∃ y, ∃ p : G.Walk x y, p.support = x :: l ∧ (x :: l).getLast? = some y
  | [], x, _ => ⟨x, Walk.nil, rfl, rfl⟩
  | z :: l, x, h => by
    rw [List.isChain_cons_cons] at h
    obtain ⟨y, p, hp, hl⟩ := walk_of_chain l z h.2
    exact ⟨y, Walk.cons h.1 p, by simp [hp], by simpa using hl⟩

lemma start_edge {u v w : V} (p : G.Walk u v) (hp : p.IsPath) (h : s(u, w) ∈ p.edges) :
    w = p.getVert 1 := by
  cases p with
  | nil => simp at h
  | @cons _ x _ hadj q =>
    rw [Walk.edges_cons, List.mem_cons] at h
    rw [Walk.cons_isPath_iff] at hp
    rcases h with h | h
    · rcases Sym2.eq_iff.mp h with ⟨-, h2⟩ | ⟨h1, -⟩
      · simp [h2]
      · exact absurd h1 (G.ne_of_adj hadj)
    · exact absurd (q.fst_mem_support_of_mem_edges h) hp.2

/-- A closed nodup list with at least three entries is a cycle of that length. -/
lemma cycle_of_CL (l : List V) (hnd : l.Nodup) (hc : CL G l) (h3 : 3 ≤ l.length) :
    ∃ a, ∃ w : G.Walk a a, w.IsCycle ∧ w.length = l.length := by
  obtain _ | ⟨x, t⟩ := l
  · simp at h3
  obtain ⟨y, p, hp, hl⟩ := walk_of_chain t x hc.1
  have hyx : G.Adj y x := hc.2 y hl x rfl
  have hpath : p.IsPath := Walk.IsPath.mk' (by rw [hp]; exact hnd)
  have hlen : p.length + 1 = (x :: t).length := by
    rw [← hp, Walk.length_support]
  refine ⟨y, Walk.cons hyx p, ?_, by simp [hlen]⟩
  rw [Walk.cons_isCycle_iff]
  refine ⟨hpath, fun he => ?_⟩
  rw [Sym2.eq_swap] at he
  have h1 := start_edge p hpath he
  have hy : p.getVert p.length = y := p.getVert_length
  have := hpath.getVert_injOn (show 1 ∈ {i | i ≤ p.length} by simp; omega)
    (show p.length ∈ {i | i ≤ p.length} by simp) (by rw [hy, ← h1])
  omega

lemma cycle_length_le {a : V} (w : G.Walk a a) (hw : w.IsCycle) : w.length ≤ Fintype.card V := by
  have h1 := hw.support_nodup
  have h2 : w.support.tail.length = w.length := by
    rw [List.length_tail, Walk.length_support]; simp
  rw [← h2]
  exact h1.length_le_card

lemma le_circumference [DecidableRel G.Adj] {a : V} (w : G.Walk a a) (hw : w.IsCycle) :
    w.length ≤ G.circumference := by
  apply le_csSup
  · exact ⟨Fintype.card V, by rintro m ⟨b, w', hw', rfl⟩; exact cycle_length_le w' hw'⟩
  · exact ⟨a, w, hw, rfl⟩

/-! ## The cycle as a periodic sequence -/

/-- `f` is a `c`-periodic enumeration of a longest cycle of length `c`. -/
structure Cy (G : SimpleGraph V) (c : ℕ) (f : ℕ → V) : Prop where
  three : 3 ≤ c
  per : ∀ t, f (t + c) = f t
  adj : ∀ t, G.Adj (f t) (f (t + 1))
  inj : ∀ i j, i < c → j < c → f i = f j → i = j
  long : ∀ l : List V, l.Nodup → CL G l → l.length ≤ c

variable {c : ℕ} {f : ℕ → V}

lemma Cy.mod (hD : Cy G c f) (t : ℕ) : f t = f (t % c) := by
  conv_lhs => rw [← Nat.mod_add_div t c]
  induction t / c with
  | zero => simp
  | succ k ih => rw [Nat.mul_succ, ← Nat.add_assoc, hD.per, ih]

lemma Cy.per' (hD : Cy G c f) (t k : ℕ) : f (t + c * k) = f t := by
  rw [hD.mod, Nat.add_mul_mod_self_left, ← hD.mod]

lemma Cy.eq_iff (hD : Cy G c f) (i j : ℕ) : f i = f j ↔ i % c = j % c := by
  have hc : 0 < c := by have := hD.three; omega
  constructor
  · intro h
    rw [hD.mod i, hD.mod j] at h
    exact hD.inj _ _ (Nat.mod_lt _ hc) (Nat.mod_lt _ hc) h
  · intro h
    rw [hD.mod i, hD.mod j, h]

lemma Cy.ne_of_window (hD : Cy G c f) {b i j : ℕ} (hi1 : b ≤ i) (hi2 : i < b + c) (hj1 : b ≤ j)
    (hj2 : j < b + c) (hij : i ≠ j) : f i ≠ f j := by
  intro h
  rw [hD.eq_iff] at h
  have hc : 0 < c := by have := hD.three; omega
  rcases Nat.lt_or_ge i j with hl | hl
  · have : (j - i) % c = 0 := by
      have := Nat.sub_mod_eq_zero_of_mod_eq h.symm
      exact this
    have h1 : 0 < j - i := by omega
    have h2 : j - i < c := by omega
    rw [Nat.mod_eq_of_lt h2] at this
    omega
  · have : (i - j) % c = 0 := Nat.sub_mod_eq_zero_of_mod_eq h
    have h1 : 0 < i - j := by omega
    have h2 : i - j < c := by omega
    rw [Nat.mod_eq_of_lt h2] at this
    omega

/-- The list `f s, f (s+1), …, f (s+k-1)`. -/
def up (f : ℕ → V) (s k : ℕ) : List V := (List.range' s k).map f

/-- The list `f (s+k-1), …, f s`. -/
def dn (f : ℕ → V) (s k : ℕ) : List V := ((List.range' s k).map f).reverse

lemma chain_up (hD : Cy G c f) (s k : ℕ) : (up f s k).IsChain G.Adj := by
  induction k generalizing s with
  | zero => simp [up]
  | succ k ih =>
    cases k with
    | zero => simp [up]
    | succ k =>
      have := ih (s + 1)
      simp only [up, List.range'_succ, List.map_cons] at this ⊢
      exact List.IsChain.cons_cons (hD.adj s) this

lemma chain_dn (hD : Cy G c f) (s k : ℕ) : (dn f s k).IsChain G.Adj := by
  unfold dn
  rw [List.isChain_reverse]
  exact (chain_up hD s k).imp (fun _ _ h => h.symm)

@[simp] lemma up_length (s k : ℕ) : (up f s k).length = k := by simp [up]
@[simp] lemma dn_length (s k : ℕ) : (dn f s k).length = k := by simp [dn]

lemma up_head (s k : ℕ) : (up f s (k + 1)).head? = some (f s) := by
  simp [up, List.range'_succ]
lemma up_last (s k : ℕ) : (up f s (k + 1)).getLast? = some (f (s + k)) := by
  simp [up, List.getLast?_map, List.getLast?_range']
lemma dn_head (s k : ℕ) : (dn f s (k + 1)).head? = some (f (s + k)) := by
  simp [dn, List.head?_reverse, List.getLast?_map, List.getLast?_range']
lemma dn_last (s k : ℕ) : (dn f s (k + 1)).getLast? = some (f s) := by
  simp [dn, List.getLast?_reverse, List.range'_succ]

lemma mem_up {s k : ℕ} {x : V} : x ∈ up f s k ↔ ∃ i, s ≤ i ∧ i < s + k ∧ f i = x := by
  simp only [up, List.mem_map, List.mem_range'_1]
  constructor
  · rintro ⟨i, ⟨h1, h2⟩, rfl⟩; exact ⟨i, h1, h2, rfl⟩
  · rintro ⟨i, h1, h2, rfl⟩; exact ⟨i, ⟨h1, h2⟩, rfl⟩

lemma mem_dn {s k : ℕ} {x : V} : x ∈ dn f s k ↔ ∃ i, s ≤ i ∧ i < s + k ∧ f i = x := by
  rw [dn, List.mem_reverse]; exact mem_up

lemma nodup_up (hD : Cy G c f) {s k : ℕ} (hk : k ≤ c) : (up f s k).Nodup := by
  unfold up
  rw [List.nodup_map_iff_inj_on List.nodup_range']
  intro i hi j hj hij
  simp only [List.mem_range'_1] at hi hj
  by_contra hne
  exact hD.ne_of_window (b := s) (by omega) (by omega) (by omega) (by omega) hne hij

lemma nodup_dn (hD : Cy G c f) {s k : ℕ} (hk : k ≤ c) : (dn f s k).Nodup := by
  rw [dn, List.nodup_reverse]; exact nodup_up hD hk



/-! ## Rerouting -/

lemma nodup_map_window (hD : Cy G c f) (I : List ℕ) (b : ℕ) (hI : ∀ i ∈ I, b ≤ i ∧ i < b + c)
    (hnd : I.Nodup) : (I.map f).Nodup := by
  rw [List.nodup_map_iff_inj_on hnd]
  intro i hi j hj hij
  by_contra hne
  exact hD.ne_of_window (hI i hi).1 (hI i hi).2 (hI j hj).1 (hI j hj).2 hne hij

/-- Any closed list made of off-cycle vertices `O` and cycle vertices indexed by a window
`I` is at most as long as the cycle. -/
lemma reroute (hD : Cy G c f) (l O : List V) (I : List ℕ) (b : ℕ) (hperm : l.Perm (O ++ I.map f))
    (hcl : CL G l) (hO : O.Nodup) (hOff : ∀ x ∈ O, ∀ t, f t ≠ x)
    (hI : ∀ i ∈ I, b ≤ i ∧ i < b + c) (hInd : I.Nodup) : O.length + I.length ≤ c := by
  have hnd : l.Nodup := by
    rw [hperm.nodup_iff, List.nodup_append]
    refine ⟨hO, nodup_map_window hD I b hI hInd, ?_⟩
    intro x hx y hy hxy
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp hy
    exact hOff x hx i hxy.symm
  have := hD.long l hnd hcl
  rw [hperm.length_eq, List.length_append, List.length_map] at this
  exact this

/-- Off-cycle walk data: a nonempty nodup chain avoiding the cycle. -/
structure OffL (G : SimpleGraph V) (f : ℕ → V) (X : List V) : Prop where
  ne : X ≠ []
  nd : X.Nodup
  ch : X.IsChain G.Adj
  off : ∀ x ∈ X, ∀ t, f t ≠ x

lemma up_succ_eq (s k : ℕ) : up f s (k + 1) = up f s k ++ [f (s + k)] := by
  simp [up, List.range'_concat]

/-- `R1`: an off-cycle path from `f b` to `f (b+j)` forces the forward arc to be long. -/
lemma R1 (hD : Cy G c f) {X : List V} (hX : OffL G f X) {b j : ℕ} (hj : 1 ≤ j) (hjc : j ≤ c)
    (h1 : ∀ z ∈ X.head?, G.Adj (f b) z) (h2 : ∀ z ∈ X.getLast?, G.Adj z (f (b + j))) :
    X.length + 1 ≤ j := by
  obtain ⟨k, hk⟩ : ∃ k, c - j = k := ⟨_, rfl⟩
  have key := reroute hD (X ++ up f (b + j) (k + 1)) X (List.range' (b + j) (k + 1)) (b + 1)
    (by simp [up]) ?_ hX.nd hX.off ?_ List.nodup_range'
  · simp at key; omega
  · refine ⟨List.IsChain.append hX.ch (chain_up hD _ _) ?_, ?_⟩
    · intro x hx y hy
      rw [up_head] at hy; cases hy; exact h2 x hx
    · intro x hx y hy
      rw [List.getLast?_append, up_last] at hx
      simp at hx; subst hx
      have hb : f (b + j + k) = f b := by
        rw [show b + j + k = b + c by omega, hD.per]
      rw [hb]
      rw [List.head?_append] at hy
      obtain ⟨x0, l0, hx0⟩ := List.ne_nil_iff_exists_cons.mp hX.ne
      rw [hx0] at hy h1; simp at hy h1; subst hy; exact h1
  · intro i hi; simp at hi; omega


lemma OffL.head (hX : OffL G f X) : ∃ x0, X.head? = some x0 := by
  obtain ⟨x0, l0, rfl⟩ := List.ne_nil_iff_exists_cons.mp hX.ne
  exact ⟨x0, rfl⟩

lemma closing_aux {l : List V} {X : List V} (hX : OffL G f X) {v : V}
    (hl : l.getLast? = some v) (h1 : ∀ z ∈ X.head?, G.Adj v z) :
    ∀ x ∈ (X ++ l).getLast?, ∀ y ∈ (X ++ l).head?, G.Adj x y := by
  intro x hx y hy
  rw [List.getLast?_append, hl] at hx
  simp at hx; subst hx
  obtain ⟨x0, hx0⟩ := hX.head
  rw [List.head?_append, hx0] at hy
  simp at hy; subst hy
  exact h1 _ hx0

/-- `R3`: the two-successor crossing. -/
lemma R3 (hD : Cy G c f) {X : List V} (hX : OffL G f X) {b j p q : ℕ} (hj : 1 ≤ j)
    (hjp : j + 1 ≤ p) (hpq : p < q) (hqc : q ≤ c)
    (h1 : ∀ z ∈ X.head?, G.Adj (f b) z) (h2 : ∀ z ∈ X.getLast?, G.Adj z (f (b + j)))
    (h3 : G.Adj (f (b + 1)) (f (b + p))) (h4 : G.Adj (f (b + j + 1)) (f (b + q))) :
    X.length + p + 1 ≤ q := by
  obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  obtain ⟨d, hd⟩ : ∃ d, p - (j' + 1) = d + 1 := ⟨p - j' - 2, by omega⟩
  obtain ⟨k, hk⟩ : ∃ k, c - q = k := ⟨_, rfl⟩
  have key := reroute hD
    (X ++ (dn f (b + 1) (j' + 1) ++ (dn f (b + j' + 1 + 1) (d + 1) ++ up f (b + q) (k + 1)))) X
    ((List.range' (b + 1) (j' + 1)).reverse ++ ((List.range' (b + j' + 1 + 1) (d + 1)).reverse
      ++ List.range' (b + q) (k + 1))) (b + 1)
    (by simp [up, dn, List.map_reverse]) ?_ hX.nd hX.off ?_ ?_
  · simp at key; omega
  · have hbc : f (b + q + k) = f b := by rw [show b + q + k = b + c by omega, hD.per]
    refine ⟨?_, closing_aux hX (by simp [up_last, hbc]) h1⟩
    refine List.IsChain.append hX.ch ?_ ?_
    · refine List.IsChain.append (chain_dn hD _ _) ?_ ?_
      · refine List.IsChain.append (chain_dn hD _ _) (chain_up hD _ _) ?_
        intro x hx y hy
        rw [dn_last] at hx; rw [up_head] at hy; cases hx; cases hy
        exact h4
      · intro x hx y hy
        rw [dn_last] at hx; cases hx
        rw [List.head?_append, dn_head] at hy; simp at hy; subst hy
        rw [show b + j' + 1 + 1 + d = b + p by omega]; exact h3
    · intro x hx y hy
      rw [List.head?_append, dn_head] at hy; simp at hy; subst hy
      rw [show b + 1 + j' = b + (j' + 1) by omega]; exact h2 x hx
  · intro i hi; simp at hi; omega
  · simp only [List.nodup_append, List.nodup_reverse, List.mem_reverse, List.mem_range'_1,
      List.mem_append]
    refine ⟨List.nodup_range', ⟨List.nodup_range', List.nodup_range', ?_⟩, ?_⟩
    · intro a ha b' hb'; omega
    · intro a ha b' hb'; omega

/-- `R4`: an attachment followed by a successor chord. -/
lemma R4 (hD : Cy G c f) {X : List V} (hX : OffL G f X) {b j q : ℕ} (hj : 1 ≤ j)
    (hjq : j < q) (hqc : q ≤ c)
    (h1 : ∀ z ∈ X.head?, G.Adj (f b) z) (h2 : ∀ z ∈ X.getLast?, G.Adj z (f (b + j)))
    (h3 : G.Adj (f (b + 1)) (f (b + q))) :
    X.length + j + 1 ≤ q := by
  obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  obtain ⟨k, hk⟩ : ∃ k, c - q = k := ⟨_, rfl⟩
  have key := reroute hD
    (X ++ (dn f (b + 1) (j' + 1) ++ up f (b + q) (k + 1))) X
    ((List.range' (b + 1) (j' + 1)).reverse ++ List.range' (b + q) (k + 1)) (b + 1)
    (by simp [up, dn, List.map_reverse]) ?_ hX.nd hX.off ?_ ?_
  · simp at key; omega
  · have hbc : f (b + q + k) = f b := by rw [show b + q + k = b + c by omega, hD.per]
    refine ⟨?_, closing_aux hX (by simp [up_last, hbc]) h1⟩
    refine List.IsChain.append hX.ch ?_ ?_
    · refine List.IsChain.append (chain_dn hD _ _) (chain_up hD _ _) ?_
      intro x hx y hy
      rw [dn_last] at hx; rw [up_head] at hy; cases hx; cases hy
      exact h3
    · intro x hx y hy
      rw [List.head?_append, dn_head] at hy; simp at hy; subst hy
      rw [show b + 1 + j' = b + (j' + 1) by omega]; exact h2 x hx
  · intro i hi; simp at hi; omega
  · simp only [List.nodup_append, List.nodup_reverse, List.mem_reverse, List.mem_range'_1]
    refine ⟨List.nodup_range', List.nodup_range', ?_⟩
    intro a ha b' hb'; omega

/-- `R22`: two successors with a common off-cycle neighbour `r`. -/
lemma R22 (hD : Cy G c f) {X : List V} (hX : OffL G f X) {r : V} (hr : ∀ t, f t ≠ r)
    (hrX : r ∉ X) {b j : ℕ} (hj : 1 ≤ j) (hjc : j + 1 ≤ c)
    (h1 : ∀ z ∈ X.head?, G.Adj (f b) z) (h2 : ∀ z ∈ X.getLast?, G.Adj z (f (b + j)))
    (h3 : G.Adj (f (b + 1)) r) (h4 : G.Adj r (f (b + j + 1))) : False := by
  obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  obtain ⟨k, hk⟩ : ∃ k, c - (j' + 1) - 1 = k := ⟨_, rfl⟩
  have key := reroute hD
    (X ++ (dn f (b + 1) (j' + 1) ++ (r :: up f (b + j' + 1 + 1) (k + 1)))) (X ++ [r])
    ((List.range' (b + 1) (j' + 1)).reverse ++ List.range' (b + j' + 1 + 1) (k + 1)) (b + 1)
    ?_ ?_ ?_ ?_ ?_ ?_
  · simp at key; omega
  · simp only [up, dn, List.map_append, List.map_reverse, List.append_assoc]
    refine List.Perm.append_left X ?_
    simp only [List.singleton_append]
    exact List.perm_middle
  · have hbc : f (b + j' + 1 + 1 + k) = f b := by
      rw [show b + j' + 1 + 1 + k = b + c by omega, hD.per]
    have hl : (r :: up f (b + j' + 1 + 1) (k + 1)).getLast? = some (f b) := by
      rw [List.getLast?_cons, up_last]; simp [hbc]
    refine ⟨?_, closing_aux hX (by rw [List.getLast?_append, hl]; simp) h1⟩
    refine List.IsChain.append hX.ch ?_ ?_
    · refine List.IsChain.append (chain_dn hD _ _) ?_ ?_
      · rw [List.isChain_cons]
        refine ⟨?_, chain_up hD _ _⟩
        intro y hy; rw [up_head] at hy; cases hy; exact h4
      · intro x hx y hy
        rw [dn_last] at hx; cases hx; simp at hy; subst hy; exact h3
    · intro x hx y hy
      rw [List.head?_append, dn_head] at hy; simp at hy; subst hy
      rw [show b + 1 + j' = b + (j' + 1) by omega]; exact h2 x hx
  · rw [List.nodup_append]
    refine ⟨hX.nd, List.nodup_singleton r, ?_⟩
    intro x hx y hy hxy; simp at hy; subst hy; subst hxy; exact hrX hx
  · intro x hx t; simp at hx; rcases hx with hx | rfl
    · exact hX.off x hx t
    · exact hr t
  · intro i hi; simp at hi; omega
  · simp only [List.nodup_append, List.nodup_reverse, List.mem_reverse, List.mem_range'_1]
    refine ⟨List.nodup_range', List.nodup_range', ?_⟩
    intro a ha b' hb'; omega



/-! ## The counting lemma on one arc -/

/-- An off-cycle path from `x` to `y` with at least `K` interior vertices. -/
def PH (G : SimpleGraph V) (f : ℕ → V) (x y : V) (K : ℕ) : Prop :=
  ∃ X : List V, OffL G f X ∧ K ≤ X.length ∧ (∀ z ∈ X.head?, G.Adj x z) ∧
    (∀ z ∈ X.getLast?, G.Adj z y)

lemma PH.symm {x y : V} {K : ℕ} (h : PH G f x y K) : PH G f y x K := by
  obtain ⟨X, hX, hK, h1, h2⟩ := h
  refine ⟨X.reverse, ⟨by simpa using hX.ne, List.nodup_reverse.mpr hX.nd, ?_, ?_⟩, by simpa, ?_, ?_⟩
  · rw [List.isChain_reverse]; exact hX.ch.imp (fun _ _ h => h.symm)
  · intro x hx; exact hX.off x (List.mem_reverse.mp hx)
  · intro z hz; rw [List.head?_reverse] at hz; exact (h2 z hz).symm
  · intro z hz; rw [List.getLast?_reverse] at hz; exact (h1 z hz).symm

lemma PH.mono {x y : V} {K K' : ℕ} (h : PH G f x y K) (hK : K' ≤ K) : PH G f x y K' := by
  obtain ⟨X, hX, hk, h1, h2⟩ := h; exact ⟨X, hX, by omega, h1, h2⟩

lemma Cy.shift (hD : Cy G c f) {s t : ℕ} (h : s = t + c) : f s = f t := by
  rw [h, hD.per]

/-- Counting on the arc `f (i+1), …, f (i+ℓ)` between the consecutive chosen attachments
`α = f i` and `β = f (i+ℓ)`, the third one being `γ = f (i+ℓ+e)`. -/
lemma arc_count [DecidableRel G.Adj] (hD : Cy G c f) {v : V} (hv : ∀ t, f t ≠ v) {i ℓ e : ℕ} (hℓ : 1 ≤ ℓ)
    (he : 1 ≤ e) (hlc : ℓ + e < c)
    (hA1 : ¬ G.Adj v (f (i + 1)))
    (hB1 : ¬ G.Adj (f (i + ℓ + 1)) (f (i + 1))) (hG1 : ¬ G.Adj (f (i + ℓ + e + 1)) (f (i + 1)))
    (pγα : PH G f (f (i + ℓ + e)) (f i) 1) (pβγ : PH G f (f (i + ℓ)) (f (i + ℓ + e)) 1)
    (pβα : PH G f (f (i + ℓ)) (f i) 2)
    (p0 : ∀ t, i + 2 ≤ t → t + 1 ≤ i + ℓ → G.Adj v (f t) →
      PH G f (f (i + ℓ)) (f t) 1 ∧ PH G f (f (i + ℓ + e)) (f t) 3 ∧ PH G f (f i) (f t) 3) :
    ((Finset.Icc (i + 1) (i + ℓ)).filter (fun t => G.Adj v (f t))).card +
    ((Finset.Icc (i + 1) (i + ℓ)).filter (fun t => G.Adj (f (i + 1)) (f t))).card +
    ((Finset.Icc (i + 1) (i + ℓ)).filter (fun t => G.Adj (f (i + ℓ + e + 1)) (f t))).card +
    ((Finset.Icc (i + 1) (i + ℓ)).filter (fun t => G.Adj (f (i + ℓ + 1)) (f t))).card
      ≤ ℓ + 2 := by
  classical
  set I := Finset.Icc (i + 1) (i + ℓ)
  set S0 := I.filter (fun t => G.Adj v (f t))
  set Sa := I.filter (fun t => G.Adj (f (i + 1)) (f t))
  set Sg := I.filter (fun t => G.Adj (f (i + ℓ + e + 1)) (f t))
  set Sb := I.filter (fun t => G.Adj (f (i + ℓ + 1)) (f t))
  -- basic facts: index `i+1` is in none of the sets
  have m0 : ∀ t ∈ S0, i + 2 ≤ t ∧ t ≤ i + ℓ := by
    intro t ht; simp only [S0, I, Finset.mem_filter, Finset.mem_Icc] at ht
    refine ⟨?_, ht.1.2⟩
    by_contra h; have : t = i + 1 := by omega
    subst this; exact hA1 ht.2
  have ma : ∀ t ∈ Sa, i + 2 ≤ t ∧ t ≤ i + ℓ := by
    intro t ht; simp only [Sa, I, Finset.mem_filter, Finset.mem_Icc] at ht
    refine ⟨?_, ht.1.2⟩
    by_contra h; have : t = i + 1 := by omega
    subst this; exact G.irrefl ht.2
  have mg : ∀ t ∈ Sg, i + 2 ≤ t ∧ t ≤ i + ℓ := by
    intro t ht; simp only [Sg, I, Finset.mem_filter, Finset.mem_Icc] at ht
    refine ⟨?_, ht.1.2⟩
    by_contra h; have : t = i + 1 := by omega
    subst this; exact hG1 ht.2
  have mb : ∀ t ∈ Sb, i + 2 ≤ t ∧ t ≤ i + ℓ := by
    intro t ht; simp only [Sb, I, Finset.mem_filter, Finset.mem_Icc] at ht
    refine ⟨?_, ht.1.2⟩
    by_contra h; have : t = i + 1 := by omega
    subst this; exact hB1 ht.2
  have adj0 : ∀ t ∈ S0, G.Adj v (f t) := fun t ht => (Finset.mem_filter.mp ht).2
  have adja : ∀ t ∈ Sa, G.Adj (f (i + 1)) (f t) := fun t ht => (Finset.mem_filter.mp ht).2
  have adjg : ∀ t ∈ Sg, G.Adj (f (i + ℓ + e + 1)) (f t) := fun t ht => (Finset.mem_filter.mp ht).2
  have adjb : ∀ t ∈ Sb, G.Adj (f (i + ℓ + 1)) (f t) := fun t ht => (Finset.mem_filter.mp ht).2
  -- the six crossing exclusions
  -- (1) t ∈ Sg, t+1 ∈ Sa : R3 at γ
  have x1 : ∀ t ∈ Sg, t + 1 ∉ Sa := by
    intro t ht ht'
    obtain ⟨h1, h2⟩ := mg t ht; obtain ⟨h1', h2'⟩ := ma _ ht'
    obtain ⟨X, hX, hK, hh, hl⟩ := pγα
    have := R3 hD hX (b := i + ℓ + e) (j := c - ℓ - e) (p := c - ℓ - e + (t - i))
      (q := c - ℓ - e + (t - i) + 1) (by omega) (by omega) (by omega) (by omega) hh
      (by rw [hD.shift (show i + ℓ + e + (c - ℓ - e) = i + c by omega)]; exact hl)
      (by rw [hD.shift (show i + ℓ + e + (c - ℓ - e + (t - i)) = t + c by omega)]; exact adjg t ht)
      (by rw [hD.shift (show i + ℓ + e + (c - ℓ - e) + 1 = (i + 1) + c by omega),
              hD.shift (show i + ℓ + e + (c - ℓ - e + (t - i) + 1) = (t + 1) + c by omega)]
          exact adja _ ht')
    omega
  -- (2) t ∈ Sb, t+1 ∈ Sg : R3 at β towards γ
  have x2 : ∀ t ∈ Sb, t + 1 ∉ Sg := by
    intro t ht ht'
    obtain ⟨h1, h2⟩ := mb t ht; obtain ⟨h1', h2'⟩ := mg _ ht'
    obtain ⟨X, hX, hK, hh, hl⟩ := pβγ
    have := R3 hD hX (b := i + ℓ) (j := e) (p := c - ℓ + (t - i))
      (q := c - ℓ + (t - i) + 1) (by omega) (by omega) (by omega) (by omega) hh hl
      (by rw [hD.shift (show i + ℓ + (c - ℓ + (t - i)) = t + c by omega)]; exact adjb t ht)
      (by rw [hD.shift (show i + ℓ + (c - ℓ + (t - i) + 1) = (t + 1) + c by omega)]
          exact adjg _ ht')
    omega
  -- (3) t ∈ Sb, t+2 ∈ Sa : R3 at β towards α
  have x3 : ∀ t ∈ Sb, t + 2 ∉ Sa := by
    intro t ht ht'
    obtain ⟨h1, h2⟩ := mb t ht; obtain ⟨h1', h2'⟩ := ma _ ht'
    obtain ⟨X, hX, hK, hh, hl⟩ := pβα
    have := R3 hD hX (b := i + ℓ) (j := c - ℓ) (p := c - ℓ + (t - i))
      (q := c - ℓ + (t - i) + 2) (by omega) (by omega) (by omega) (by omega) hh
      (by rw [hD.shift (show i + ℓ + (c - ℓ) = i + c by omega)]; exact hl)
      (by rw [hD.shift (show i + ℓ + (c - ℓ + (t - i)) = t + c by omega)]; exact adjb t ht)
      (by rw [hD.shift (show i + ℓ + (c - ℓ) + 1 = (i + 1) + c by omega),
              hD.shift (show i + ℓ + (c - ℓ + (t - i) + 2) = (t + 2) + c by omega)]
          exact adja _ ht')
    omega
  -- (4) t ∈ S0, t+1 ∈ Sb : R4 at β
  have x4 : ∀ t ∈ S0, t + 1 ∉ Sb := by
    intro t ht ht'
    obtain ⟨h1, h2⟩ := m0 t ht; obtain ⟨h1', h2'⟩ := mb _ ht'
    obtain ⟨X, hX, hK, hh, hl⟩ := (p0 t h1 (by omega) (adj0 t ht)).1
    have := R4 hD hX (b := i + ℓ) (j := c - ℓ + (t - i)) (q := c - ℓ + (t - i) + 1)
      (by omega) (by omega) (by omega) hh
      (by rw [hD.shift (show i + ℓ + (c - ℓ + (t - i)) = t + c by omega)]; exact hl)
      (by rw [hD.shift (show i + ℓ + (c - ℓ + (t - i) + 1) = (t + 1) + c by omega)]
          exact adjb _ ht')
    omega
  -- (5) t ∈ S0, t+2 ∈ Sg : R4 at γ
  have x5 : ∀ t ∈ S0, t + 2 ∉ Sg := by
    intro t ht ht'
    obtain ⟨h1, h2⟩ := m0 t ht; obtain ⟨h1', h2'⟩ := mg _ ht'
    obtain ⟨X, hX, hK, hh, hl⟩ := (p0 t h1 (by omega) (adj0 t ht)).2.1
    have := R4 hD hX (b := i + ℓ + e) (j := c - ℓ - e + (t - i)) (q := c - ℓ - e + (t - i) + 2)
      (by omega) (by omega) (by omega) hh
      (by rw [hD.shift (show i + ℓ + e + (c - ℓ - e + (t - i)) = t + c by omega)]; exact hl)
      (by rw [hD.shift (show i + ℓ + e + (c - ℓ - e + (t - i) + 2) = (t + 2) + c by omega)]
          exact adjg _ ht')
    omega
  -- (6) t ∈ S0, t+3 ∈ Sa : R4 at α
  have x6 : ∀ t ∈ S0, t + 3 ∉ Sa := by
    intro t ht ht'
    obtain ⟨h1, h2⟩ := m0 t ht; obtain ⟨h1', h2'⟩ := ma _ ht'
    obtain ⟨X, hX, hK, hh, hl⟩ := (p0 t h1 (by omega) (adj0 t ht)).2.2
    have := R4 hD hX (b := i) (j := t - i) (q := t - i + 3)
      (by omega) (by omega) (by omega) hh
      (by rw [show i + (t - i) = t by omega]; exact hl)
      (by rw [show i + (t - i + 3) = t + 3 by omega]; exact adja _ ht')
    omega
  -- assemble
  set T1 := Sg.image (· + 1)
  set T2 := Sb.image (· + 2)
  set T3 := S0.image (· + 3)
  have c1 : T1.card = Sg.card := Finset.card_image_of_injective _ (add_left_injective 1)
  have c2 : T2.card = Sb.card := Finset.card_image_of_injective _ (add_left_injective 2)
  have c3 : T3.card = S0.card := Finset.card_image_of_injective _ (add_left_injective 3)
  have d1 : Disjoint Sa T1 := by
    rw [Finset.disjoint_left]; intro x hx hx'
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hx'; exact x1 t ht hx
  have d2 : Disjoint (Sa ∪ T1) T2 := by
    rw [Finset.disjoint_left]; intro x hx hx'
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hx'
    rcases Finset.mem_union.mp hx with hx | hx
    · exact x3 t ht hx
    · obtain ⟨s, hs, hst⟩ := Finset.mem_image.mp hx
      have : s = t + 1 := by omega
      subst this; exact x2 t ht hs
  have d3 : Disjoint (Sa ∪ T1 ∪ T2) T3 := by
    rw [Finset.disjoint_left]; intro x hx hx'
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hx'
    rcases Finset.mem_union.mp hx with hx | hx
    · rcases Finset.mem_union.mp hx with hx | hx
      · exact x6 t ht hx
      · obtain ⟨s, hs, hst⟩ := Finset.mem_image.mp hx
        have : s = t + 2 := by omega
        subst this; exact x5 t ht hs
    · obtain ⟨s, hs, hst⟩ := Finset.mem_image.mp hx
      have : s = t + 1 := by omega
      subst this; exact x4 t ht hs
  have sub : Sa ∪ T1 ∪ T2 ∪ T3 ⊆ Finset.Icc (i + 2) (i + ℓ + 3) := by
    intro x hx
    simp only [Finset.mem_union, Finset.mem_image, T1, T2, T3] at hx
    rw [Finset.mem_Icc]
    rcases hx with ((hx | ⟨t, ht, rfl⟩) | ⟨t, ht, rfl⟩) | ⟨t, ht, rfl⟩
    · have := ma x hx; omega
    · have := mg t ht; omega
    · have := mb t ht; omega
    · have := m0 t ht; omega
  have := Finset.card_le_card sub
  rw [Finset.card_union_of_disjoint d3, Finset.card_union_of_disjoint d2,
    Finset.card_union_of_disjoint d1, c1, c2, c3, Nat.card_Icc] at this
  omega



/-! ## The off-cycle component -/

/-- A path list inside `H` from `x` to `y`. -/
def HP (G : SimpleGraph V) (H : Finset V) (x y : V) (X : List V) : Prop :=
  X.Nodup ∧ X.IsChain G.Adj ∧ (∀ z ∈ X, z ∈ H) ∧ X.head? = some x ∧ X.getLast? = some y

/-- `H` is a component of `G - C`. -/
structure Comp (G : SimpleGraph V) (f : ℕ → V) (H : Finset V) : Prop where
  off : ∀ x ∈ H, ∀ t, f t ≠ x
  cl : ∀ x ∈ H, ∀ y, G.Adj x y → y ∈ H ∨ ∃ t, f t = y
  conn : ∀ x ∈ H, ∀ y ∈ H, ∃ X, HP G H x y X

variable {H : Finset V}

lemma HP.offL (hC : Comp G f H) {x y : V} {X : List V} (h : HP G H x y X) : OffL G f X :=
  ⟨by rintro rfl; simp [HP] at h, h.1, h.2.1, fun z hz => hC.off z (h.2.2.1 z hz)⟩

lemma HP.two_le {x y : V} {X : List V} (h : HP G H x y X) (hxy : x ≠ y) : 2 ≤ X.length := by
  obtain ⟨-, -, -, h1, h2⟩ := h
  match X, h1, h2 with
  | [a], h1, h2 => simp at h1 h2; exact absurd (h1.symm.trans h2) hxy
  | a :: b :: l, _, _ => simp

lemma ph_of (hC : Comp G f H) {a b z z' : V} (hz : z ∈ H) (hz' : z' ∈ H) (ha : G.Adj a z)
    (hb : G.Adj b z') : PH G f a b 1 := by
  obtain ⟨X, hX⟩ := hC.conn z hz z' hz'
  exact ⟨X, hX.offL hC, by have := (hX.offL hC).ne; exact List.length_pos_iff.mpr this,
    by intro w hw; rw [hX.2.2.2.1] at hw; cases hw; exact ha,
    by intro w hw; rw [hX.2.2.2.2] at hw; cases hw; exact hb.symm⟩

lemma ph_two (hC : Comp G f H) {a b z z' : V} (hz : z ∈ H) (hz' : z' ∈ H) (hzz : z ≠ z')
    (ha : G.Adj a z) (hb : G.Adj b z') : PH G f a b 2 := by
  obtain ⟨X, hX⟩ := hC.conn z hz z' hz'
  exact ⟨X, hX.offL hC, hX.two_le hzz,
    by intro w hw; rw [hX.2.2.2.1] at hw; cases hw; exact ha,
    by intro w hw; rw [hX.2.2.2.2] at hw; cases hw; exact hb.symm⟩

/-- `f s` is an attachment vertex of `H`. -/
def Att (G : SimpleGraph V) (f : ℕ → V) (H : Finset V) (s : ℕ) : Prop := ∃ z ∈ H, G.Adj (f s) z

lemma G1 (hD : Cy G c f) (hC : Comp G f H) {s : ℕ} (hs : Att G f H s) :
    ∀ z ∈ H, ¬ G.Adj (f (s + 1)) z := by
  intro z hz hadj
  obtain ⟨z0, hz0, ha⟩ := hs
  obtain ⟨X, hX, hK, h1, h2⟩ := ph_of hC hz0 hz ha hadj
  have := R1 hD hX (b := s) (j := 1) le_rfl (by have := hD.three; omega) h1 h2
  omega

lemma G2 (hD : Cy G c f) (hC : Comp G f H) {s j : ℕ} (hs : Att G f H s)
    (hsj : Att G f H (s + j)) (hj : 1 ≤ j) (hjc : j < c) :
    ¬ G.Adj (f (s + 1)) (f (s + j + 1)) := by
  intro hadj
  obtain ⟨z, hz, hsz⟩ := hs
  rcases Nat.lt_or_ge (j + 1) c with h | h
  · obtain ⟨z', hz', hsz'⟩ := hsj
    obtain ⟨X, hX, hK, h1, h2⟩ := ph_of hC hz hz' hsz hsz'
    have := R3 hD hX (b := s) (j := j) (p := j + 1) (q := j + 2) hj le_rfl (by omega) (by omega)
      h1 h2 (by simpa [Nat.add_assoc] using hadj) (by rw [Nat.add_assoc]; exact (hD.adj _))
    omega
  · have : f (s + j + 1) = f s := hD.shift (by omega)
    exact G1 hD hC hsj z hz (by rw [this]; exact hsz)

lemma G3 (hD : Cy G c f) (hC : Comp G f H) {s j : ℕ} (hs : Att G f H s)
    (hsj : Att G f H (s + j)) (hj : 1 ≤ j) (hjc : j < c) {r : V} (hrH : r ∉ H)
    (hrC : ∀ t, f t ≠ r) (h3 : G.Adj (f (s + 1)) r) (h4 : G.Adj r (f (s + j + 1))) : False := by
  obtain ⟨z, hz, hsz⟩ := hs
  obtain ⟨z', hz', hsz'⟩ := hsj
  obtain ⟨X, hX⟩ := hC.conn z hz z' hz'
  exact R22 hD (hX.offL hC) hrC (fun h => hrH (hX.2.2.1 r h)) (b := s) (j := j) hj (by omega)
    (by intro w hw; rw [hX.2.2.2.1] at hw; cases hw; exact hsz)
    (by intro w hw; rw [hX.2.2.2.2] at hw; cases hw; exact hsz'.symm) h3 h4


lemma att_shift (hD : Cy G c f) {s t : ℕ} (h : s = t + c) (ht : Att G f H t) : Att G f H s := by
  obtain ⟨z, hz, h⟩ := ht; exact ⟨z, hz, by rw [hD.shift (by omega : s = t + c)]; exact h⟩

lemma split_Ioc (P : ℕ → Prop) [DecidablePred P] {a b d : ℕ} (hab : a ≤ b) (hbd : b ≤ d) :
    ((Finset.Ioc a d).filter P).card =
      ((Finset.Ioc a b).filter P).card + ((Finset.Ioc b d).filter P).card := by
  simp only [Finset.card_filter]
  exact (Finset.sum_Ioc_consecutive _ hab hbd).symm

/-- The cycle part of the four-vertex count. -/
lemma master_C [DecidableRel G.Adj] (hD : Cy G c f) (hC : Comp G f H) {v : V} (hv : v ∈ H)
    {p1 p2 p3 : ℕ} (h12 : p1 < p2) (h23 : p2 < p3) (h31 : p3 < p1 + c)
    (a1 : Att G f H p1) (a2 : Att G f H p2) (a3 : Att G f H p3)
    (c12 : PH G f (f p1) (f p2) 2) (c23 : PH G f (f p2) (f p3) 2) (c13 : PH G f (f p1) (f p3) 2)
    (c2 : ∀ t, G.Adj v (f t) → f t ≠ f p1 → f t ≠ f p2 → f t ≠ f p3 →
      PH G f (f p1) (f t) 3 ∧ PH G f (f p2) (f t) 3 ∧ PH G f (f p3) (f t) 3) :
    ((Finset.Ioc p1 (p1 + c)).filter (fun t => G.Adj v (f t))).card +
    ((Finset.Ioc p1 (p1 + c)).filter (fun t => G.Adj (f (p1 + 1)) (f t))).card +
    ((Finset.Ioc p1 (p1 + c)).filter (fun t => G.Adj (f (p2 + 1)) (f t))).card +
    ((Finset.Ioc p1 (p1 + c)).filter (fun t => G.Adj (f (p3 + 1)) (f t))).card ≤ c + 6 := by
  have hvC := hC.off v hv
  have e1 : f (p1 + c) = f p1 := hD.per p1
  have e1s : f (p1 + c + 1) = f (p1 + 1) := hD.shift (by omega)
  have e2s : f (p2 + c + 1) = f (p2 + 1) := hD.shift (by omega)
  have a1c : Att G f H (p1 + c) := att_shift hD rfl a1
  -- attachments of `v` are attachment vertices
  have attv : ∀ t, G.Adj v (f t) → Att G f H t := fun t h => ⟨v, hv, h.symm⟩
  have pv1 : ∀ s t, Att G f H s → G.Adj v (f t) → PH G f (f s) (f t) 1 := by
    intro s t hs ht; obtain ⟨z, hz, h⟩ := hs; exact ph_of hC hz hv h ht.symm
  have nA : ∀ s, Att G f H s → ¬ G.Adj v (f (s + 1)) :=
    fun s hs h => G1 hD hC hs v hv h.symm
  -- window distinctness
  have win : ∀ t, p1 ≤ t → t < p1 + c → ∀ p, p1 ≤ p → p < p1 + c → t ≠ p → f t ≠ f p :=
    fun t h1 h2 p h3 h4 h5 => hD.ne_of_window h1 h2 h3 h4 h5
  -- arc A : i = p1, ℓ = p2 - p1, e = p3 - p2
  have hA := arc_count hD hvC (i := p1) (ℓ := p2 - p1) (e := p3 - p2) (by omega) (by omega)
    (by omega) (nA p1 a1)
    (fun h => G2 hD hC (j := p2 - p1) a1 (by rw [show p1 + (p2 - p1) = p2 by omega]; exact a2)
      (by omega) (by omega) h.symm)
    (fun h => G2 hD hC (j := p2 - p1 + (p3 - p2)) a1
      (by rw [show p1 + (p2 - p1 + (p3 - p2)) = p3 by omega]; exact a3) (by omega) (by omega)
      (by rw [show p1 + (p2 - p1 + (p3 - p2)) + 1 = p1 + (p2 - p1) + (p3 - p2) + 1 by omega]
          exact h.symm))
    (by rw [show p1 + (p2 - p1) + (p3 - p2) = p3 by omega]; exact (c13.mono (by omega)).symm)
    (by rw [show p1 + (p2 - p1) + (p3 - p2) = p3 by omega, show p1 + (p2 - p1) = p2 by omega]
        exact c23.mono (by omega))
    (by rw [show p1 + (p2 - p1) = p2 by omega]; exact c12.symm)
    (by
      intro t ht1 ht2 hvt
      have n1 := win t (by omega) (by omega) p1 le_rfl (by omega) (by omega)
      have n2 := win t (by omega) (by omega) p2 (by omega) (by omega) (by omega)
      have n3 := win t (by omega) (by omega) p3 (by omega) (by omega) (by omega)
      obtain ⟨q1, q2, q3⟩ := c2 t hvt n1 n2 n3
      refine ⟨?_, ?_, q1⟩
      · rw [show p1 + (p2 - p1) = p2 by omega]; exact pv1 p2 t a2 hvt
      · rw [show p1 + (p2 - p1) + (p3 - p2) = p3 by omega]; exact q3)
  rw [show p1 + (p2 - p1) = p2 by omega, show p2 + (p3 - p2) + 1 = p3 + 1 by omega] at hA
  -- arc B : i = p2, ℓ = p3 - p2, e = c + p1 - p3
  have hB := arc_count hD hvC (i := p2) (ℓ := p3 - p2) (e := c + p1 - p3) (by omega) (by omega)
    (by omega) (nA p2 a2)
    (fun h => G2 hD hC (j := p3 - p2) a2 (by rw [show p2 + (p3 - p2) = p3 by omega]; exact a3)
      (by omega) (by omega) h.symm)
    (fun h => G2 hD hC (j := p3 - p2 + (c + p1 - p3)) a2
      (by rw [show p2 + (p3 - p2 + (c + p1 - p3)) = p1 + c by omega]; exact a1c) (by omega)
      (by omega)
      (by rw [show p2 + (p3 - p2 + (c + p1 - p3)) + 1 = p2 + (p3 - p2) + (c + p1 - p3) + 1 by omega]
          exact h.symm))
    (by rw [show p2 + (p3 - p2) + (c + p1 - p3) = p1 + c by omega, e1]; exact c12.mono (by omega))
    (by rw [show p2 + (p3 - p2) + (c + p1 - p3) = p1 + c by omega, e1,
          show p2 + (p3 - p2) = p3 by omega]
        exact (c13.mono (by omega)).symm)
    (by rw [show p2 + (p3 - p2) = p3 by omega]; exact c23.symm)
    (by
      intro t ht1 ht2 hvt
      have n1 := win t (by omega) (by omega) p1 le_rfl (by omega) (by omega)
      have n2 := win t (by omega) (by omega) p2 (by omega) (by omega) (by omega)
      have n3 := win t (by omega) (by omega) p3 (by omega) (by omega) (by omega)
      obtain ⟨q1, q2, q3⟩ := c2 t hvt n1 n2 n3
      refine ⟨?_, ?_, q2⟩
      · rw [show p2 + (p3 - p2) = p3 by omega]; exact pv1 p3 t a3 hvt
      · rw [show p2 + (p3 - p2) + (c + p1 - p3) = p1 + c by omega, e1]; exact q1)
  rw [show p2 + (p3 - p2) = p3 by omega,
    show p3 + (c + p1 - p3) + 1 = p1 + c + 1 by omega, e1s] at hB
  -- arc C : i = p3, ℓ = c + p1 - p3, e = p2 - p1
  have hCc := arc_count hD hvC (i := p3) (ℓ := c + p1 - p3) (e := p2 - p1) (by omega) (by omega)
    (by omega) (nA p3 a3)
    (fun h => G2 hD hC (j := c + p1 - p3) a3
      (by rw [show p3 + (c + p1 - p3) = p1 + c by omega]; exact a1c) (by omega) (by omega) h.symm)
    (fun h => G2 hD hC (j := c + p1 - p3 + (p2 - p1)) a3
      (by rw [show p3 + (c + p1 - p3 + (p2 - p1)) = p2 + c by omega]; exact att_shift hD rfl a2)
      (by omega) (by omega)
      (by rw [show p3 + (c + p1 - p3 + (p2 - p1)) + 1 = p3 + (c + p1 - p3) + (p2 - p1) + 1 by omega]
          exact h.symm))
    (by rw [show p3 + (c + p1 - p3) + (p2 - p1) = p2 + c by omega, hD.per]
        exact (c23.mono (by omega)))
    (by rw [show p3 + (c + p1 - p3) + (p2 - p1) = p2 + c by omega, hD.per,
          show p3 + (c + p1 - p3) = p1 + c by omega, e1]
        exact c12.mono (by omega))
    (by rw [show p3 + (c + p1 - p3) = p1 + c by omega, e1]; exact c13)
    (by
      intro t ht1 ht2 hvt
      have n1 := win t (by omega) (by omega) p1 le_rfl (by omega) (by omega)
      have n2 := win t (by omega) (by omega) p2 (by omega) (by omega) (by omega)
      have n3 := win t (by omega) (by omega) p3 (by omega) (by omega) (by omega)
      obtain ⟨q1, q2, q3⟩ := c2 t hvt n1 n2 n3
      refine ⟨?_, ?_, q3⟩
      · rw [show p3 + (c + p1 - p3) = p1 + c by omega, e1]; exact pv1 p1 t a1 hvt
      · rw [show p3 + (c + p1 - p3) + (p2 - p1) = p2 + c by omega, hD.per]; exact q2)
  rw [show p3 + (c + p1 - p3) = p1 + c by omega, e1s,
    show p1 + c + (p2 - p1) + 1 = p2 + c + 1 by omega, e2s] at hCc
  simp only [Finset.Icc_add_one_left_eq_Ioc] at hA hB hCc
  rw [split_Ioc _ (show p1 ≤ p2 by omega) (show p2 ≤ p1 + c by omega),
    split_Ioc _ (show p2 ≤ p3 by omega) (show p3 ≤ p1 + c by omega)]
  rw [split_Ioc _ (show p1 ≤ p2 by omega) (show p2 ≤ p1 + c by omega),
    split_Ioc _ (show p2 ≤ p3 by omega) (show p3 ≤ p1 + c by omega)]
  rw [split_Ioc _ (show p1 ≤ p2 by omega) (show p2 ≤ p1 + c by omega),
    split_Ioc _ (show p2 ≤ p3 by omega) (show p3 ≤ p1 + c by omega)]
  rw [split_Ioc _ (show p1 ≤ p2 by omega) (show p2 ≤ p1 + c by omega),
    split_Ioc _ (show p2 ≤ p3 by omega) (show p3 ≤ p1 + c by omega)]
  omega



/-! ## The four-vertex degree count -/

lemma Cy.exists_window (hD : Cy G c f) (b t : ℕ) : ∃ t', b < t' ∧ t' ≤ b + c ∧ f t' = f t := by
  have hc : 0 < c := by have := hD.three; omega
  set m := t + c * (b + 1) - (b + 1)
  have hm : b + 1 ≤ t + c * (b + 1) := by nlinarith
  refine ⟨b + 1 + m % c, by omega, by have := Nat.mod_lt m hc; omega, ?_⟩
  have e1 : f (b + 1 + m % c + c * (m / c)) = f (b + 1 + m % c) := hD.per' _ _
  have e2 : b + 1 + m % c + c * (m / c) = t + c * (b + 1) := by
    have := Nat.mod_add_div m c; omega
  rw [← e1, e2, hD.per']

lemma Cy.mem_cset (hD : Cy G c f) (t : ℕ) : f t ∈ (Finset.range c).image f := by
  obtain ⟨t', h1, h2, h3⟩ := hD.exists_window 0 t
  rw [Finset.mem_image]
  refine ⟨t' % c, Finset.mem_range.mpr (Nat.mod_lt _ (by have := hD.three; omega)), ?_⟩
  rw [← hD.mod, h3]

lemma card_on_cycle [DecidableRel G.Adj] (hD : Cy G c f) (b : ℕ) (x : V) :
    ((Finset.Ioc b (b + c)).filter (fun t => G.Adj x (f t))).card =
      ((G.neighborFinset x).filter (· ∈ (Finset.range c).image f)).card := by
  have hinj : Set.InjOn f ((Finset.Ioc b (b + c)).filter (fun t => G.Adj x (f t))) := by
    intro i hi j hj hij
    simp only [Finset.coe_filter, Finset.mem_Ioc, Set.mem_setOf_eq] at hi hj
    by_contra hne
    exact hD.ne_of_window (b := b + 1) (by omega) (by omega) (by omega) (by omega) hne hij
  rw [← Finset.card_image_of_injOn hinj]
  congr 1
  ext y
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_Ioc, mem_neighborFinset]
  constructor
  · rintro ⟨t, ⟨-, h⟩, rfl⟩; exact ⟨h, Finset.mem_image.mp (hD.mem_cset t)⟩
  · rintro ⟨h, hy⟩
    obtain ⟨t, -, rfl⟩ := hy
    obtain ⟨t', h1, h2, h3⟩ := hD.exists_window b t
    exact ⟨t', ⟨⟨h1, h2⟩, by rw [h3]; exact h⟩, h3⟩

lemma card_cset (hD : Cy G c f) : ((Finset.range c).image f).card = c := by
  rw [Finset.card_image_of_injOn, Finset.card_range]
  intro i hi j hj hij
  exact hD.inj i j (Finset.mem_range.mp hi) (Finset.mem_range.mp hj) hij

/-- The full four-vertex count: `d(v) + d(a₁⁺) + d(a₂⁺) + d(a₃⁺) ≤ n + 5`. -/
lemma four_count [DecidableRel G.Adj] (hD : Cy G c f) (hC : Comp G f H) {v : V} (hv : v ∈ H)
    {p1 p2 p3 : ℕ} (h12 : p1 < p2) (h23 : p2 < p3) (h31 : p3 < p1 + c)
    (a1 : Att G f H p1) (a2 : Att G f H p2) (a3 : Att G f H p3)
    (c12 : PH G f (f p1) (f p2) 2) (c23 : PH G f (f p2) (f p3) 2) (c13 : PH G f (f p1) (f p3) 2)
    (c2 : ∀ t, G.Adj v (f t) → f t ≠ f p1 → f t ≠ f p2 → f t ≠ f p3 →
      PH G f (f p1) (f t) 3 ∧ PH G f (f p2) (f t) 3 ∧ PH G f (f p3) (f t) 3) :
    G.degree v + G.degree (f (p1 + 1)) + G.degree (f (p2 + 1)) + G.degree (f (p3 + 1)) ≤
      Fintype.card V + 5 := by
  have hM := master_C hD hC hv h12 h23 h31 a1 a2 a3 c12 c23 c13 c2
  simp only [card_on_cycle hD p1] at hM
  set Cs := (Finset.range c).image f with hCs
  set R : Finset V := (Finset.univ.filter (fun y => y ∉ Cs ∧ y ∉ H)) with hR
  have offCs : ∀ y ∈ H, y ∉ Cs := by
    intro y hy hyC
    obtain ⟨t, -, ht⟩ := Finset.mem_image.mp hyC
    exact hC.off y hy t ht
  have split : ∀ x, G.degree x = ((G.neighborFinset x).filter (· ∈ Cs)).card +
      ((G.neighborFinset x).filter (· ∈ H)).card +
      ((G.neighborFinset x).filter (· ∈ R)).card := by
    intro x
    rw [← card_neighborFinset_eq_degree,
      ← Finset.card_filter_add_card_filter_not (s := G.neighborFinset x) (· ∈ Cs)]
    have : ((G.neighborFinset x).filter (fun a => ¬ a ∈ Cs)) =
        ((G.neighborFinset x).filter (· ∈ H)) ∪ ((G.neighborFinset x).filter (· ∈ R)) := by
      ext y; simp only [Finset.mem_filter, Finset.mem_union, hR, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨h1, h2⟩; by_cases hy : y ∈ H
        · exact Or.inl ⟨h1, hy⟩
        · exact Or.inr ⟨h1, h2, hy⟩
      · rintro (⟨h1, h2⟩ | ⟨h1, h2, -⟩)
        · exact ⟨h1, offCs y h2⟩
        · exact ⟨h1, h2⟩
    rw [this, Finset.card_union_of_disjoint, Nat.add_assoc]
    rw [Finset.disjoint_left]
    intro y h1 h2
    simp only [Finset.mem_filter, hR, Finset.mem_univ, true_and] at h1 h2
    exact h2.2.2 h1.2
  -- counting the vertex set
  have hn : Fintype.card V = c + H.card + R.card := by
    rw [← card_cset hD, ← Finset.card_univ]
    have : (Finset.univ : Finset V) = Cs ∪ H ∪ R := by
      ext y; simp only [Finset.mem_univ, Finset.mem_union, hR, Finset.mem_filter, true_iff]
      tauto
    rw [this, Finset.card_union_of_disjoint, Finset.card_union_of_disjoint]
    · rw [Finset.disjoint_left]; intro y h1 h2; exact offCs y h2 h1
    · rw [Finset.disjoint_left]; intro y h1 h2
      simp only [hR, Finset.mem_filter, Finset.mem_univ, true_and] at h2
      rcases Finset.mem_union.mp h1 with h | h
      · exact h2.1 h
      · exact h2.2 h
  -- the vertex `v`
  have hvR : ((G.neighborFinset v).filter (· ∈ R)).card = 0 := by
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro y hy hyR
    simp only [hR, Finset.mem_filter, Finset.mem_univ, true_and] at hyR
    rcases hC.cl v hv y ((mem_neighborFinset _ _ _).mp hy) with h | ⟨t, rfl⟩
    · exact hyR.2 h
    · exact hyR.1 (hD.mem_cset t)
  have hvH : ((G.neighborFinset v).filter (· ∈ H)).card + 1 ≤ H.card := by
    have : (G.neighborFinset v).filter (· ∈ H) ⊆ H.erase v := by
      intro y hy
      simp only [Finset.mem_filter, mem_neighborFinset] at hy
      exact Finset.mem_erase.mpr ⟨(G.ne_of_adj hy.1).symm, hy.2⟩
    have := Finset.card_le_card this
    rw [Finset.card_erase_of_mem hv] at this
    have : 1 ≤ H.card := Finset.card_pos.mpr ⟨v, hv⟩
    omega
  -- the successors
  have sH : ∀ s, Att G f H s → ((G.neighborFinset (f (s + 1))).filter (· ∈ H)).card = 0 := by
    intro s hs
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro y hy hyH
    exact G1 hD hC hs y hyH ((mem_neighborFinset _ _ _).mp hy)
  have disj : ∀ s j, Att G f H s → Att G f H (s + j) → 1 ≤ j → j < c →
      Disjoint ((G.neighborFinset (f (s + 1))).filter (· ∈ R))
        ((G.neighborFinset (f (s + j + 1))).filter (· ∈ R)) := by
    intro s j hs hsj hj hjc
    rw [Finset.disjoint_left]
    intro y h1 h2
    simp only [Finset.mem_filter, mem_neighborFinset, hR, Finset.mem_univ, true_and] at h1 h2
    exact G3 hD hC hs hsj hj hjc h1.2.2 (fun t ht => h1.2.1 (ht ▸ hD.mem_cset t)) h1.1 h2.1.symm
  have d12 := disj p1 (p2 - p1) a1 (by rw [show p1 + (p2 - p1) = p2 by omega]; exact a2)
    (by omega) (by omega)
  have d13 := disj p1 (p3 - p1) a1 (by rw [show p1 + (p3 - p1) = p3 by omega]; exact a3)
    (by omega) (by omega)
  have d23 := disj p2 (p3 - p2) a2 (by rw [show p2 + (p3 - p2) = p3 by omega]; exact a3)
    (by omega) (by omega)
  rw [show p1 + (p2 - p1) = p2 by omega] at d12
  rw [show p1 + (p3 - p1) = p3 by omega] at d13
  rw [show p2 + (p3 - p2) = p3 by omega] at d23
  have hRsum : ((G.neighborFinset (f (p1 + 1))).filter (· ∈ R)).card +
      ((G.neighborFinset (f (p2 + 1))).filter (· ∈ R)).card +
      ((G.neighborFinset (f (p3 + 1))).filter (· ∈ R)).card ≤ R.card := by
    rw [← Finset.card_union_of_disjoint d12, ← Finset.card_union_of_disjoint
      (Finset.disjoint_union_left.mpr ⟨d13, d23⟩)]
    apply Finset.card_le_card
    intro y hy
    simp only [Finset.mem_union, Finset.mem_filter] at hy
    rcases hy with (h | h) | h <;> exact h.2
  rw [split v, split (f (p1 + 1)), split (f (p2 + 1)), split (f (p3 + 1)), sH p1 a1, sH p2 a2,
    sH p3 a3, hvR, hn]
  omega



/-! ## Attachment sets and the gap bound -/

/-- Attachment vertices of `H` on the cycle. -/
def Aset (G : SimpleGraph V) [DecidableRel G.Adj] (c : ℕ) (f : ℕ → V) (H : Finset V) : Finset V :=
  ((Finset.range c).image f).filter (fun y => ∃ z ∈ H, G.Adj y z)

/-- Attachment vertices with at least two neighbours in `H`. -/
def Mset (G : SimpleGraph V) [DecidableRel G.Adj] (c : ℕ) (f : ℕ → V) (H : Finset V) : Finset V :=
  (Aset G c f H).filter (fun y => 2 ≤ (H.filter (G.Adj y)).card)

lemma two_nbrs {H : Finset V} [DecidableRel G.Adj] {y : V} (h : 2 ≤ (H.filter (G.Adj y)).card)
    (z' : V) : ∃ z ∈ H, G.Adj y z ∧ z ≠ z' := by
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (by omega : 1 < (H.filter (G.Adj y)).card)
  simp only [Finset.mem_filter] at ha hb
  by_cases h' : a = z'
  · exact ⟨b, hb.1, hb.2, fun e => hab (h'.trans e.symm)⟩
  · exact ⟨a, ha.1, ha.2, h'⟩

lemma gap_bound [DecidableRel G.Adj] (hD : Cy G c f) (hC : Comp G f H) :
    2 * (Aset G c f H).card + (Mset G c f H).card ≤ c := by
  have hc : 0 < c := by have := hD.three; omega
  set Ai := (Finset.range c).filter (fun t => ∃ z ∈ H, G.Adj (f t) z)
  set Mi := Ai.filter (fun t => 2 ≤ (H.filter (G.Adj (f t))).card)
  have injr : Set.InjOn f (Finset.range c : Set ℕ) := by
    intro i hi j hj h; exact hD.inj i j (Finset.mem_range.mp hi) (Finset.mem_range.mp hj) h
  have hA : (Aset G c f H).card = Ai.card := by
    rw [← Finset.card_image_of_injOn (injr.mono (Finset.coe_subset.mpr (Finset.filter_subset _ _)))]
    congr 1; ext y
    simp only [Aset, Ai, Att, Finset.mem_filter, Finset.mem_image, Finset.mem_range]
    constructor
    · rintro ⟨⟨t, ht, rfl⟩, h⟩; exact ⟨t, ⟨ht, h⟩, rfl⟩
    · rintro ⟨t, ⟨ht, h⟩, rfl⟩; exact ⟨⟨t, ht, rfl⟩, h⟩
  have hM : (Mset G c f H).card = Mi.card := by
    rw [← Finset.card_image_of_injOn (injr.mono (Finset.coe_subset.mpr
      ((Finset.filter_subset _ _).trans (Finset.filter_subset _ _))))]
    congr 1; ext y
    simp only [Mset, Aset, Mi, Ai, Att, Finset.mem_filter, Finset.mem_image, Finset.mem_range]
    constructor
    · rintro ⟨⟨⟨t, ht, rfl⟩, h⟩, h2⟩; exact ⟨t, ⟨⟨ht, h⟩, h2⟩, rfl⟩
    · rintro ⟨t, ⟨⟨ht, h⟩, h2⟩, rfl⟩; exact ⟨⟨⟨t, ht, rfl⟩, h⟩, h2⟩
  have attmod : ∀ s, Att G f H (s % c) → Att G f H s := by
    intro s ⟨z, hz, h⟩; exact ⟨z, hz, by rw [hD.mod]; exact h⟩
  set B1 := Ai.image (fun t => (t + 1) % c)
  set B2 := Mi.image (fun t => (t + 2) % c)
  have i1 : B1.card = Ai.card := by
    apply Finset.card_image_of_injOn
    intro s hs t ht hst
    simp only [Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq, Ai] at hs ht
    have : (s + 1) % c = (t + 1) % c := hst
    have h2 := Nat.ModEq.add_right_cancel' 1 this
    rwa [Nat.ModEq, Nat.mod_eq_of_lt hs.1, Nat.mod_eq_of_lt ht.1] at h2
  have i2 : B2.card = Mi.card := by
    apply Finset.card_image_of_injOn
    intro s hs t ht hst
    have hs' := Finset.mem_range.mp (Finset.mem_filter.mp (Finset.mem_filter.mp
      (Finset.mem_coe.mp hs)).1).1
    have ht' := Finset.mem_range.mp (Finset.mem_filter.mp (Finset.mem_filter.mp
      (Finset.mem_coe.mp ht)).1).1
    have : (s + 2) % c = (t + 2) % c := hst
    have h2 := Nat.ModEq.add_right_cancel' 2 this
    rwa [Nat.ModEq, Nat.mod_eq_of_lt hs', Nat.mod_eq_of_lt ht'] at h2
  have d1 : Disjoint Ai B1 := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hx'
    simp only [Ai, Finset.mem_filter] at hx ht
    obtain ⟨z, hz, h⟩ := attmod _ hx.2
    exact G1 hD hC ht.2 z hz h
  have d2 : Disjoint (Ai ∪ B1) B2 := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hx'
    simp only [Mi, Ai, Finset.mem_filter] at ht
    rcases Finset.mem_union.mp hx with hx | hx
    · simp only [Ai, Finset.mem_filter] at hx
      obtain ⟨z', hz', h'⟩ := attmod _ hx.2
      obtain ⟨z, hz, hzt, hzz⟩ := two_nbrs ht.2 z'
      obtain ⟨X, hX, hK, h1, h2⟩ := ph_two hC hz hz' hzz hzt h'
      have := R1 hD hX (b := t) (j := 2) (by omega) (by have := hD.three; omega) h1 h2
      omega
    · obtain ⟨s, hs, hst⟩ := Finset.mem_image.mp hx
      simp only [Ai, Finset.mem_filter] at hs
      have h2 : s % c = (t + 1) % c := Nat.ModEq.add_right_cancel' 1
        (show (s + 1) % c = (t + 1 + 1) % c from hst)
      have : f s = f (t + 1) := by rw [hD.eq_iff]; exact h2
      obtain ⟨z, hz, h⟩ := hs.2
      exact G1 hD hC ht.1.2 z hz (this ▸ h)
  have sub : Ai ∪ B1 ∪ B2 ⊆ Finset.range c := by
    intro x hx
    simp only [Finset.mem_union, Finset.mem_image, B1, B2] at hx
    rcases hx with (hx | ⟨t, -, rfl⟩) | ⟨t, -, rfl⟩
    · exact (Finset.mem_filter.mp hx).1
    · exact Finset.mem_range.mpr (Nat.mod_lt _ hc)
    · exact Finset.mem_range.mpr (Nat.mod_lt _ hc)
  have := Finset.card_le_card sub
  rw [Finset.card_union_of_disjoint d2, Finset.card_union_of_disjoint d1, Finset.card_range,
    i1, i2] at this
  omega



/-! ## The four-vertex contradiction, for any three suitable attachments -/

lemma mem_Aset [DecidableRel G.Adj] {y : V} :
    y ∈ Aset G c f H ↔ (∃ t < c, f t = y) ∧ ∃ z ∈ H, G.Adj y z := by
  simp [Aset]

lemma four_sorted [DecidableRel G.Adj] (hD : Cy G c f) (hC : Comp G f H) {δ : ℕ}
    (hδ : ∀ x, δ ≤ G.degree x) (hn : Fintype.card V + 6 ≤ 4 * δ) {v : V} (hv : v ∈ H)
    (S : Finset V) (hSA : S ⊆ Aset G c f H)
    (hP : ∀ y ∈ S, ∀ y' ∈ S, y ≠ y' → PH G f y y' 2)
    (hc2 : ∀ t, G.Adj v (f t) → f t ∉ S → ∀ y ∈ S, PH G f y (f t) 3)
    {p1 p2 p3 : ℕ} (h12 : p1 < p2) (h23 : p2 < p3) (h31 : p3 < p1 + c)
    (m1 : f p1 ∈ S) (m2 : f p2 ∈ S) (m3 : f p3 ∈ S)
    (hS : ∀ y ∈ S, y = f p1 ∨ y = f p2 ∨ y = f p3) : False := by
  have att : ∀ p, f p ∈ S → Att G f H p := fun p hp => (mem_Aset.mp (hSA hp)).2
  have n12 : f p1 ≠ f p2 := hD.ne_of_window (b := p1) le_rfl (by omega) (by omega) (by omega)
    (by omega)
  have n23 : f p2 ≠ f p3 := hD.ne_of_window (b := p1) (by omega) (by omega) (by omega) (by omega)
    (by omega)
  have n13 : f p1 ≠ f p3 := hD.ne_of_window (b := p1) le_rfl (by omega) (by omega) (by omega)
    (by omega)
  have h := four_count hD hC hv h12 h23 h31 (att p1 m1) (att p2 m2) (att p3 m3)
    (hP _ m1 _ m2 n12) (hP _ m2 _ m3 n23) (hP _ m1 _ m3 n13)
    (by
      intro t ht e1 e2 e3
      have hn : f t ∉ S := by
        intro hm; rcases hS _ hm with h | h | h
        · exact e1 h
        · exact e2 h
        · exact e3 h
      exact ⟨hc2 t ht hn _ m1, hc2 t ht hn _ m2, hc2 t ht hn _ m3⟩)
  have := hδ v; have := hδ (f (p1 + 1)); have := hδ (f (p2 + 1)); have := hδ (f (p3 + 1))
  omega

lemma four_ok [DecidableRel G.Adj] (hD : Cy G c f) (hC : Comp G f H) {δ : ℕ}
    (hδ : ∀ x, δ ≤ G.degree x) (hn : Fintype.card V + 6 ≤ 4 * δ) {v : V} (hv : v ∈ H)
    (S : Finset V) (hS3 : S.card = 3) (hSA : S ⊆ Aset G c f H)
    (hP : ∀ y ∈ S, ∀ y' ∈ S, y ≠ y' → PH G f y y' 2)
    (hc2 : ∀ t, G.Adj v (f t) → f t ∉ S → ∀ y ∈ S, PH G f y (f t) 3) : False := by
  obtain ⟨x1, x2, x3, h12, h13, h23, rfl⟩ := Finset.card_eq_three.mp hS3
  obtain ⟨⟨t1, t1c, rfl⟩, -⟩ := mem_Aset.mp (hSA (show x1 ∈ ({x1, x2, x3} : Finset V) by simp))
  obtain ⟨⟨t2, t2c, rfl⟩, -⟩ := mem_Aset.mp (hSA (show x2 ∈ ({f t1, x2, x3} : Finset V) by simp))
  obtain ⟨⟨t3, t3c, rfl⟩, -⟩ := mem_Aset.mp (hSA (show x3 ∈ ({f t1, f t2, x3} : Finset V) by simp))
  have ne : ∀ i j, f i ≠ f j → i ≠ j := fun i j h e => h (e ▸ rfl)
  have a12 := ne _ _ h12; have a13 := ne _ _ h13; have a23 := ne _ _ h23
  have fs := fun p1 p2 p3 => @four_sorted _ _ _ G c f H _ hD hC δ hδ hn v hv _ hSA hP hc2 p1 p2 p3
  rcases Nat.lt_or_gt_of_ne a12 with b12 | b12 <;> rcases Nat.lt_or_gt_of_ne a13 with b13 | b13 <;>
    rcases Nat.lt_or_gt_of_ne a23 with b23 | b23
  · exact fs t1 t2 t3 b12 b23 (by omega) (by simp) (by simp) (by simp)
      (by intro y hy; simp at hy; tauto)
  · exact fs t1 t3 t2 b13 b23 (by omega) (by simp) (by simp) (by simp)
      (by intro y hy; simp at hy; tauto)
  · omega
  · exact fs t3 t1 t2 b13 b12 (by omega) (by simp) (by simp) (by simp)
      (by intro y hy; simp at hy; tauto)
  · exact fs t2 t1 t3 b12 b13 (by omega) (by simp) (by simp) (by simp)
      (by intro y hy; simp at hy; tauto)
  · omega
  · exact fs t2 t3 t1 b23 b13 (by omega) (by simp) (by simp) (by simp)
      (by intro y hy; simp at hy; tauto)
  · exact fs t3 t2 t1 b23 b12 (by omega) (by simp) (by simp) (by simp)
      (by intro y hy; simp at hy; tauto)



/-! ## Structure inside `H` -/

/-- Valid path lists in `H`. -/
def VL (G : SimpleGraph V) (H : Finset V) (P : List V) : Prop :=
  P.Nodup ∧ P.IsChain G.Adj ∧ ∀ z ∈ P, z ∈ H

lemma VL.length_le {P : List V} (h : VL G H P) : P.length ≤ H.card := by
  rw [← List.toFinset_card_of_nodup h.1]
  exact Finset.card_le_card (fun z hz => h.2.2 z (List.mem_toFinset.mp hz))

/-- A path list in `H` whose first vertex has all its `H`-neighbours on the list. -/
lemma exists_headmax {x : V} (hx : x ∈ H) :
    ∃ v Q, VL G H (v :: Q) ∧ ∀ u ∈ H, G.Adj v u → u ∈ v :: Q := by
  suffices ∀ k, ∀ v Q, VL G H (v :: Q) → H.card - (v :: Q).length ≤ k →
      ∃ v' Q', VL G H (v' :: Q') ∧ ∀ u ∈ H, G.Adj v' u → u ∈ v' :: Q' from
    this _ x [] ⟨List.nodup_singleton x, List.isChain_singleton x, by simpa using hx⟩ le_rfl
  intro k
  induction k with
  | zero =>
    intro v Q hP hk
    refine ⟨v, Q, hP, fun u hu huv => ?_⟩
    by_contra hn
    have : VL G H (u :: v :: Q) := ⟨List.nodup_cons.mpr ⟨hn, hP.1⟩,
      List.IsChain.cons_cons huv.symm hP.2.1, by
        intro z hz; rcases List.mem_cons.mp hz with rfl | hz
        · exact hu
        · exact hP.2.2 z hz⟩
    have := this.length_le; simp at this hk; omega
  | succ k ih =>
    intro v Q hP hk
    by_cases hmax : ∀ u ∈ H, G.Adj v u → u ∈ v :: Q
    · exact ⟨v, Q, hP, hmax⟩
    · push_neg at hmax
      obtain ⟨u, hu, huv, hn⟩ := hmax
      exact ih u (v :: Q) ⟨List.nodup_cons.mpr ⟨hn, hP.1⟩, List.IsChain.cons_cons huv.symm hP.2.1, by
        intro z hz; rcases List.mem_cons.mp hz with rfl | hz
        · exact hu
        · exact hP.2.2 z hz⟩ (by simp at hk ⊢; omega)

lemma HP.three_le {x y : V} {X : List V} (h : HP G H x y X) (hxy : ¬ G.Adj x y) (hne : x ≠ y) :
    3 ≤ X.length := by
  obtain ⟨-, hch, -, h1, h2⟩ := h
  match X, hch, h1, h2 with
  | [a], _, h1, h2 => simp at h1 h2; exact absurd (h1.symm.trans h2) hne
  | [a, b], hch, h1, h2 =>
    simp at h1 h2; subst h1; subst h2
    exact absurd (List.isChain_cons_cons.mp hch).1 hxy
  | a :: b :: d :: l, _, _, _ => simp

lemma HP_of_VL {P : List V} (h : VL G H P) {x y : V} (hx : P.head? = some x)
    (hy : P.getLast? = some y) : HP G H x y P := ⟨h.1, h.2.1, h.2.2, hx, hy⟩

/-- The endpoint of a head-maximal path: when it has two `H`-neighbours, every other vertex of `H`
reaches it by an `H`-path with at least three vertices. -/
lemma endpoint (hC : Comp G f H) {x : V} (hx : x ∈ H) :
    ∃ v ∈ H, (∀ u ∈ H, G.Adj v u → u ∈ H → True) ∧
      ∀ u ∈ H, u ≠ v → (∃ w w', w ∈ H ∧ w' ∈ H ∧ w ≠ w' ∧ G.Adj v w ∧ G.Adj v w') →
        ∃ X, HP G H u v X ∧ 3 ≤ X.length := by
  obtain ⟨v, Q, hP, hmax⟩ := exists_headmax (G := G) hx
  have hvH : v ∈ H := hP.2.2 v (by simp)
  refine ⟨v, hvH, fun _ _ _ _ => trivial, ?_⟩
  intro u hu huv ⟨w, w', hw, hw', hww, hvw, hvw'⟩
  by_cases hadj : G.Adj u v
  · -- `u` lies on the path
    have huP : u ∈ Q := by
      rcases List.mem_cons.mp (hmax u hu hadj.symm) with h | h
      · exact absurd h huv
      · exact h
    obtain ⟨Q1, Q2, rfl⟩ := List.append_of_mem huP
    have hnd := hP.1
    have hch := hP.2.2
    have hc := hP.2.1
    rcases Q1 with _ | ⟨q, Q1⟩
    · -- `u` is the second vertex; use the other neighbour, which lies further along
      obtain ⟨w0, hw0, hvw0, hw0u⟩ : ∃ w0 ∈ H, G.Adj v w0 ∧ w0 ≠ u := by
        by_cases h : w = u
        · exact ⟨w', hw', hvw', fun e => hww (h.trans e.symm)⟩
        · exact ⟨w, hw, hvw, h⟩
      have hw0Q : w0 ∈ Q2 := by
        have := hmax w0 hw0 hvw0
        simp at this
        rcases this with h | h | h
        · exact absurd h (G.ne_of_adj hvw0).symm
        · exact absurd h hw0u
        · exact h
      obtain ⟨R1, R2, rfl⟩ := List.append_of_mem hw0Q
      have hpre : List.Sublist (v :: (u :: R1 ++ [w0])) (v :: ([] ++ u :: (R1 ++ w0 :: R2))) := by
        simp only [List.nil_append]
        refine List.Sublist.cons₂ v ?_
        have : u :: (R1 ++ w0 :: R2) = (u :: R1 ++ [w0]) ++ R2 := by simp
        rw [this]; exact List.sublist_append_left _ _
      have hl : (u :: R1 ++ [w0]).getLast? = some w0 := List.getLast?_concat
      refine ⟨(u :: R1 ++ [w0]) ++ [v], ⟨?_, ?_, ?_, by simp, List.getLast?_concat⟩, by simp⟩
      · exact (List.perm_append_singleton v _).nodup_iff.mpr (hnd.sublist hpre)
      · have hc2 : (v :: (u :: R1 ++ [w0])).IsChain G.Adj := by
          have : (v :: (u :: R1 ++ [w0]) ++ R2).IsChain G.Adj := by simpa using hc
          exact (List.isChain_append.mp this).1
        have hc3 : (u :: R1 ++ [w0]).IsChain G.Adj := (List.isChain_cons.mp hc2).2
        refine hc3.append (List.isChain_singleton v) ?_
        intro a ha b hb
        rw [hl] at ha
        obtain rfl : w0 = a := by simpa using ha
        obtain rfl : v = b := by simpa using hb
        exact hvw0.symm
      · intro z hz
        exact hch z (hpre.subset ((List.perm_append_singleton v _).mem_iff.mp hz))
    · -- `u` is further along: walk back along the path
      refine ⟨(v :: q :: Q1 ++ [u]).reverse, ⟨?_, ?_, ?_, by simp, by rw [List.getLast?_reverse]; rfl⟩, by simp⟩
      · rw [List.nodup_reverse]
        have : (v :: q :: Q1 ++ [u] ++ Q2).Nodup := by simpa using hnd
        exact (List.nodup_append.mp this).1
      · rw [List.isChain_reverse]
        have : (v :: q :: Q1 ++ [u] ++ Q2).IsChain G.Adj := by simpa using hc
        exact (List.isChain_append.mp this).1.imp (fun _ _ h => h.symm)
      · intro z hz; exact hch z (by simp at hz ⊢; tauto)
  · obtain ⟨X, hX⟩ := hC.conn u hu v hvH
    exact ⟨X, hX, hX.three_le hadj huv⟩



/-! ## Attachment types -/

section types

variable [DecidableRel G.Adj]

/-- Neighbours on the cycle. -/
def NC (G : SimpleGraph V) [DecidableRel G.Adj] (c : ℕ) (f : ℕ → V) (x : V) : Finset V :=
  (G.neighborFinset x).filter (· ∈ (Finset.range c).image f)

/-- Vertices of `H` holding a private attachment. -/
def X1 (G : SimpleGraph V) [DecidableRel G.Adj] (c : ℕ) (f : ℕ → V) (H : Finset V) : Finset V :=
  H.filter (fun x => ∃ a ∈ Aset G c f H, H.filter (G.Adj a) = {x})

/-- The attachment types. -/
def Ty (G : SimpleGraph V) [DecidableRel G.Adj] (c : ℕ) (f : ℕ → V) (H : Finset V) :
    Finset (V ⊕ V) :=
  (Mset G c f H).disjSum (X1 G c f H)

open Classical in
/-- A representative attachment of each type. -/
noncomputable def rep (G : SimpleGraph V) [DecidableRel G.Adj] (c : ℕ) (f : ℕ → V) (H : Finset V) :
    V ⊕ V → V
  | Sum.inl a => a
  | Sum.inr x => if h : ∃ a ∈ Aset G c f H, H.filter (G.Adj a) = {x} then h.choose else x

lemma mem_Mset {y : V} : y ∈ Mset G c f H ↔ y ∈ Aset G c f H ∧ 2 ≤ (H.filter (G.Adj y)).card := by
  simp [Mset]

lemma Aset_dich {a : V} (ha : a ∈ Aset G c f H) :
    a ∈ Mset G c f H ∨ ∃ x ∈ H, H.filter (G.Adj a) = {x} := by
  by_cases h2 : 2 ≤ (H.filter (G.Adj a)).card
  · exact Or.inl (mem_Mset.mpr ⟨ha, h2⟩)
  · right
    obtain ⟨-, z, hz, hza⟩ := mem_Aset.mp ha
    have h1 : (H.filter (G.Adj a)).card = 1 := by
      have : 0 < (H.filter (G.Adj a)).card :=
        Finset.card_pos.mpr ⟨z, Finset.mem_filter.mpr ⟨hz, hza⟩⟩
      omega
    obtain ⟨x, hx⟩ := Finset.card_eq_one.mp h1
    have : x ∈ H.filter (G.Adj a) := by rw [hx]; simp
    exact ⟨x, (Finset.mem_filter.mp this).1, hx⟩

lemma rep_inl (a : V) : rep G c f H (Sum.inl a) = a := rfl

lemma rep_inr {x : V} (hx : x ∈ X1 G c f H) :
    rep G c f H (Sum.inr x) ∈ Aset G c f H ∧
      H.filter (G.Adj (rep G c f H (Sum.inr x))) = {x} := by
  have h : ∃ a ∈ Aset G c f H, H.filter (G.Adj a) = {x} := (Finset.mem_filter.mp hx).2
  simp only [rep, dif_pos h]
  exact h.choose_spec

lemma rep_mem {s : V ⊕ V} (hs : s ∈ Ty G c f H) : rep G c f H s ∈ Aset G c f H := by
  rcases s with a | x
  · simp only [Ty, Finset.inl_mem_disjSum] at hs; exact (mem_Mset.mp hs).1
  · simp only [Ty, Finset.inr_mem_disjSum] at hs; exact (rep_inr hs).1

lemma single_ne_multi {a b : V} {x : V} (ha : H.filter (G.Adj a) = {x})
    (hb : 2 ≤ (H.filter (G.Adj b)).card) : a ≠ b := by
  rintro rfl; rw [ha] at hb; simp at hb

lemma rep_pair (hC : Comp G f H) {s s' : V ⊕ V} (hs : s ∈ Ty G c f H) (hs' : s' ∈ Ty G c f H)
    (hne : s ≠ s') :
    rep G c f H s ≠ rep G c f H s' ∧ PH G f (rep G c f H s) (rep G c f H s') 2 := by
  rcases s with a | x <;> rcases s' with b | y <;>
    simp only [Ty, Finset.inl_mem_disjSum, Finset.inr_mem_disjSum] at hs hs'
  · have hab : a ≠ b := fun h => hne (h ▸ rfl)
    refine ⟨hab, ?_⟩
    obtain ⟨-, z', hz', hbz'⟩ := mem_Aset.mp (mem_Mset.mp hs').1
    obtain ⟨z, hz, haz, hzz⟩ := two_nbrs (mem_Mset.mp hs).2 z'
    exact ph_two hC hz hz' hzz haz hbz'
  · obtain ⟨-, hy⟩ := rep_inr hs'
    have hyH : y ∈ H := (Finset.mem_filter.mp hs').1
    refine ⟨(single_ne_multi hy (mem_Mset.mp hs).2).symm, ?_⟩
    obtain ⟨z, hz, haz, hzz⟩ := two_nbrs (mem_Mset.mp hs).2 y
    have : G.Adj (rep G c f H (Sum.inr y)) y := by
      have : y ∈ H.filter (G.Adj (rep G c f H (Sum.inr y))) := by rw [hy]; simp
      exact (Finset.mem_filter.mp this).2
    exact ph_two hC hz hyH hzz haz this
  · obtain ⟨-, hx⟩ := rep_inr hs
    have hxH : x ∈ H := (Finset.mem_filter.mp hs).1
    refine ⟨single_ne_multi hx (mem_Mset.mp hs').2, ?_⟩
    obtain ⟨z, hz, hbz, hzz⟩ := two_nbrs (mem_Mset.mp hs').2 x
    have : G.Adj (rep G c f H (Sum.inr x)) x := by
      have : x ∈ H.filter (G.Adj (rep G c f H (Sum.inr x))) := by rw [hx]; simp
      exact (Finset.mem_filter.mp this).2
    exact ph_two hC hxH hz (Ne.symm hzz) this hbz
  · have hxy : x ≠ y := fun h => hne (h ▸ rfl)
    obtain ⟨-, hx⟩ := rep_inr hs
    obtain ⟨-, hy⟩ := rep_inr hs'
    refine ⟨fun h => hxy (by rw [h] at hx; rw [hx] at hy; simpa using hy), ?_⟩
    have ax : G.Adj (rep G c f H (Sum.inr x)) x := by
      have : x ∈ H.filter (G.Adj (rep G c f H (Sum.inr x))) := by rw [hx]; simp
      exact (Finset.mem_filter.mp this).2
    have ay : G.Adj (rep G c f H (Sum.inr y)) y := by
      have : y ∈ H.filter (G.Adj (rep G c f H (Sum.inr y))) := by rw [hy]; simp
      exact (Finset.mem_filter.mp this).2
    exact ph_two hC (Finset.mem_filter.mp hs).1 (Finset.mem_filter.mp hs').1 hxy ax ay

/-- Three types give three suitable attachments. -/
lemma pick (hC : Comp G f H) {U : Finset (V ⊕ V)} (hU : U ⊆ Ty G c f H) (h3 : U.card = 3) :
    (U.image (rep G c f H)).card = 3 ∧ U.image (rep G c f H) ⊆ Aset G c f H ∧
      ∀ y ∈ U.image (rep G c f H), ∀ y' ∈ U.image (rep G c f H), y ≠ y' → PH G f y y' 2 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [Finset.card_image_of_injOn, h3]
    intro s hs s' hs' h
    by_contra hne
    exact (rep_pair hC (hU hs) (hU hs') hne).1 h
  · intro y hy
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hy
    exact rep_mem (hU hs)
  · intro y hy y' hy' hne
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨s', hs', rfl⟩ := Finset.mem_image.mp hy'
    exact (rep_pair hC (hU hs) (hU hs') (fun h => hne (h ▸ rfl))).2

lemma NC_sub (hD : Cy G c f) {x : V} (hx : x ∈ H) : NC G c f x ⊆ Aset G c f H := by
  intro y hy
  simp only [NC, Finset.mem_filter, mem_neighborFinset] at hy
  rw [Aset, Finset.mem_filter]
  exact ⟨hy.2, x, hx, hy.1.symm⟩

lemma degH (hD : Cy G c f) (hC : Comp G f H) {x : V} (hx : x ∈ H) :
    G.degree x = (NC G c f x).card + (H.filter (G.Adj x)).card := by
  rw [← card_neighborFinset_eq_degree, NC,
    ← Finset.card_filter_add_card_filter_not (s := G.neighborFinset x)
      (· ∈ (Finset.range c).image f)]
  congr 1
  apply Finset.card_bij (fun y _ => y)
  · intro y hy
    simp only [Finset.mem_filter, mem_neighborFinset] at hy ⊢
    rcases hC.cl x hx y hy.1 with h | ⟨t, rfl⟩
    · exact ⟨h, hy.1⟩
    · exact absurd (hD.mem_cset t) hy.2
  · intro a _ b _ h; exact h
  · intro y hy
    simp only [Finset.mem_filter, mem_neighborFinset] at hy
    refine ⟨y, ?_, rfl⟩
    simp only [Finset.mem_filter, mem_neighborFinset]
    refine ⟨hy.2, fun hm => ?_⟩
    obtain ⟨t, -, rfl⟩ := Finset.mem_image.mp hm
    exact hC.off _ hy.1 t rfl

lemma card_CH (hD : Cy G c f) (hC : Comp G f H) : c + H.card ≤ Fintype.card V := by
  rw [← card_cset hD, ← Finset.card_union_of_disjoint]
  · exact Finset.card_le_univ _
  · rw [Finset.disjoint_left]
    intro y hy hyH
    obtain ⟨t, -, rfl⟩ := Finset.mem_image.mp hy
    exact hC.off _ hyH t rfl

end types



/-! ## The case analysis -/

section core

variable [DecidableRel G.Adj]

lemma ph3_of (hC : Comp G f H) {u v y w : V} {X : List V} (hX : HP G H u v X) (h3 : 3 ≤ X.length)
    (hyu : G.Adj y u) (hvw : G.Adj v w) : PH G f y w 3 :=
  ⟨X, hX.offL hC, h3, by intro z hz; rw [hX.2.2.2.1] at hz; cases hz; exact hyu,
    by intro z hz; rw [hX.2.2.2.2] at hz; cases hz; exact hvw⟩

lemma exists_nbr (hC : Comp G f H) (h2 : 2 ≤ H.card) {v : V} (hv : v ∈ H) :
    ∃ w ∈ H, G.Adj v w := by
  obtain ⟨u, hu, huv⟩ := Finset.exists_mem_ne (by omega : 1 < H.card) v
  obtain ⟨X, hnd, hch, hsub, h1, h2⟩ := hC.conn v hv u hu
  match X, hch, hsub, h1, h2 with
  | [a], _, _, h1, h2 => simp at h1 h2; exact absurd (h2.symm.trans h1) huv
  | a :: b :: l, hch, hsub, h1, _ =>
    simp at h1; subst h1
    exact ⟨b, hsub b (by simp), (List.isChain_cons_cons.mp hch).1⟩

lemma Aset_nbr {a x : V} (ha : a ∈ Aset G c f H) (hx : x ∈ H) (hax : G.Adj a x)
    (hs : ∀ y, H.filter (G.Adj a) = {y} → False) : a ∈ Mset G c f H := by
  rcases Aset_dich ha with h | ⟨y, -, hy⟩
  · exact h
  · exact (hs y hy).elim

lemma mem_single {a x y : V} (h : H.filter (G.Adj a) = {y}) (hx : x ∈ H) (hax : G.Adj a x) :
    x = y := by
  have : x ∈ H.filter (G.Adj a) := Finset.mem_filter.mpr ⟨hx, hax⟩
  rw [h] at this; simpa using this

lemma core (hD : Cy G c f) (hC : Comp G f H) {δ : ℕ} (hδ : ∀ x, δ ≤ G.degree x)
    (hn : Fintype.card V + 6 ≤ 4 * δ) (h3 : 3 ≤ H.card)
    (hK : ∀ S : Finset V, S.card ≤ 2 → ∀ X : Finset V, (∀ a ∈ X, a ∉ S) →
      (∀ a ∈ X, ∀ b, G.Adj a b → b ∉ S → b ∈ X) → X.Nonempty → ∀ y, y ∉ S → y ∉ X → False) :
    False := by
  have hcn := card_CH hD hC
  have hgap := gap_bound hD hC
  have hc3 := hD.three
  have hdeg : ∀ x ∈ H, δ ≤ (NC G c f x).card + (H.filter (G.Adj x)).card := by
    intro x hx; rw [← degH hD hC hx]; exact hδ x
  have hNHle : ∀ x ∈ H, (H.filter (G.Adj x)).card + 1 ≤ H.card := by
    intro x hx
    have : H.filter (G.Adj x) ⊆ H.erase x := by
      intro y hy; simp only [Finset.mem_filter] at hy
      exact Finset.mem_erase.mpr ⟨(G.ne_of_adj hy.2).symm, hy.1⟩
    have := Finset.card_le_card this
    rw [Finset.card_erase_of_mem hx] at this; omega
  have offA : ∀ y ∈ H, y ∉ Aset G c f H := by
    intro y hy hA
    obtain ⟨⟨t, -, rfl⟩, -⟩ := mem_Aset.mp hA
    exact hC.off _ hy t rfl
  have nbrA : ∀ x ∈ H, ∀ t, G.Adj x (f t) → f t ∈ Aset G c f H := by
    intro x hx t h
    rw [Aset, Finset.mem_filter]; exact ⟨hD.mem_cset t, x, hx, h.symm⟩
  have hTy : (Ty G c f H).card = (Mset G c f H).card + (X1 G c f H).card := by
    simp [Ty, Finset.card_disjSum]
  have hX1H : X1 G c f H ⊆ H := Finset.filter_subset _ _
  -- holders
  have holder : ∀ x ∈ H, ∀ a ∈ Aset G c f H, H.filter (G.Adj a) = {x} → x ∈ X1 G c f H := by
    intro x hx a ha h; exact Finset.mem_filter.mpr ⟨hx, a, ha, h⟩
  -- a type of a C-neighbour of a non-holder
  have nonholder : ∀ x ∈ H, x ∉ X1 G c f H → ∀ t, G.Adj x (f t) → f t ∈ Mset G c f H := by
    intro x hx hx1 t h
    exact Aset_nbr (nbrA x hx t h) hx h.symm
      (fun y hy => hx1 (mem_single hy hx h.symm ▸ holder y (by
        have := mem_single hy hx h.symm; rw [← this]; exact hx) _ (nbrA x hx t h) hy))
  ------------------------------------------------------------------
  -- Step 0: at least three types
  have hT3 : 3 ≤ (Ty G c f H).card := by
    by_contra hlt
    push_neg at hlt
    obtain ⟨S, hSd⟩ : ∃ S, S = Mset G c f H ∪ X1 G c f H := ⟨_, rfl⟩
    have hS : S.card ≤ 2 := by
      have := Finset.card_union_le (Mset G c f H) (X1 G c f H); rw [← hSd] at this; omega
    have hX1c : (X1 G c f H).card ≤ 2 := by omega
    have hXne : (H \ X1 G c f H).Nonempty := by
      rw [← Finset.card_pos, Finset.card_sdiff_of_subset hX1H]; omega
    -- a cycle vertex which is not an attachment
    obtain ⟨y, hyC, hyA⟩ : ∃ t, f t ∉ Aset G c f H ∧ True := by
      by_cases h0 : f 0 ∈ Aset G c f H
      · refine ⟨1, fun h1 => ?_, trivial⟩
        obtain ⟨-, z, hz, hza⟩ := mem_Aset.mp h1
        exact G1 hD hC (s := 0) (mem_Aset.mp h0).2 z hz (by simpa using hza)
      · exact ⟨0, h0, trivial⟩
    refine hK S hS (H \ X1 G c f H) ?_ ?_ hXne (f y) ?_ ?_
    · intro a ha haS
      rw [Finset.mem_sdiff] at ha
      rw [hSd] at haS
      rcases Finset.mem_union.mp haS with h | h
      · exact offA a ha.1 (mem_Mset.mp h).1
      · exact ha.2 h
    · intro a ha b hab hbS
      rw [Finset.mem_sdiff] at ha
      rcases hC.cl a ha.1 b hab with hb | ⟨t, rfl⟩
      · exact Finset.mem_sdiff.mpr ⟨hb, fun h => hbS (hSd ▸ Finset.mem_union_right _ h)⟩
      · exfalso
        exact hbS (hSd ▸ Finset.mem_union_left _ (nonholder a ha.1 ha.2 t hab))
    · intro h
      rw [hSd] at h
      rcases Finset.mem_union.mp h with h | h
      · exact hyC (mem_Mset.mp h).1
      · exact hC.off _ (hX1H h) y rfl
    · intro h; exact hC.off _ (Finset.mem_sdiff.mp h).1 y rfl
  ------------------------------------------------------------------
  have adj_single : ∀ a x, H.filter (G.Adj a) = {x} → G.Adj a x := by
    intro a x h
    have : x ∈ H.filter (G.Adj a) := by rw [h]; simp
    exact (Finset.mem_filter.mp this).2
  -- the four-vertex count, packaged
  have run : ∀ (U : Finset (V ⊕ V)), U ⊆ Ty G c f H → U.card = 3 → ∀ v ∈ H,
      (∀ t, G.Adj v (f t) → f t ∉ U.image (rep G c f H) →
        ∀ y ∈ U.image (rep G c f H), PH G f y (f t) 3) → False := by
    intro U hU hU3 v hv hc2
    obtain ⟨h1, h2, h3⟩ := pick hC hU hU3
    exact four_ok hD hC hδ hn hv _ h1 h2 h3 hc2
  -- reps of types in `U` all lie in `S`; a C-neighbour of type in `U` is in `S`
  have inS : ∀ (U : Finset (V ⊕ V)) (a : V), Sum.inl a ∈ U → a ∈ U.image (rep G c f H) :=
    fun U a h => Finset.mem_image.mpr ⟨_, h, rfl⟩
  rcases Nat.lt_or_ge 3 (Ty G c f H).card with hT4 | hT3'
  swap
  · ------------------------------------------------------------------
    -- Step 1: exactly three types
    have hTeq : (Ty G c f H).card = 3 := by omega
    by_cases hex : ∃ v ∈ H, v ∉ X1 G c f H
    · obtain ⟨v, hv, hv1⟩ := hex
      refine run _ subset_rfl hTeq v hv ?_
      intro t ht hS
      exfalso
      have hM := nonholder v hv hv1 t ht
      exact hS (inS _ _ (by simp [Ty, hM]))
    · push_neg at hex
      have hXeq : X1 G c f H = H := Finset.Subset.antisymm hX1H hex
      have hX1c := Finset.card_le_card hX1H
      have hM0 : (Mset G c f H).card = 0 := by rw [hXeq] at hTy; omega
      have hH3 : H.card = 3 := by rw [hXeq] at hTy; omega
      have single : ∀ a ∈ Aset G c f H, ∃ x ∈ H, H.filter (G.Adj a) = {x} := by
        intro a ha
        rcases Aset_dich ha with h | h
        · rw [Finset.card_eq_zero] at hM0; rw [hM0] at h; simp at h
        · exact h
      have hdisj : (H : Set V).PairwiseDisjoint (NC G c f) := by
        intro x hx x' hx' hne
        rw [Function.onFun, Finset.disjoint_left]
        intro a ha ha'
        have haA := NC_sub hD hx ha
        simp only [NC, Finset.mem_filter, mem_neighborFinset] at ha ha'
        obtain ⟨y, -, hy⟩ := single a haA
        exact hne ((mem_single hy hx ha.1.symm).trans (mem_single hy hx' ha'.1.symm).symm)
      have hsub : H.biUnion (NC G c f) ⊆ Aset G c f H := by
        intro a ha
        obtain ⟨x, hx, hax⟩ := Finset.mem_biUnion.mp ha
        exact NC_sub hD hx hax
      have hcard := Finset.card_le_card hsub
      rw [Finset.card_biUnion hdisj] at hcard
      have hsum : H.card • (δ - 2) ≤ ∑ x ∈ H, (NC G c f x).card := by
        apply Finset.card_nsmul_le_sum
        intro x hx; have := hdeg x hx; have := hNHle x hx; omega
      rw [smul_eq_mul, hH3] at hsum
      omega
  ------------------------------------------------------------------
  -- Step 2: at least four types
  obtain ⟨x0, hx0⟩ : H.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨v, hv, -, hend⟩ := endpoint hC hx0
  obtain ⟨z, hz, hvz⟩ := exists_nbr hC (by omega) hv
  by_cases h2 : 2 ≤ (H.filter (G.Adj v)).card
  · -- (I) the endpoint has two neighbours in `H`
    obtain ⟨w, hw, w', hw', hww⟩ := Finset.one_lt_card.mp (by omega : 1 < (H.filter (G.Adj v)).card)
    simp only [Finset.mem_filter] at hw hw'
    have hU0 : 3 ≤ ((Ty G c f H).erase (Sum.inr v)).card := by
      have := Finset.pred_card_le_card_erase (s := Ty G c f H) (a := Sum.inr v); omega
    obtain ⟨U, hUs, hU3⟩ := Finset.exists_subset_card_eq hU0
    refine run U (hUs.trans (Finset.erase_subset _ _)) hU3 v hv ?_
    intro t ht _ y hy
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hy
    have hsT := Finset.mem_of_mem_erase (hUs hs)
    have hsv := Finset.ne_of_mem_erase (hUs hs)
    obtain ⟨u, hu, huv, hyu⟩ : ∃ u ∈ H, u ≠ v ∧ G.Adj (rep G c f H s) u := by
      rcases s with a | x
      · have ha : a ∈ Mset G c f H := by simpa [Ty] using hsT
        obtain ⟨u, hu, hau, huv⟩ := two_nbrs (mem_Mset.mp ha).2 v
        exact ⟨u, hu, huv, hau⟩
      · have hx : x ∈ X1 G c f H := by simpa [Ty] using hsT
        exact ⟨x, hX1H hx, fun h => hsv (h ▸ rfl), adj_single _ _ (rep_inr hx).2⟩
    obtain ⟨X, hX, hX3⟩ := hend u hu huv ⟨w, w', hw.1, hw'.1, hww, hw.2, hw'.2⟩
    exact ph3_of hC hX hX3 hyu ht
  · -- (II) the endpoint is a leaf of `H`, with neighbour `z`
    have hNv : H.filter (G.Adj v) = {z} := by
      have h1 : (H.filter (G.Adj v)).card = 1 := by
        have : 0 < (H.filter (G.Adj v)).card :=
          Finset.card_pos.mpr ⟨z, Finset.mem_filter.mpr ⟨hz, hvz⟩⟩
        omega
      obtain ⟨z', hz'⟩ := Finset.card_eq_one.mp h1
      have : z ∈ H.filter (G.Adj v) := Finset.mem_filter.mpr ⟨hz, hvz⟩
      rw [hz'] at this ⊢; simp at this; rw [this]
    have hzv : z ≠ v := (G.ne_of_adj hvz).symm
    set L := (H.erase v).erase z with hLdef
    have hLH : L ⊆ H := (Finset.erase_subset _ _).trans (Finset.erase_subset _ _)
    have hLc : L.card + 2 = H.card := by
      rw [hLdef, Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hzv, hz⟩),
        Finset.card_erase_of_mem hv]
      omega
    have memL : ∀ u, u ∈ L ↔ u ∈ H ∧ u ≠ v ∧ u ≠ z := by
      intro u; rw [hLdef]; simp only [Finset.mem_erase]; tauto
    have Lnadj : ∀ u ∈ L, ¬ G.Adj u v := by
      intro u hu h
      have := mem_single hNv ((memL u).mp hu).1 h.symm
      exact ((memL u).mp hu).2.2 this
    have Lpath : ∀ u ∈ L, ∃ X, HP G H u v X ∧ 3 ≤ X.length := by
      intro u hu
      obtain ⟨X, hX⟩ := hC.conn u ((memL u).mp hu).1 v hv
      exact ⟨X, hX, hX.three_le (Lnadj u hu) ((memL u).mp hu).2.1⟩
    set ML := (Mset G c f H).filter (fun a => ∃ u ∈ L, G.Adj a u) with hML
    set XL := (X1 G c f H).filter (· ∈ L) with hXL
    have hTyL : ML.disjSum XL ⊆ Ty G c f H := by
      intro s hs
      rcases s with a | x
      · simp only [Finset.inl_mem_disjSum, hML, Finset.mem_filter] at hs
        simp [Ty, hs.1]
      · simp only [Finset.inr_mem_disjSum, hXL, Finset.mem_filter] at hs
        simp [Ty, hs.1]
    by_cases hA : 3 ≤ (ML.disjSum XL).card
    · -- (a) three types touch `L`
      obtain ⟨U, hUs, hU3⟩ := Finset.exists_subset_card_eq hA
      refine run U (hUs.trans hTyL) hU3 v hv ?_
      intro t ht _ y hy
      obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hy
      obtain ⟨u, hu, hyu⟩ : ∃ u ∈ L, G.Adj (rep G c f H s) u := by
        have := hUs hs
        rcases s with a | x
        · simp only [Finset.inl_mem_disjSum, hML, Finset.mem_filter] at this
          exact this.2
        · simp only [Finset.inr_mem_disjSum, hXL, Finset.mem_filter] at this
          exact ⟨x, this.2, adj_single _ _ (rep_inr this.1).2⟩
      obtain ⟨X, hX, hX3⟩ := Lpath u hu
      exact ph3_of hC hX hX3 hyu ht
    push_neg at hA
    have hTyLc : (ML.disjSum XL).card = ML.card + XL.card := Finset.card_disjSum _ _
    by_cases hB : ∃ y ∈ L, y ∉ X1 G c f H
    · -- (b) a vertex of `L` without private attachments
      obtain ⟨y, hyL, hy1⟩ := hB
      have hyH := hLH hyL
      have hW : ML.disjSum ∅ ⊆ Ty G c f H := by
        intro s hs; apply hTyL
        rcases s with a | x
        · simpa using hs
        · simp at hs
      obtain ⟨U, hWU, hUT, hU3⟩ := Finset.exists_subsuperset_card_eq (n := 3) hW
        (by rw [Finset.card_disjSum, Finset.card_empty]; omega) (by omega)
      refine run U hUT hU3 y hyH ?_
      intro t ht hS
      exfalso
      have hM := nonholder y hyH hy1 t ht
      have : Sum.inl (f t) ∈ U := hWU (by
        simp only [Finset.inl_mem_disjSum, hML, Finset.mem_filter]
        exact ⟨hM, y, hyL, ht.symm⟩)
      exact hS (inS _ _ this)
    · -- (c) every vertex of `L` holds a private attachment
      push_neg at hB
      have hXLeq : XL = L := by
        ext u; simp only [hXL, Finset.mem_filter]
        exact ⟨fun h => h.2, fun h => ⟨hB u h, h⟩⟩
      have hcount : ML.card + XL.card ≤ 2 := by omega
      rw [hXLeq] at hcount
      have hLpos : 1 ≤ L.card := by omega
      -- attachments of `L` that are not multi are private
      have Lsingle : ∀ u ∈ L, ∀ a ∈ NC G c f u, a ∉ Mset G c f H →
          H.filter (G.Adj a) = {u} := by
        intro u hu a ha haM
        have hua : G.Adj u a := by simp only [NC, Finset.mem_filter, mem_neighborFinset] at ha; exact ha.1
        rcases Aset_dich (NC_sub hD (hLH hu) ha) with h | ⟨x, -, hx⟩
        · exact absurd h haM
        · rw [hx, mem_single hx (hLH hu) hua.symm]
      have NCadj : ∀ x a, a ∈ NC G c f x → G.Adj a x := by
        intro x a ha; simp only [NC, Finset.mem_filter, mem_neighborFinset] at ha; exact ha.1.symm
      have Ltouch : ∀ u ∈ L, ∀ a ∈ NC G c f u, a ∈ Mset G c f H → a ∈ ML := by
        intro u hu a ha haM
        simp only [hML, Finset.mem_filter]; exact ⟨haM, u, hu, NCadj u a ha⟩
      rcases Nat.lt_or_ge L.card 2 with hL1 | hL2
      · -- |L| = 1
        obtain ⟨y, hLy⟩ := Finset.card_eq_one.mp (by omega : L.card = 1)
        have hyL : y ∈ L := by rw [hLy]; simp
        obtain ⟨hyH, hyv, hyz⟩ := (memL y).mp hyL
        have hH3 : H.card = 3 := by omega
        have hMLc : ML.card ≤ 1 := by omega
        -- degrees inside `H`
        have hNy : (H.filter (G.Adj y)).card ≤ 1 := by
          have : H.filter (G.Adj y) ⊆ (H.erase y).erase v := by
            intro u hu; simp only [Finset.mem_filter] at hu
            refine Finset.mem_erase.mpr ⟨fun h => Lnadj y hyL (h ▸ hu.2), ?_⟩
            exact Finset.mem_erase.mpr ⟨(G.ne_of_adj hu.2).symm, hu.1⟩
          have := Finset.card_le_card this
          rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hyv.symm, hv⟩),
            Finset.card_erase_of_mem hyH] at this
          omega
        have dy := hdeg y hyH
        have dv := hdeg v hv
        have dz := hdeg z hz
        have nz := hNHle z hz
        rw [hNv] at dv; simp at dv
        set Ay := (NC G c f y).filter (· ∉ Mset G c f H) with hAy
        have hAyc : (NC G c f y).card ≤ Ay.card + ML.card := by
          rw [← Finset.card_filter_add_card_filter_not (s := NC G c f y) (· ∈ Mset G c f H)]
          have : (NC G c f y).filter (· ∈ Mset G c f H) ⊆ ML :=
            fun a ha => Ltouch y hyL a (Finset.mem_filter.mp ha).1 (Finset.mem_filter.mp ha).2
          have := Finset.card_le_card this
          have e : ((NC G c f y).filter (fun a => ¬ a ∈ Mset G c f H)).card = Ay.card := by
            simp [hAy]
          omega
        have hAyA : Ay ⊆ Aset G c f H :=
          fun a ha => NC_sub hD hyH (Finset.mem_filter.mp ha).1
        set B := Aset G c f H \ Ay with hBdef
        have hBc : B.card + Ay.card = (Aset G c f H).card := by
          rw [hBdef, Finset.card_sdiff_of_subset hAyA]
          have := Finset.card_le_card hAyA; omega
        have notAy : ∀ x ∈ H, x ≠ y → ∀ a ∈ NC G c f x, a ∈ B := by
          intro x hx hxy a ha
          refine Finset.mem_sdiff.mpr ⟨NC_sub hD hx ha, fun haY => ?_⟩
          obtain ⟨ha1, ha2⟩ := Finset.mem_filter.mp haY
          have := Lsingle y hyL a ha1 ha2
          exact hxy (mem_single this hx (NCadj x a ha))
        have hMB : Mset G c f H ⊆ B := by
          intro a ha
          exact Finset.mem_sdiff.mpr ⟨(mem_Mset.mp ha).1, fun h => (Finset.mem_filter.mp h).2 ha⟩
        have hvz' : NC G c f v ∩ NC G c f z ⊆ Mset G c f H := by
          intro a ha
          obtain ⟨h1, h2⟩ := Finset.mem_inter.mp ha
          refine mem_Mset.mpr ⟨NC_sub hD hv h1, ?_⟩
          apply Finset.one_lt_card.mpr
          exact ⟨v, Finset.mem_filter.mpr ⟨hv, NCadj v a h1⟩, z,
            Finset.mem_filter.mpr ⟨hz, NCadj z a h2⟩, hzv.symm⟩
        have hvzB : NC G c f v ∪ NC G c f z ⊆ B := by
          intro a ha
          rcases Finset.mem_union.mp ha with h | h
          · exact notAy v hv hyv.symm a h
          · exact notAy z hz hyz.symm a h
        have hu := Finset.card_union_add_card_inter (NC G c f v) (NC G c f z)
        have c1 := Finset.card_le_card hvzB
        have c2 := Finset.card_le_card hvz'
        have c3 := Finset.card_le_card hMB
        omega
      · -- |L| = 2
        have hML0 : ML.card = 0 := by omega
        have hL2' : L.card = 2 := by omega
        obtain ⟨y1, y2, hy12, hLy⟩ := Finset.card_eq_two.mp hL2'
        have hy1L : y1 ∈ L := by rw [hLy]; simp
        have hy2L : y2 ∈ L := by rw [hLy]; simp
        have hH4 : H.card = 4 := by omega
        have noM : ∀ u ∈ L, ∀ a ∈ NC G c f u, a ∉ Mset G c f H := by
          intro u hu a ha haM
          have := Ltouch u hu a ha haM
          rw [Finset.card_eq_zero] at hML0; rw [hML0] at this; simp at this
        have priv : ∀ u ∈ L, ∀ a ∈ NC G c f u, ∀ x ∈ H, G.Adj a x → x = u := by
          intro u hu a ha x hx hax
          exact mem_single (Lsingle u hu a ha (noM u hu a ha)) hx hax
        have hNyi : ∀ u ∈ L, (H.filter (G.Adj u)).card ≤ 2 := by
          intro u hu
          obtain ⟨huH, huv, -⟩ := (memL u).mp hu
          have : H.filter (G.Adj u) ⊆ (H.erase u).erase v := by
            intro w hw; simp only [Finset.mem_filter] at hw
            refine Finset.mem_erase.mpr ⟨fun h => Lnadj u hu (h ▸ hw.2), ?_⟩
            exact Finset.mem_erase.mpr ⟨(G.ne_of_adj hw.2).symm, hw.1⟩
          have := Finset.card_le_card this
          rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨huv.symm, hv⟩),
            Finset.card_erase_of_mem huH] at this
          omega
        have d1 := hdeg y1 (hLH hy1L)
        have d2 := hdeg y2 (hLH hy2L)
        have dv := hdeg v hv
        have n1 := hNyi y1 hy1L
        have n2 := hNyi y2 hy2L
        rw [hNv] at dv; simp at dv
        have e1 : Disjoint (NC G c f y1) (NC G c f y2) := by
          rw [Finset.disjoint_left]; intro a h1 h2
          exact hy12 ((priv y1 hy1L a h1 y2 (hLH hy2L) (NCadj y2 a h2)).symm)
        have e2 : Disjoint (NC G c f y1 ∪ NC G c f y2) (NC G c f v) := by
          rw [Finset.disjoint_left]; intro a h1 h2
          rcases Finset.mem_union.mp h1 with h | h
          · exact ((memL y1).mp hy1L).2.1 (priv y1 hy1L a h v hv (NCadj v a h2)).symm
          · exact ((memL y2).mp hy2L).2.1 (priv y2 hy2L a h v hv (NCadj v a h2)).symm
        have hsub : NC G c f y1 ∪ NC G c f y2 ∪ NC G c f v ⊆ Aset G c f H := by
          intro a ha
          simp only [Finset.mem_union] at ha
          rcases ha with (h | h) | h
          · exact NC_sub hD (hLH hy1L) h
          · exact NC_sub hD (hLH hy2L) h
          · exact NC_sub hD hv h
        have := Finset.card_le_card hsub
        rw [Finset.card_union_of_disjoint e2, Finset.card_union_of_disjoint e1] at this
        omega

end core



/-! ## From the statement to the combinatorial core -/

section glue

variable [DecidableRel G.Adj]

/-- The periodic enumeration of a closed walk. -/
def cyc {a : V} (C : G.Walk a a) : ℕ → V := fun t => C.getVert (t % C.length)

lemma cy_of {a : V} (C : G.Walk a a) (hC : C.IsCycle) (hlong : C.length = G.circumference) :
    Cy G C.length (cyc C) := by
  have hc := hC.three_le_length
  refine ⟨hc, fun t => by simp [cyc], fun t => ?_, fun i j hi hj h => ?_, fun l hnd hcl => ?_⟩
  · simp only [cyc]
    have hlt : t % C.length < C.length := Nat.mod_lt _ (by omega)
    have hm : (t + 1) % C.length = (t % C.length + 1) % C.length := by
      rw [Nat.add_mod, Nat.mod_eq_of_lt (show 1 < C.length by omega)]
    rw [hm]
    by_cases h : t % C.length + 1 < C.length
    · rw [Nat.mod_eq_of_lt h]; exact C.adj_getVert_succ hlt
    · have h' : t % C.length + 1 = C.length := by omega
      rw [h', Nat.mod_self, Walk.getVert_zero]
      have := C.adj_getVert_succ hlt
      rwa [h', Walk.getVert_length] at this
  · simp only [cyc, Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] at h
    exact hC.getVert_injOn' (by simp; omega) (by simp; omega) h
  · by_cases h3 : l.length < 3
    · omega
    · obtain ⟨b, w, hw, hwl⟩ := cycle_of_CL l hnd hcl (by omega)
      rw [← hwl, hlong]; exact le_circumference w hw

lemma mem_support_cyc {a : V} (C : G.Walk a a) (hC : C.IsCycle) (y : V) :
    y ∈ C.support ↔ ∃ t, cyc C t = y := by
  have hc := hC.three_le_length
  constructor
  · intro hy
    obtain ⟨n, hn, hnl⟩ := Walk.mem_support_iff_exists_getVert.mp hy
    rcases Nat.lt_or_ge n C.length with h | h
    · exact ⟨n, by simp [cyc, Nat.mod_eq_of_lt h, hn]⟩
    · refine ⟨0, ?_⟩
      have : n = C.length := by omega
      subst this
      simp [cyc, ← hn, Walk.getVert_length]
  · rintro ⟨t, rfl⟩; exact Walk.getVert_mem_support _ _

lemma reach_mem {s : Set V} {x y : s} (w : (G.induce s).Walk x y) {z : s} (hz : z ∈ w.support) :
    (G.induce s).Reachable x z := ⟨w.takeUntil z hz⟩

open Arxiv.«2606.03696» in
theorem main3 (hG : IsKConnected G 3)
    (hd : ((Fintype.card V : ℝ) + 6) / 4 ≤ G.minDegree)
    {a : V} (C : G.Walk a a) (hC : C.IsCycle) (hlong : C.length = G.circumference)
    (u v : offWalk C) (P : (G.induce (offWalk C)).Walk u v)
    (hP : P.IsPath) : P.support.length + 1 ≤ 3 := by
  by_contra hlt
  push_neg at hlt
  have hD := cy_of C hC hlong
  have hsupp := mem_support_cyc C hC
  have mem_s : ∀ y, y ∈ offWalk C ↔ y ∉ C.support := fun y => Iff.rfl
  classical
  obtain ⟨H, hH⟩ : ∃ H : Finset V, H = Finset.univ.filter
      (fun y => ∃ hy : y ∈ offWalk C, (G.induce (offWalk C)).Reachable u ⟨y, hy⟩) := ⟨_, rfl⟩
  have memH : ∀ y, y ∈ H ↔ ∃ hy : y ∈ offWalk C, (G.induce (offWalk C)).Reachable u ⟨y, hy⟩ := by
    intro y; simp [hH]
  have hComp : Comp G (cyc C) H := by
    refine ⟨?_, ?_, ?_⟩
    · intro x hx t ht
      obtain ⟨hxs, -⟩ := (memH x).mp hx
      exact (mem_s x).mp hxs ((hsupp x).mpr ⟨t, ht⟩)
    · intro x hx y hxy
      obtain ⟨hxs, hr⟩ := (memH x).mp hx
      by_cases hy : y ∈ C.support
      · exact Or.inr ((hsupp y).mp hy)
      · left
        have hys : y ∈ offWalk C := (mem_s y).mpr hy
        exact (memH y).mpr ⟨hys, hr.trans (Adj.reachable (G := G.induce (offWalk C))
          (u := ⟨x, hxs⟩) (v := ⟨y, hys⟩) hxy)⟩
    · intro x hx y hy
      obtain ⟨hxs, hrx⟩ := (memH x).mp hx
      obtain ⟨hys, hry⟩ := (memH y).mp hy
      obtain ⟨w⟩ := hrx.symm.trans hry
      obtain ⟨p, hp⟩ := w.toPath
      refine ⟨p.support.map Subtype.val, ?_, ?_, ?_, ?_, ?_⟩
      · exact hp.support_nodup.map Subtype.val_injective
      · exact (List.isChain_map Subtype.val).mpr p.isChain_adj_support
      · intro z hz
        obtain ⟨z', hz', rfl⟩ := List.mem_map.mp hz
        exact (memH z').mpr ⟨z'.2, hrx.trans (reach_mem p hz')⟩
      · rw [Walk.support_eq_cons, List.map_cons, List.head?_cons]
      · rw [List.getLast?_map, List.getLast?_eq_getLast_of_ne_nil (Walk.support_ne_nil _),
          Walk.getLast_support]; rfl
  have h3 : 3 ≤ H.card := by
    have hnd := hP.support_nodup.map Subtype.val_injective
    have hsub : (P.support.map Subtype.val).toFinset ⊆ H := by
      intro z hz
      obtain ⟨z', hz', rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hz)
      exact (memH z').mpr ⟨z'.2, reach_mem P hz'⟩
    have := Finset.card_le_card hsub
    rw [List.toFinset_card_of_nodup hnd, List.length_map] at this
    omega
  have hKs : ∀ S : Finset V, S.card ≤ 2 → ∀ X : Finset V, (∀ a ∈ X, a ∉ S) →
      (∀ a ∈ X, ∀ b, G.Adj a b → b ∉ S → b ∈ X) → X.Nonempty → ∀ y, y ∉ S → y ∉ X → False := by
    intro S hS X hXS hXcl hXne y hyS hyX
    obtain ⟨x, hx⟩ := hXne
    have hconn := hG.2 S (by omega)
    obtain ⟨w⟩ := hconn.preconnected ⟨x, hXS x hx⟩ ⟨y, hyS⟩
    have key : ∀ (p q : ((S : Set V)ᶜ : Set V)) (w : (G.induce ((S : Set V)ᶜ)).Walk p q),
        p.1 ∈ X → q.1 ∈ X := by
      intro p q w
      induction w with
      | nil => exact id
      | @cons p0 p1 q h w ih =>
        intro hp
        exact ih (hXcl _ hp _ h (fun h' => p1.2 h'))
    exact hyX (key _ _ w hx)
  have hn : Fintype.card V + 6 ≤ 4 * G.minDegree := by
    have := (div_le_iff₀ (by norm_num : (0 : ℝ) < 4)).mp hd
    have h' : ((Fintype.card V + 6 : ℕ) : ℝ) ≤ ((4 * G.minDegree : ℕ) : ℝ) := by
      push_cast; linarith
    exact_mod_cast h'
  exact core hD hComp (fun x => G.minDegree_le_degree x) hn h3 hKs

end glue




end OMA.Bondy3

theorem OMA.solution : type_of% @Arxiv.«2606.03696».bondy_conjecture.variants.three := by
  intro V _ _ G _ hG hd a C hC hlong u v P hP
  exact OMA.Bondy3.main3 hG hd C hC hlong u v P hP
