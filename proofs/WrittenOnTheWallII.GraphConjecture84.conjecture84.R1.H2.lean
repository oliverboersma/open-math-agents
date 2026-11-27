import OMAReductions.R_WrittenOnTheWallII_GraphConjecture84_conjecture84_R1

-- Step WrittenOnTheWallII.GraphConjecture84.conjecture84.R1.H2: hypothesis H2 of reduction WrittenOnTheWallII.GraphConjecture84.conjecture84.R1
-- Credit: @ivillar
-- H2 := ∀ (α : Type) [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj], G.Connected → 0 < G.minDegree → 2 ≤ G.minDegree → 2 * (G.radius.toNat : ℝ) / (G.minDegree : ℝ) ≤ (largestInducedTreeSize G : ℝ) 
-- Reuses isAcyclic_of_rank from proofs/WrittenOnTheWallII.GraphConjecture4.conjecture4.lean (credit @jonas-klesen).

namespace OMA.W84H2

open SimpleGraph

/-- A graph is acyclic if every vertex `x` has at most one neighbour of rank at most the rank
of `x`, namely `p x`. (Reused from the merged proof of WrittenOnTheWallII.GraphConjecture4,
credit @jonas-klesen.) -/
lemma isAcyclic_of_rank {V : Type*} (H : SimpleGraph V) (r : V → ℕ) (p : V → V)
    (h : ∀ x y, H.Adj x y → r y ≤ r x → y = p x) : H.IsAcyclic := by
  classical
  intro a c hc
  obtain ⟨x, hx, hmax⟩ := Finset.exists_max_image c.support.toFinset r
    ⟨a, List.mem_toFinset.2 c.start_mem_support⟩
  rw [List.mem_toFinset] at hx
  have hc' : (c.rotate x hx).IsCycle := hc.rotate hx
  have hsup : ∀ y ∈ (c.rotate x hx).support, r y ≤ r x := by
    intro y hy
    apply hmax
    rw [List.mem_toFinset]
    exact (c.mem_support_rotate_iff x hx).1 hy
  have h1 := h x _ ((c.rotate x hx).adj_snd hc'.not_nil)
    (hsup _ ((c.rotate x hx).getVert_mem_support 1))
  have h2 := h x _ ((c.rotate x hx).adj_penultimate hc'.not_nil).symm
    (hsup _ ((c.rotate x hx).getVert_mem_support _))
  exact hc'.snd_ne_penultimate (h1.trans h2.symm)

/-- In a shortest walk, the `i`-th vertex is at distance `i` from the start. -/
lemma geodesic_dist {α : Type} {G : SimpleGraph α} (hG : G.Connected) {u v : α}
    (q : G.Walk u v) (hq : q.length = G.dist u v) {i : ℕ} (hi : i ≤ q.length) :
    G.dist u (q.getVert i) = i := by
  have h1 : G.dist u (q.getVert i) ≤ i := by
    have := dist_le (q.take i)
    rw [Walk.take_length] at this
    exact this.trans inf_le_left
  have h2 : G.dist (q.getVert i) v ≤ q.length - i := by
    have := dist_le (q.drop i)
    rwa [Walk.drop_length] at this
  have t1 := hG.dist_triangle (u := u) (v := q.getVert i) (w := v)
  omega

/-- In a shortest walk, two adjacent vertices at positions `i < j` are consecutive. -/
lemma geodesic_adj {α : Type} {G : SimpleGraph α} (hG : G.Connected) {u v : α}
    (q : G.Walk u v) (hq : q.length = G.dist u v) {i j : ℕ} (hij : i < j)
    (hj : j ≤ q.length) (hadj : G.Adj (q.getVert i) (q.getVert j)) : j = i + 1 := by
  have h1 : G.dist u (q.getVert i) ≤ i := by
    have := dist_le (q.take i)
    rw [Walk.take_length] at this
    exact this.trans inf_le_left
  have h2 : G.dist (q.getVert j) v ≤ q.length - j := by
    have := dist_le (q.drop j)
    rwa [Walk.drop_length] at this
  have h3 : G.dist (q.getVert i) (q.getVert j) = 1 := dist_eq_one_iff_adj.mpr hadj
  have t1 := hG.dist_triangle (u := u) (v := q.getVert i) (w := v)
  have t2 := hG.dist_triangle (u := q.getVert i) (v := q.getVert j) (w := v)
  omega

/-- A connected finite graph has an induced tree on at least `radius + 1` vertices: the vertex
set of a shortest walk from any vertex to a vertex realizing its eccentricity induces a path. -/
lemma radius_succ_le_tree {α : Type} [Fintype α] [DecidableEq α] [Nontrivial α]
    (G : SimpleGraph α) (hG : G.Connected) :
    G.radius.toNat + 1 ≤ largestInducedTreeSize G := by
  classical
  obtain ⟨u⟩ : Nonempty α := inferInstance
  obtain ⟨v, hv⟩ := G.exists_edist_eq_eccent_of_finite u
  obtain ⟨p, hp⟩ := hG.exists_walk_length_eq_dist u v
  let q := p.bypass
  have hqpath : q.IsPath := p.bypass_isPath
  have hqlen : q.length = G.dist u v :=
    le_antisymm (hp ▸ p.length_bypass_le_length) (dist_le q)
  have hrad : G.radius.toNat ≤ G.dist u v := by
    have hne : G.eccent u ≠ ⊤ := by
      rw [← hv]; exact edist_ne_top_iff_reachable.mpr (hG.preconnected u v)
    have := ENat.toNat_le_toNat (G.radius_le_eccent (u := u)) hne
    rw [← hv] at this
    exact this
  let S : Set α := {x | x ∈ q.support}
  have hconn : (G.induce S).Connected := q.connected_induce_support
  have hmem : ∀ x : S, ∃ i, i ≤ q.length ∧ q.getVert i = x.val := by
    intro x
    obtain ⟨n, hn, hnl⟩ := Walk.mem_support_iff_exists_getVert.mp x.property
    exact ⟨n, hnl, hn⟩
  let par : S → S := fun x => ⟨q.getVert (G.dist u x.val - 1), q.getVert_mem_support _⟩
  have hacyc : (G.induce S).IsAcyclic := by
    apply isAcyclic_of_rank (G.induce S) (fun x => G.dist u x.val) par
    intro x y hxy hr
    obtain ⟨i, hi, hix⟩ := hmem x
    obtain ⟨j, hj, hjy⟩ := hmem y
    have hxy' : G.Adj x.val y.val := hxy
    have hadj : G.Adj (q.getVert i) (q.getVert j) := by rw [hix, hjy]; exact hxy'
    have di : G.dist u x.val = i := by rw [← hix]; exact geodesic_dist hG q hqlen hi
    have dj : G.dist u y.val = j := by rw [← hjy]; exact geodesic_dist hG q hqlen hj
    have hr' : G.dist u y.val ≤ G.dist u x.val := hr
    rw [di, dj] at hr'
    have hne : j ≠ i := by
      rintro rfl; exact hadj.ne rfl
    have hji : j < i := lt_of_le_of_ne hr' hne
    have hij := geodesic_adj hG q hqlen hji hi hadj.symm
    apply Subtype.ext
    show y.val = q.getVert (G.dist u x.val - 1)
    rw [di, ← hjy]
    congr 1
    omega
  let s : Finset α := q.support.toFinset
  have hs : (s : Set α) = S := by ext x; simp [s, S]
  have htree : (G.induce (s : Set α)).IsTree := by rw [hs]; exact ⟨hconn, hacyc⟩
  have hcard : s.card = q.length + 1 := by
    rw [List.toFinset_card_of_nodup hqpath.support_nodup, Walk.length_support]
  have := card_le_largestInducedTreeSize htree
  omega

end OMA.W84H2

theorem OMA.solution : OMA.R_WrittenOnTheWallII_GraphConjecture84_conjecture84_R1.H2 := by
  unfold OMA.R_WrittenOnTheWallII_GraphConjecture84_conjecture84_R1.H2
  intro α _ _ _ G _ hG _ hδ2
  have hT := OMA.W84H2.radius_succ_le_tree G hG
  have hδR : (2 : ℝ) ≤ (G.minDegree : ℝ) := by exact_mod_cast hδ2
  have hTR : (G.radius.toNat : ℝ) + 1 ≤ (SimpleGraph.largestInducedTreeSize G : ℝ) := by
    exact_mod_cast hT
  have hL0 : (0 : ℝ) ≤ (SimpleGraph.largestInducedTreeSize G : ℝ) := Nat.cast_nonneg _
  rw [div_le_iff₀ (by linarith)]
  nlinarith [mul_le_mul_of_nonneg_left hδR hL0]
