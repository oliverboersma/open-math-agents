import OMAReductions.R_WrittenOnTheWallII_GraphConjecture133_conjecture133_R1

-- Step WrittenOnTheWallII.GraphConjecture133.conjecture133.R1.H2: hypothesis H2 of reduction WrittenOnTheWallII.GraphConjecture133.conjecture133.R1
-- Credit: @ivillar
-- H2 := ∀ {α : Type} [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α), G.Connected →     (∃ a b c d : α, a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧       G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a) →     (G.radius.toNat : ℝ) + 1 ≤ (SimpleGraph.path G : ℝ)

namespace OMA.W133H2

open SimpleGraph

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

/-- A connected finite graph has an induced path on at least `radius + 1` vertices:
a shortest walk from any vertex to a vertex realizing its eccentricity. -/
lemma radius_succ_le_path {α : Type} [Fintype α] [DecidableEq α] [Nontrivial α]
    (G : SimpleGraph α) (hG : G.Connected) : G.radius.toNat + 1 ≤ SimpleGraph.path G := by
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
  have hind : G.isInducedPath q.support := by
    refine ⟨hqpath.support_nodup, ?_⟩
    intro i j
    have hi : i.val ≤ q.length := by
      have := i.isLt; have := q.length_support; omega
    have hj : j.val ≤ q.length := by
      have := j.isLt; have := q.length_support; omega
    rw [List.get_eq_getElem, List.get_eq_getElem, Walk.support_getElem_eq_getVert,
      Walk.support_getElem_eq_getVert]
    constructor
    · intro hadj
      rcases lt_trichotomy i.val j.val with h | h | h
      · left; exact (geodesic_adj hG q hqlen h hj hadj).symm
      · exfalso; rw [h] at hadj; exact hadj.ne rfl
      · right; exact (geodesic_adj hG q hqlen h hi hadj.symm).symm
    · rintro (h | h)
      · rw [← h]; exact q.adj_getVert_succ (by omega)
      · rw [← h]; exact (q.adj_getVert_succ (by omega)).symm
  have hlen := length_le_path_of_isInducedPath G q.support hind
  rw [Walk.length_support] at hlen
  omega

end OMA.W133H2

theorem OMA.solution : OMA.R_WrittenOnTheWallII_GraphConjecture133_conjecture133_R1.H2 := by
  unfold OMA.R_WrittenOnTheWallII_GraphConjecture133_conjecture133_R1.H2
  intro α _ _ _ G hG _
  have := OMA.W133H2.radius_succ_le_path G hG
  exact_mod_cast this
