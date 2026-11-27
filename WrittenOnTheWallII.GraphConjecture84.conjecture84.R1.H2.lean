import OMAReductions.R_WrittenOnTheWallII_GraphConjecture84_conjecture84_R1

-- Step WrittenOnTheWallII.GraphConjecture84.conjecture84.R1.H2: hypothesis H2 of reduction WrittenOnTheWallII.GraphConjecture84.conjecture84.R1
-- Credit: @oliverboersma
-- Minimum degree at least two. Take any vertex u and a vertex v at distance eccent u from it.
-- A shortest u-v walk induces a tree on dist u v + 1 vertices, and dist u v = eccent u is at
-- least the radius, so the radius is below the largest induced tree. Since the minimum degree
-- is at least two, 2 rad / minDegree is at most rad.

namespace OMAStepWOWII84H2

open SimpleGraph

theorem radius_toNat_lt_largestInducedTreeSize {α : Type} [Fintype α] [DecidableEq α]
    [Nontrivial α] (G : SimpleGraph α) (hc : G.Connected) :
    G.radius.toNat < largestInducedTreeSize G := by
  obtain ⟨u⟩ := (inferInstance : Nonempty α)
  obtain ⟨v, hv⟩ := G.exists_edist_eq_eccent_of_finite u
  obtain ⟨p, hp⟩ := hc.exists_walk_length_eq_dist u v
  have htree := Walk.induce_support_isTree_of_length_eq_dist p hp
  have hcard : p.support.toFinset.card = p.length + 1 := by
    rw [List.toFinset_card_of_nodup (p.isPath_of_length_eq_dist hp).support_nodup,
      Walk.length_support]
  have hle := card_le_largestInducedTreeSize htree
  have hrad : G.radius ≤ (G.dist u v : ℕ∞) := by
    rw [(hc u v).coe_dist_eq_edist, hv]
    exact radius_le_eccent
  have hnat : G.radius.toNat ≤ G.dist u v := by
    have h := ENat.toNat_le_toNat hrad (ENat.natCast_ne_top _)
    simpa using h
  omega

end OMAStepWOWII84H2

theorem OMA.solution : OMA.R_WrittenOnTheWallII_GraphConjecture84_conjecture84_R1.H2 := by
  intro α _ _ _ G _ hc _ hδ2
  have hlt := OMAStepWOWII84H2.radius_toNat_lt_largestInducedTreeSize G hc
  have hδ : (2 : ℝ) ≤ (G.minDegree : ℝ) := by exact_mod_cast hδ2
  have hpos : (0 : ℝ) < (G.minDegree : ℝ) := by linarith
  have hr : (G.radius.toNat : ℝ) ≤ (G.largestInducedTreeSize : ℝ) := by exact_mod_cast hlt.le
  have hr0 : (0 : ℝ) ≤ (G.radius.toNat : ℝ) := Nat.cast_nonneg _
  rw [div_le_iff₀ hpos]
  nlinarith
