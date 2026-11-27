import OMAReductions.R_WrittenOnTheWallII_GraphConjecture133_conjecture133_R1

/-!
Split the C4-free case of Written on the Wall II, Conjecture 133, by the gap `path - radius`.

Proved here, with no hypothesis:
* `path G ≥ radius + 1`: a geodesic is an induced path.
* In a connected C4-free graph, if a vertex `v` has two non-adjacent neighbours, then
  `path G ≥ eccent v + 2 ≥ radius + 2`. Take a geodesic `v = p0, p1, …, pe` to a vertex at
  distance `e = eccent v`. Two independent neighbours of `v` give a neighbour `c` of `v` with
  `c ≠ p1` and `c` not adjacent to `p1`, since two neighbours of `v` adjacent to `p1` would
  close a 4-cycle through `v` and `p1`. Then `c, p0, …, pe` is an induced path: `c ~ p2` would
  close the 4-cycle `v c p2 p1`, and `c ~ pj` for `j ≥ 3` contradicts `dist v pj = j`.
  So if `path G ≤ radius + 1`, every neighbourhood is a clique and `l G ≤ 1`.
* `l(v) ≤ deg v`, so `l G ≤ 2|E|/n`. Hence the bound holds whenever `2|E| ≤ (path - radius) n`.
* The average is at most the maximum, so the bound holds whenever every `l(v) ≤ path - radius`.

What is left:
* H1, the gap-2 regime: `path = radius + 2`, more edges than vertices (no trees, no unicyclic
  graphs) and a vertex `v` with `l(v) ≥ 3`. Claim: `l G ≤ 2`.
* H2, the gap ≥ 3 regime, for graphs whose average degree exceeds `path - radius` and that have
  a vertex `v` with `l(v) > path - radius`. This removes, for instance, every C4-free graph whose
  neighbourhood independence numbers are all at most 3, which includes the Petersen graph,
  where the gap-3 bound is attained.

Evidence (exhaustive search over connected C4-free graphs with at most 14 vertices, not part of
the proof): in the gap-2 regime the sum of `l(v)` is at most `2n`, with equality only for C5 and
C6, and the radius is at most 2 except for C6. No claim is made that H1 or H2 is proved.
-/

namespace OMA.R_WrittenOnTheWallII_GraphConjecture133_conjecture133_R1_H1_R1

open SimpleGraph

/-- The gap-2 regime: a connected C4-free graph with `path = radius + 2` and a vertex whose
neighbourhood has independence number at least 3 has average neighbourhood independence
number at most 2. -/
def H1 : Prop :=
  ∀ {α : Type} [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α), G.Connected →
    ¬ (∃ a b c d : α, a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a) →
    SimpleGraph.path G = G.radius.toNat + 2 →
    (∃ v : α, 3 ≤ indepNeighborsCard G v) →
    Fintype.card α < Nat.card G.edgeSet →
    SimpleGraph.l G ≤ 2

/-- The gap ≥ 3 regime, for graphs with a vertex `v` whose neighbourhood independence number
exceeds `path - radius`. -/
def H2 : Prop :=
  ∀ {α : Type} [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α), G.Connected →
    ¬ (∃ a b c d : α, a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a) →
    G.radius.toNat + 3 ≤ SimpleGraph.path G →
    (∃ v : α, SimpleGraph.path G < G.radius.toNat + indepNeighborsCard G v) →
    (SimpleGraph.path G - G.radius.toNat) * Fintype.card α < 2 * Nat.card G.edgeSet →
    (G.radius.toNat : ℝ) + SimpleGraph.l G ≤ (SimpleGraph.path G : ℝ)

section lemmas

variable {α : Type} [Fintype α] [DecidableEq α]

lemma le_path_of_fun (G : SimpleGraph α) (f : ℕ → α) (m : ℕ)
    (hinj : ∀ i j, i < m → j < m → f i = f j → i = j)
    (hadj : ∀ i j, i < m → j < m → (G.Adj (f i) (f j) ↔ i + 1 = j ∨ j + 1 = i)) :
    m ≤ SimpleGraph.path G := by
  have h := length_le_path_of_isInducedPath G (List.ofFn (fun i : Fin m => f i)) ?_
  · simpa using h
  refine ⟨?_, ?_⟩
  · rw [List.nodup_ofFn]
    intro i j hij
    exact Fin.ext (hinj i j i.2 j.2 hij)
  · intro i j
    have hi : (i : ℕ) < m := by simpa using i.2
    have hj : (j : ℕ) < m := by simpa using j.2
    simpa [List.get_eq_getElem, List.getElem_ofFn] using hadj i j hi hj

omit [Fintype α] [DecidableEq α] in
lemma exists_geodesic (G : SimpleGraph α) (hconn : G.Connected) (v z : α) :
    ∃ f : ℕ → α, f 0 = v ∧ (∀ i, i ≤ G.dist v z → G.dist v (f i) = i) ∧
      (∀ i, i < G.dist v z → G.Adj (f i) (f (i + 1))) := by
  obtain ⟨p, hp⟩ := hconn.exists_walk_length_eq_dist v z
  refine ⟨p.getVert, p.getVert_zero, ?_, ?_⟩
  · intro i hi
    have h1 : G.dist v (p.getVert i) ≤ i := by
      have := dist_le (p.take i)
      rw [Walk.take_length] at this
      omega
    have h2 : G.dist (p.getVert i) z ≤ G.dist v z - i := by
      have := dist_le (p.drop i)
      rw [Walk.drop_length] at this
      omega
    have h3 := hconn.dist_triangle (u := v) (v := p.getVert i) (w := z)
    omega
  · intro i hi
    exact p.adj_getVert_succ (by omega)

omit [Fintype α] [DecidableEq α] in
lemma dist_le_of_adj (G : SimpleGraph α) (hconn : G.Connected) {v x y : α} (h : G.Adj x y) :
    G.dist v y ≤ G.dist v x + 1 := by
  have := hconn.dist_triangle (u := v) (v := x) (w := y)
  rw [dist_eq_one_iff_adj.mpr h] at this
  exact this

omit [Fintype α] [DecidableEq α] in
lemma geodesic_iff (G : SimpleGraph α) (hconn : G.Connected) (v : α) (d : ℕ) (f : ℕ → α)
    (hd : ∀ i, i ≤ d → G.dist v (f i) = i) (ha : ∀ i, i < d → G.Adj (f i) (f (i + 1)))
    (i j : ℕ) (hi : i ≤ d) (hj : j ≤ d) :
    G.Adj (f i) (f j) ↔ i + 1 = j ∨ j + 1 = i := by
  constructor
  · intro h
    have h1 := dist_le_of_adj G hconn (v := v) h
    have h2 := dist_le_of_adj G hconn (v := v) h.symm
    rw [hd i hi, hd j hj] at h1 h2
    have hne : i ≠ j := by
      rintro rfl
      exact G.irrefl h
    omega
  · rintro (h | h)
    · subst h
      exact ha i (by omega)
    · subst h
      exact (ha j (by omega)).symm

lemma add_one_le_path (G : SimpleGraph α) (hconn : G.Connected) (v z : α) :
    G.dist v z + 1 ≤ SimpleGraph.path G := by
  obtain ⟨f, -, hd, ha⟩ := exists_geodesic G hconn v z
  apply le_path_of_fun G f
  · intro i j hi hj hij
    have := hd i (by omega)
    rw [hij, hd j (by omega)] at this
    exact this.symm
  · intro i j hi hj
    exact geodesic_iff G hconn v _ f hd ha i j (by omega) (by omega)

lemma add_two_le_path (G : SimpleGraph α) (hconn : G.Connected)
    (hC4 : ¬ (∃ a b c d : α, a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (v z c : α) (f : ℕ → α) (hf0 : f 0 = v)
    (hd : ∀ i, i ≤ G.dist v z → G.dist v (f i) = i)
    (ha : ∀ i, i < G.dist v z → G.Adj (f i) (f (i + 1)))
    (hd1 : 1 ≤ G.dist v z) (hvc : G.Adj v c) (hc1 : c ≠ f 1) (hcn : ¬ G.Adj c (f 1)) :
    G.dist v z + 2 ≤ SimpleGraph.path G := by
  set d := G.dist v z with hdd
  have hdc : G.dist v c = 1 := dist_eq_one_iff_adj.mpr hvc
  -- `c` is not on the geodesic
  have hcf : ∀ j, j ≤ d → c ≠ f j := by
    intro j hj hcj
    rcases Nat.lt_or_ge j 2 with h | h
    · interval_cases j
      · rw [hf0] at hcj
        exact G.ne_of_adj hvc hcj.symm
      · exact hc1 hcj
    · have := hd j hj
      rw [← hcj, hdc] at this
      omega
  -- adjacency of `c` with the geodesic
  have hcadj : ∀ j, j ≤ d → (G.Adj c (f j) ↔ j = 0) := by
    intro j hj
    constructor
    · intro h
      by_contra hj0
      have hle := dist_le_of_adj G hconn (v := v) h
      rw [hdc, hd j hj] at hle
      have hj1 : 1 ≤ j := by omega
      interval_cases j
      · exact hcn h
      · apply hC4
        refine ⟨v, c, f 2, f 1, ?_, ?_, ?_, ?_, ?_, ?_, hvc, h, (ha 1 (by omega)).symm, ?_⟩
        · exact G.ne_of_adj hvc
        · intro h'
          have := hd 2 hj
          rw [← h', SimpleGraph.dist_self] at this
          omega
        · intro h'
          have := hd 1 (by omega)
          rw [← h', SimpleGraph.dist_self] at this
          omega
        · exact hcf 2 hj
        · exact hc1
        · intro h'
          have h2 := hd 2 hj
          rw [h', hd 1 (by omega)] at h2
          omega
        · have := ha 0 (by omega)
          rw [hf0] at this
          exact this.symm
    · rintro rfl
      rw [hf0]
      exact hvc.symm
  let g : ℕ → α := fun i => match i with
    | 0 => c
    | k + 1 => f k
  have hg0 : g 0 = c := rfl
  have hgs : ∀ k, g (k + 1) = f k := fun k => rfl
  have key := le_path_of_fun G g (d + 2) ?_ ?_
  · exact key
  · intro i j hi hj hij
    rcases i with _ | i <;> rcases j with _ | j
    · rfl
    · rw [hg0, hgs] at hij
      exact absurd hij (hcf j (by omega))
    · rw [hg0, hgs] at hij
      exact absurd hij.symm (hcf i (by omega))
    · rw [hgs, hgs] at hij
      have h1 := hd i (by omega)
      rw [hij, hd j (by omega)] at h1
      omega
  · intro i j hi hj
    rcases i with _ | i <;> rcases j with _ | j
    · rw [hg0]
      simp
    · rw [hg0, hgs, hcadj j (by omega)]
      omega
    · rw [hg0, hgs, G.adj_comm, hcadj i (by omega)]
      omega
    · rw [hgs, hgs, geodesic_iff G hconn v d f hd ha i j (by omega) (by omega)]
      omega

lemma exists_escape (G : SimpleGraph α)
    (hC4 : ¬ (∃ a b c d : α, a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (v u : α) (hvu : G.Adj v u) (h2 : 2 ≤ indepNeighborsCard G v) :
    ∃ c, G.Adj v c ∧ c ≠ u ∧ ¬ G.Adj c u := by
  obtain ⟨S, hS, hI, hc⟩ :=
    OMA.R_WrittenOnTheWallII_GraphConjecture133_conjecture133_R1.exists_indepNeighbors G v
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (by omega : 1 < S.card)
  have hnab : ¬ G.Adj a b := hI ha hb hab
  by_cases hau : a = u
  · subst hau
    exact ⟨b, hS b hb, fun h => hab h.symm, fun h => hnab h.symm⟩
  by_cases hadj : G.Adj a u
  · refine ⟨b, hS b hb, ?_, ?_⟩
    · rintro rfl
      exact hnab hadj
    · intro hbu
      apply hC4
      refine ⟨v, a, u, b, G.ne_of_adj (hS a ha), G.ne_of_adj hvu, G.ne_of_adj (hS b hb),
        hau, hab, ?_, hS a ha, hadj, hbu.symm, (hS b hb).symm⟩
      rintro rfl
      exact hnab hadj
  · exact ⟨a, hS a ha, hau, hadj⟩

lemma sum_indep_le_edges (G : SimpleGraph α) :
    (∑ v ∈ Finset.univ, (indepNeighborsCard G v : ℝ)) ≤ 2 * (Nat.card G.edgeSet : ℝ) := by
  classical
  have h1 : ∀ v, indepNeighborsCard G v ≤ G.degree v := by
    intro v
    obtain ⟨S, hS, -, hc⟩ :=
      OMA.R_WrittenOnTheWallII_GraphConjecture133_conjecture133_R1.exists_indepNeighbors G v
    rw [← hc, ← card_neighborFinset_eq_degree]
    apply Finset.card_le_card
    intro x hx
    rw [mem_neighborFinset]
    exact hS x hx
  have h2 : ∑ v, G.degree v = 2 * Nat.card G.edgeSet := by
    rw [sum_degrees_eq_twice_card_edges, edgeFinset_card, Nat.card_eq_fintype_card]
  have h3 : ∑ v, indepNeighborsCard G v ≤ 2 * Nat.card G.edgeSet :=
    h2 ▸ Finset.sum_le_sum (fun v _ => h1 v)
  exact_mod_cast h3

end lemmas

theorem main : H1 → H2 → OMA.R_WrittenOnTheWallII_GraphConjecture133_conjecture133_R1.H1 := by
  intro h1 h2 α _ _ _ G hconn hC4
  set r := G.radius.toNat with hr
  have hrtop : G.radius ≠ ⊤ := radius_ne_top_iff.mpr hconn
  have hr1 : 1 ≤ r := by
    have h0 : G.radius ≠ 0 := radius_ne_zero_of_nontrivial
    rw [hr]
    by_contra h
    apply h0
    have : G.radius.toNat = 0 := by omega
    rcases (ENat.toNat_eq_zero.mp this) with h' | h'
    · exact h'
    · exact absurd h' hrtop
  -- every vertex has a far vertex at distance at least the radius
  have hfar : ∀ v : α, ∃ z, r ≤ G.dist v z := by
    intro v
    obtain ⟨z, hz⟩ := G.exists_edist_eq_eccent_of_finite v
    refine ⟨z, ?_⟩
    have hle : G.radius ≤ G.edist v z := hz ▸ radius_le_eccent
    obtain ⟨p, hp⟩ := hconn.exists_walk_length_eq_dist v z
    have h2 : G.edist v z ≤ (G.dist v z : ℕ∞) := by
      rw [← hp]
      exact edist_le p
    have := ENat.toNat_le_toNat (le_trans hle h2) (by simp)
    simpa [hr] using this
  obtain ⟨v0⟩ := (inferInstance : Nonempty α)
  have hP1 : r + 1 ≤ SimpleGraph.path G := by
    obtain ⟨z, hz⟩ := hfar v0
    have := add_one_le_path G hconn v0 z
    omega
  have hP2 : ∀ v, 2 ≤ indepNeighborsCard G v → r + 2 ≤ SimpleGraph.path G := by
    intro v hv
    obtain ⟨z, hz⟩ := hfar v
    obtain ⟨f, hf0, hd, ha⟩ := exists_geodesic G hconn v z
    have hd1 : 1 ≤ G.dist v z := by omega
    have hv1 : G.Adj v (f 1) := by
      have := ha 0 (by omega)
      rwa [hf0] at this
    obtain ⟨c, hvc, hc1, hcn⟩ := exists_escape G hC4 v (f 1) hv1 hv
    have := add_two_le_path G hconn hC4 v z c f hf0 hd ha hd1 hvc hc1 hcn
    omega
  have hsum : ∀ k : ℕ, (∀ v, indepNeighborsCard G v ≤ k) → SimpleGraph.l G ≤ k := by
    intro k hk
    have hn : (0 : ℝ) < Fintype.card α := by exact_mod_cast Fintype.card_pos
    unfold SimpleGraph.l averageIndepNeighbors indepNeighbors
    rw [div_le_iff₀ hn]
    calc (∑ v ∈ Finset.univ, (indepNeighborsCard G v : ℝ))
        ≤ ∑ _v ∈ Finset.univ, (k : ℝ) := by
          apply Finset.sum_le_sum
          intro v _
          exact_mod_cast hk v
      _ = k * Fintype.card α := by simp [mul_comm]
  have hn : (0 : ℝ) < Fintype.card α := by exact_mod_cast Fintype.card_pos
  have hedge : ∀ k : ℕ, 2 * Nat.card G.edgeSet ≤ k * Fintype.card α → SimpleGraph.l G ≤ k := by
    intro k hk
    unfold SimpleGraph.l averageIndepNeighbors indepNeighbors
    rw [div_le_iff₀ hn]
    have hk' : (2 * Nat.card G.edgeSet : ℝ) ≤ k * Fintype.card α := by exact_mod_cast hk
    linarith [sum_indep_le_edges G]
  have hgap : ((SimpleGraph.path G - r : ℕ) : ℝ) = (SimpleGraph.path G : ℝ) - r := by
    rw [Nat.cast_sub (by omega)]
  by_cases hsparse : 2 * Nat.card G.edgeSet ≤ (SimpleGraph.path G - r) * Fintype.card α
  · have hl := hedge _ hsparse
    rw [hgap] at hl
    linarith
  push Not at hsparse
  by_cases hbig : ∃ v, SimpleGraph.path G < r + indepNeighborsCard G v
  · by_cases h3 : r + 3 ≤ SimpleGraph.path G
    · exact h2 G hconn hC4 h3 hbig hsparse
    · obtain ⟨v, hv⟩ := hbig
      have hv2 : 2 ≤ indepNeighborsCard G v := by omega
      have hP := hP2 v hv2
      have hPe : SimpleGraph.path G = r + 2 := by omega
      rw [hPe, Nat.add_sub_cancel_left] at hsparse
      have hl := h1 G hconn hC4 hPe ⟨v, by omega⟩ (by omega)
      rw [hPe]
      push_cast
      linarith
  · push Not at hbig
    have hl := hsum (SimpleGraph.path G - r) (fun v => by have := hbig v; omega)
    rw [hgap] at hl
    linarith

end OMA.R_WrittenOnTheWallII_GraphConjecture133_conjecture133_R1_H1_R1
