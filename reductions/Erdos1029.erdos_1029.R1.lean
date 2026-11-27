import FormalConjectures.ErdosProblems.«1029»

-- Reduction Erdos1029.erdos_1029.R1 of Erdős Problem 1029
-- Credit: @mucoucah
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

open Filter SimpleGraph

namespace OMA.R_Erdos1029_erdos_1029_R1

/-- Clique sizes `k = 4 s` (divisible by 4): for every `a` and all large `s` there is a graph on
`a * k * 2^(k/2)` vertices with neither a `k`-clique nor a `k`-independent set. -/
def H1 : Prop :=
  ∀ a : ℕ, ∃ N : ℕ, ∀ s : ℕ, N ≤ s →
    ∃ G : SimpleGraph (Fin (a * (2 * (2 * s) * 2 ^ (2 * s)))),
      G.CliqueFree (2 * (2 * s)) ∧ Gᶜ.CliqueFree (2 * (2 * s))

/-- Clique sizes `k = 4 s + 2` (congruent to 2 mod 4): same graph-existence statement. -/
def H2 : Prop :=
  ∀ a : ℕ, ∃ N : ℕ, ∀ s : ℕ, N ≤ s →
    ∃ G : SimpleGraph (Fin (a * (2 * (2 * s + 1) * 2 ^ (2 * s + 1)))),
      G.CliqueFree (2 * (2 * s + 1)) ∧ Gᶜ.CliqueFree (2 * (2 * s + 1))

lemma forcesClique_mono {n m k : ℕ} (hnm : n ≤ m)
    (hn : ∀ G : SimpleGraph (Fin n), ¬ (G.CliqueFree k ∧ Gᶜ.CliqueFree k)) :
    ∀ G : SimpleGraph (Fin m), ¬ (G.CliqueFree k ∧ Gᶜ.CliqueFree k) := by
  intro G hG
  let e : Fin n ↪ Fin m := Fin.castLEEmb hnm
  let H := G.comap e
  let f : H ↪g G := SimpleGraph.Embedding.comap e G
  exact hn H ⟨hG.1.comap f.isContained, hG.2.comap f.complEquiv.isContained⟩

lemma forcesClique_choose (k : ℕ) :
    ∀ G : SimpleGraph (Fin ((k + k).choose k)), ¬ (G.CliqueFree k ∧ Gᶜ.CliqueFree k) := by
  classical
  intro G hG
  let c (s : Finset (Fin ((k + k).choose k))) : Bool :=
    decide (G.IsClique (s : Set _))
  rcases Combinatorics.Diagonal.hasRamseyProperty_choose k k c Finset.univ (by simp)
    with ⟨s, _, hs, hm⟩ | ⟨s, _, hs, hm⟩
  · apply hG.2 s
    refine ⟨?_, hs⟩
    intro x hx y hy hxy
    have hc := hm {x, y}
      (Finset.insert_subset hx (Finset.singleton_subset_iff.mpr hy)) (Finset.card_pair hxy)
    have hn : ¬ G.Adj x y := by simpa [c, hxy] using hc
    exact (G.compl_adj x y).2 ⟨hxy, hn⟩
  · apply hG.1 s
    refine ⟨?_, hs⟩
    intro x hx y hy hxy
    have hc := hm {x, y}
      (Finset.insert_subset hx (Finset.singleton_subset_iff.mpr hy)) (Finset.card_pair hxy)
    simpa [c, hxy] using hc

lemma lt_diagonalRamsey_iff (n k : ℕ) :
    n < diagonalRamsey k ↔
      ∃ G : SimpleGraph (Fin n), G.CliqueFree k ∧ Gᶜ.CliqueFree k := by
  classical
  have heq : diagonalRamsey k = sInf {m | ∀ G : SimpleGraph (Fin m),
      ¬ (G.CliqueFree k ∧ Gᶜ.CliqueFree k)} := by
    simp only [diagonalRamsey, classicalRamsey, graphRamsey,
      not_and_or, not_cliqueFree_iff_top_isContained]
  have hmem : diagonalRamsey k ∈ {m | ∀ G : SimpleGraph (Fin m),
      ¬ (G.CliqueFree k ∧ Gᶜ.CliqueFree k)} :=
    heq ▸ Nat.sInf_mem ⟨_, forcesClique_choose k⟩
  have hiff : diagonalRamsey k ≤ n ↔
      ∀ G : SimpleGraph (Fin n), ¬ (G.CliqueFree k ∧ Gᶜ.CliqueFree k) :=
    ⟨fun hn ↦ forcesClique_mono hn hmem, fun hn ↦ heq.trans_le (Nat.sInf_le hn)⟩
  rw [← not_le, hiff]
  simp

lemma scale_pos {k : ℕ} (hk : 0 < k) : 0 < (k : ℝ) * (2 : ℝ) ^ ((k : ℝ) / 2) := by
  positivity

lemma tendsto_iff_cliqueFree_graphs :
    Tendsto (fun k : ℕ ↦ (diagonalRamsey k : ℝ) / ((k : ℝ) * (2 : ℝ) ^ ((k : ℝ) / 2)))
        atTop atTop ↔
      ∀ a : ℕ, ∀ᶠ k : ℕ in atTop,
        ∃ G : SimpleGraph (Fin ⌊(a : ℝ) * ((k : ℝ) * (2 : ℝ) ^ ((k : ℝ) / 2))⌋₊),
          G.CliqueFree k ∧ Gᶜ.CliqueFree k := by
  have hk : ∀ᶠ k : ℕ in atTop, 0 < k := eventually_gt_atTop 0
  constructor
  · intro h a
    filter_upwards [(tendsto_atTop.1 h) ((a : ℝ) + 1), hk] with k ha hk'
    apply (lt_diagonalRamsey_iff _ _).mp
    have hlt : (a : ℝ) < (diagonalRamsey k : ℝ) / ((k : ℝ) * (2 : ℝ) ^ ((k : ℝ) / 2)) := by
      linarith
    exact (Nat.floor_lt (mul_nonneg (Nat.cast_nonneg a) (scale_pos hk').le)).2
      ((lt_div_iff₀ (scale_pos hk')).1 hlt)
  · intro h
    refine tendsto_atTop.2 fun b ↦ ?_
    obtain ⟨a, ha⟩ := exists_nat_ge b
    filter_upwards [h a, hk] with k hG hk'
    have hlt := (lt_diagonalRamsey_iff _ _).2 hG
    exact ha.trans ((lt_div_iff₀ (scale_pos hk')).2 (Nat.lt_of_floor_lt hlt)).le

lemma scale_even (t : ℕ) :
    (((2 * t : ℕ) : ℝ) * (2 : ℝ) ^ (((2 * t : ℕ) : ℝ) / 2)) = (2 : ℝ) * t * 2 ^ t := by
  have hexp : ((2 * t : ℕ) : ℝ) / 2 = (t : ℝ) := by push_cast; ring
  rw [hexp, Real.rpow_natCast]
  push_cast
  norm_num

lemma floor_mul_scale_even (a t : ℕ) :
    ⌊(a : ℝ) * (((2 * t : ℕ) : ℝ) * (2 : ℝ) ^ (((2 * t : ℕ) : ℝ) / 2))⌋₊
      = a * (2 * t * 2 ^ t) := by
  have h : (a : ℝ) * (((2 * t : ℕ) : ℝ) * (2 : ℝ) ^ (((2 * t : ℕ) : ℝ) / 2))
      = ((a * (2 * t * 2 ^ t) : ℕ) : ℝ) := by
    rw [scale_even]; push_cast; ring
  rw [h, Nat.floor_natCast]

lemma scale_le_four_mul_of_div_two {k : ℕ} (hk : 2 ≤ k) :
    (k : ℝ) * (2 : ℝ) ^ ((k : ℝ) / 2) ≤
      4 * (((2 * (k / 2) : ℕ) : ℝ) * (2 : ℝ) ^ (((2 * (k / 2) : ℕ) : ℝ) / 2)) := by
  generalize hj : 2 * (k / 2) = j
  have hnat : k ≤ j + 1 ∧ 1 ≤ j := by omega
  have hk' : (k : ℝ) ≤ 2 * j := by
    exact_mod_cast (show k ≤ 2 * j by omega)
  have hpow : (2 : ℝ) ^ ((k : ℝ) / 2) ≤ 2 * (2 : ℝ) ^ ((j : ℝ) / 2) := by
    have hreal : (k : ℝ) ≤ (j : ℝ) + 1 := by exact_mod_cast hnat.1
    calc
      (2 : ℝ) ^ ((k : ℝ) / 2) ≤ (2 : ℝ) ^ (1 + (j : ℝ) / 2) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = 2 * (2 : ℝ) ^ ((j : ℝ) / 2) := by
        rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_one]
  calc
    (k : ℝ) * (2 : ℝ) ^ ((k : ℝ) / 2)
        ≤ (2 * (j : ℝ)) * (2 * (2 : ℝ) ^ ((j : ℝ) / 2)) :=
      mul_le_mul hk' hpow (by positivity) (by positivity)
    _ = 4 * ((j : ℝ) * (2 : ℝ) ^ ((j : ℝ) / 2)) := by ring

lemma tendsto_of_even_cliqueFree_graphs
    (h : ∀ a : ℕ, ∀ᶠ t : ℕ in atTop,
        ∃ G : SimpleGraph (Fin (a * (2 * t * 2 ^ t))),
          G.CliqueFree (2 * t) ∧ Gᶜ.CliqueFree (2 * t)) :
    Tendsto (fun k : ℕ ↦ (diagonalRamsey k : ℝ) / ((k : ℝ) * (2 : ℝ) ^ ((k : ℝ) / 2)))
        atTop atTop := by
  rw [tendsto_iff_cliqueFree_graphs]
  intro a
  obtain ⟨N, hN⟩ := eventually_atTop.1 (h (4 * a))
  refine eventually_atTop.2 ⟨2 * N + 2, fun k hk ↦ ?_⟩
  have hjk : 2 * (k / 2) ≤ k := by omega
  have hn : ⌊(a : ℝ) * ((k : ℝ) * (2 : ℝ) ^ ((k : ℝ) / 2))⌋₊
      ≤ (4 * a) * (2 * (k / 2) * 2 ^ (k / 2)) := by
    rw [← floor_mul_scale_even (4 * a) (k / 2)]
    apply Nat.floor_mono
    calc
      (a : ℝ) * ((k : ℝ) * (2 : ℝ) ^ ((k : ℝ) / 2))
          ≤ (a : ℝ) * (4 * (((2 * (k / 2) : ℕ) : ℝ) *
              (2 : ℝ) ^ (((2 * (k / 2) : ℕ) : ℝ) / 2))) :=
        mul_le_mul_of_nonneg_left (scale_le_four_mul_of_div_two (by omega)) (by positivity)
      _ = ((4 * a : ℕ) : ℝ) * (((2 * (k / 2) : ℕ) : ℝ) *
              (2 : ℝ) ^ (((2 * (k / 2) : ℕ) : ℝ) / 2)) := by push_cast; ring
  obtain ⟨G, hG, hGc⟩ := hN (k / 2) (by omega)
  let e := Fin.castLEEmb hn
  let f := SimpleGraph.Embedding.comap e G
  exact ⟨G.comap e, (hG.mono hjk).comap f.isContained,
    (hGc.mono hjk).comap f.complEquiv.isContained⟩

theorem main : H1 → H2 → type_of% @Erdos1029.erdos_1029 := by
  intro h1 h2
  apply tendsto_of_even_cliqueFree_graphs
  intro a
  obtain ⟨N1, hN1⟩ := h1 a
  obtain ⟨N2, hN2⟩ := h2 a
  refine eventually_atTop.2 ⟨2 * (N1 + N2), fun t ht ↦ ?_⟩
  rcases Nat.even_or_odd' t with ⟨s, rfl | rfl⟩
  · exact hN1 s (by omega)
  · exact hN2 s (by omega)

end OMA.R_Erdos1029_erdos_1029_R1
