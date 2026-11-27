import OMAReductions.R_Erdos1013_erdos_1013_variants_upper_R1
import Mathlib

-- Reduction Erdos1013.erdos_1013.variants.upper.R1.H1.R1 of step Erdos1013.erdos_1013.variants.upper.R1.H1
-- Credit: @marcusbuffett

/-! The lower bound f(n) ≥ (1 - o(1)) (n / log n)^(1/2) for the maximum chromatic number of a
triangle-free graph on n vertices, from the Ramsey lower bound
R(3,k) ≥ (1/2 - o(1)) k^2 / log k of Hefty, Horn, King and Pfender (Improving R(3,k) in just
two bites, 2025). A triangle-free graph G on n vertices with no independent set of size k
satisfies n ≤ χ(G) k, since every colour class is independent. For large n choose
k about (n log n)^(1/2) / (1 - ε): then n log k ≤ (1/2 - δ) k^2, so such a graph exists, and
χ(G) ≥ n / k ≥ (1 - ε) (n / log n)^(1/2).

H1 is the Ramsey lower bound, in the form of a triangle-free graph on any n vertices below the
bound whose complement has no k-clique. H2 is the colour-class count. H3 is the elementary
choice of k. -/

namespace OMA.R_Erdos1013_erdos_1013_variants_upper_R1_H1_R1

open Filter

/-- Hefty, Horn, King and Pfender: R(3,k) ≥ (1/2 - o(1)) k^2 / log k, stated as the existence
of a triangle-free graph without independent k-sets on every n ≤ (1/2 - δ) k^2 / log k
vertices, for each δ > 0 and all large k. -/
def H1 : Prop := ∀ δ > (0 : ℝ), ∀ᶠ k : ℕ in atTop, ∀ n : ℕ,
  (n : ℝ) * Real.log k ≤ (1 / 2 - δ) * (k : ℝ) ^ 2 →
    ∃ G : SimpleGraph (Fin n), G.CliqueFree 3 ∧ Gᶜ.CliqueFree k

/-- A graph on n vertices whose complement has no k-clique, properly coloured with c colours,
has n ≤ c k: every colour class is an independent set. -/
def H2 : Prop := ∀ (n k c : ℕ) (G : SimpleGraph (Fin n)),
  Gᶜ.CliqueFree k → G.Colorable c → n ≤ c * k

/-- The choice of k: for ε in (0,1) there is δ > 0 such that for every bound K and all large n
some k ≥ K has n log k ≤ (1/2 - δ) k^2 and (1 - ε) (n / log n)^(1/2) k ≤ n. -/
def H3 : Prop := ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ δ > (0 : ℝ), ∀ K : ℕ, ∀ᶠ n : ℕ in atTop,
  ∃ k : ℕ, K ≤ k ∧ (n : ℝ) * Real.log k ≤ (1 / 2 - δ) * (k : ℝ) ^ 2 ∧
    (1 - ε) * Real.sqrt (n : ℝ) / Real.sqrt (Real.log (n : ℝ)) * k ≤ n

theorem main : H1 → H2 → H3 → OMA.R_Erdos1013_erdos_1013_variants_upper_R1.H1 := by
  intro ramsey count choose ε hε
  by_cases hε1 : 1 ≤ ε
  · refine Eventually.of_forall fun n => ?_
    have h0 : (1 - ε) * Real.sqrt (n : ℝ) / Real.sqrt (Real.log (n : ℝ)) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonpos_of_nonneg (by linarith) (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
    exact h0.trans (Nat.cast_nonneg _)
  push_neg at hε1
  obtain ⟨δ, hδ, hk⟩ := choose ε hε hε1
  obtain ⟨K, hK⟩ := eventually_atTop.1 (ramsey δ hδ)
  filter_upwards [hk (max K 1)] with n hn
  obtain ⟨k, hKk, hlog, hfin⟩ := hn
  obtain ⟨G, htri, hind⟩ := hK k (le_trans (le_max_left _ _) hKk) n hlog
  have hk1 : 1 ≤ k := le_trans (le_max_right _ _) hKk
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk1
  set c := ENat.toNat G.chromaticNumber with hc
  have hcol : G.Colorable c := G.colorable_chromaticNumber_of_fintype
  have hnc : (n : ℝ) ≤ c * k := by exact_mod_cast count n k c G hind hcol
  have hmem : c ∈ {χ : ℕ | ∃ G : SimpleGraph (Fin n), G.CliqueFree 3 ∧ G.chromaticNumber = χ} := by
    refine ⟨G, htri, ?_⟩
    rw [hc, ENat.coe_toNat]
    exact ne_top_of_le_ne_top (ENat.natCast_ne_top n)
      (le_trans G.chromaticNumber_le_card (by simp))
  have hbdd : BddAbove {χ : ℕ | ∃ G : SimpleGraph (Fin n), G.CliqueFree 3 ∧ G.chromaticNumber = χ} := by
    refine ⟨n, ?_⟩
    rintro χ ⟨H, -, hH⟩
    have h := H.chromaticNumber_le_card
    rw [hH, Fintype.card_fin] at h
    exact_mod_cast h
  have hcf : (c : ℝ) ≤ ((sSup {χ : ℕ | ∃ G : SimpleGraph (Fin n), G.CliqueFree 3 ∧ G.chromaticNumber = χ} : ℕ) : ℝ) := by
    exact_mod_cast le_csSup hbdd hmem
  have hmain : (1 - ε) * Real.sqrt (n : ℝ) / Real.sqrt (Real.log (n : ℝ)) ≤ c := by
    have h2 : (1 - ε) * Real.sqrt (n : ℝ) / Real.sqrt (Real.log (n : ℝ)) * k ≤ c * k :=
      hfin.trans hnc
    exact le_of_mul_le_mul_right h2 hkpos
  exact hmain.trans hcf

end OMA.R_Erdos1013_erdos_1013_variants_upper_R1_H1_R1
