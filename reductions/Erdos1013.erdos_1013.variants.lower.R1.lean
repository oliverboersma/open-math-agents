import FormalConjectures.ErdosProblems.«1013»
import Mathlib

/-! The lower bound for h_3(k) from the upper bound for the maximum chromatic number f(n)
of a triangle-free graph on n vertices. Davies and Illingworth, The chi-Ramsey problem for
triangle-free graphs, SIAM J. Discrete Math. 36 (2022), give
f(n) ≤ (2 + o(1)) (n / log n)^(1/2). Triangle-free graphs of every chromatic number exist
(Mycielski 1955), so h_3(k) is attained by a graph on n = h_3(k) vertices, which gives
k ≤ n and k ≤ f(n). An elementary inversion of k ≤ (2 + δ) (n / log n)^(1/2) then shows
n ≥ (1/2 - ε) k^2 log k for large k. -/

namespace OMA.R_Erdos1013_erdos_1013_variants_lower_R1
open Filter

/-- The upper bound of Davies and Illingworth for the maximum chromatic number of a
triangle-free graph on n vertices. -/
def H1 : Prop := ∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
  ((sSup {χ : ℕ | ∃ G : SimpleGraph (Fin n), G.CliqueFree 3 ∧ G.chromaticNumber = χ} : ℕ) : ℝ)
    ≤ (2 + ε) * Real.sqrt (n : ℝ) / Real.sqrt (Real.log (n : ℝ))

/-- Mycielski: triangle-free graphs of every chromatic number exist. -/
def H2 : Prop := ∀ k : ℕ, 1 ≤ k →
  ∃ n : ℕ, ∃ G : SimpleGraph (Fin n), G.CliqueFree 3 ∧ G.chromaticNumber = k

/-- When such a graph exists, a graph on h_3(k) vertices attains chromatic number k. -/
def H3 : Prop := ∀ k : ℕ, 1 ≤ k →
  (∃ n : ℕ, ∃ G : SimpleGraph (Fin n), G.CliqueFree 3 ∧ G.chromaticNumber = k) →
  k ≤ Erdos1013.h3 k ∧
    k ≤ sSup {χ : ℕ | ∃ G : SimpleGraph (Fin (Erdos1013.h3 k)),
      G.CliqueFree 3 ∧ G.chromaticNumber = χ}

/-- The inversion of the bound k ≤ (2 + δ) (n / log n)^(1/2). -/
def H4 : Prop := ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ), ∀ᶠ k : ℕ in atTop, ∀ n : ℕ,
  (k : ℝ) ≤ (2 + δ) * Real.sqrt (n : ℝ) / Real.sqrt (Real.log (n : ℝ)) →
    (1 / 2 - ε) * (k : ℝ) ^ 2 * Real.log k ≤ n

theorem main : H1 → H2 → H3 → H4 → type_of% @Erdos1013.erdos_1013.variants.lower := by
  intro hup hmyc hbridge hinv ε hε
  obtain ⟨δ, hδ, hk⟩ := hinv ε hε
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 (hup δ hδ)
  filter_upwards [hk, eventually_ge_atTop (max N₀ 1)] with k hkn hkN
  have hk1 : 1 ≤ k := le_trans (le_max_right _ _) hkN
  have hkN₀ : N₀ ≤ k := le_trans (le_max_left _ _) hkN
  obtain ⟨hle, hsup⟩ := hbridge k hk1 (hmyc k hk1)
  have hf := hN₀ (Erdos1013.h3 k) (le_trans hkN₀ hle)
  have hsup' : (k : ℝ) ≤ ((sSup {χ : ℕ | ∃ G : SimpleGraph (Fin (Erdos1013.h3 k)),
      G.CliqueFree 3 ∧ G.chromaticNumber = χ} : ℕ) : ℝ) := by exact_mod_cast hsup
  exact hkn (Erdos1013.h3 k) (hsup'.trans hf)

end OMA.R_Erdos1013_erdos_1013_variants_lower_R1
