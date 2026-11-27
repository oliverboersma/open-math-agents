import FormalConjectures.ErdosProblems.«1013»
import Mathlib

/-! The upper bound for h_3(k) from the lower bound for the maximum chromatic number f(n)
of a triangle-free graph on n vertices. Hefty, Horn, King and Pfender, Improving R(3,k) in
just two bites (2025), give f(n) ≥ (1 - o(1)) (n / log n)^(1/2). If k ≤ f(n) then some
triangle-free graph on at most n vertices has chromatic number exactly k, so h_3(k) ≤ n.
Taking n the integer part of (2 + ε) k^2 log k, an elementary inversion shows that
(1 - δ) (n / log n)^(1/2) ≥ k for a suitable δ > 0 and all large k. -/

namespace OMA.R_Erdos1013_erdos_1013_variants_upper_R1
open Filter

/-- The lower bound of Hefty, Horn, King and Pfender for the maximum chromatic number of
a triangle-free graph on n vertices. -/
def H1 : Prop := ∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
  (1 - ε) * Real.sqrt (n : ℝ) / Real.sqrt (Real.log (n : ℝ)) ≤
    ((sSup {χ : ℕ | ∃ G : SimpleGraph (Fin n), G.CliqueFree 3 ∧ G.chromaticNumber = χ} : ℕ) : ℝ)

/-- If some triangle-free graph on n vertices has chromatic number at least k, then some
triangle-free graph on at most n vertices has chromatic number exactly k. -/
def H2 : Prop := ∀ n k : ℕ, 1 ≤ k →
  k ≤ sSup {χ : ℕ | ∃ G : SimpleGraph (Fin n), G.CliqueFree 3 ∧ G.chromaticNumber = χ} →
    Erdos1013.h3 k ≤ n

/-- The inversion: with n the integer part of (2 + ε) k^2 log k, the quantity
(1 - δ) (n / log n)^(1/2) is at least k for large k. -/
def H3 : Prop := ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ), ∀ N : ℕ, ∀ᶠ k : ℕ in atTop,
  N ≤ ⌊(2 + ε) * (k : ℝ) ^ 2 * Real.log k⌋₊ ∧
  (k : ℝ) ≤ (1 - δ) * Real.sqrt ((⌊(2 + ε) * (k : ℝ) ^ 2 * Real.log k⌋₊ : ℕ) : ℝ) /
    Real.sqrt (Real.log ((⌊(2 + ε) * (k : ℝ) ^ 2 * Real.log k⌋₊ : ℕ) : ℝ))

theorem main : H1 → H2 → H3 → type_of% @Erdos1013.erdos_1013.variants.upper := by
  intro hlow hbridge hinv ε hε
  obtain ⟨δ, hδ, hk⟩ := hinv ε hε
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 (hlow δ hδ)
  filter_upwards [hk N₀, eventually_ge_atTop 1] with k hk' hk1
  obtain ⟨hN, hle⟩ := hk'
  have hf := hN₀ _ hN
  have hkf := hle.trans hf
  have hh := hbridge _ k hk1 (by exact_mod_cast hkf)
  have hx0 : (0 : ℝ) ≤ (2 + ε) * (k : ℝ) ^ 2 * Real.log k :=
    mul_nonneg (mul_nonneg (by linarith) (sq_nonneg _)) (Real.log_natCast_nonneg k)
  have hfloor := Nat.floor_le hx0
  have hh' : (Erdos1013.h3 k : ℝ) ≤ ((⌊(2 + ε) * (k : ℝ) ^ 2 * Real.log k⌋₊ : ℕ) : ℝ) := by
    exact_mod_cast hh
  exact hh'.trans hfloor

end OMA.R_Erdos1013_erdos_1013_variants_upper_R1
