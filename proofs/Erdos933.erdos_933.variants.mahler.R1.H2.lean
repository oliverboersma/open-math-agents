import OMAReductions.R_Erdos933_erdos_933_variants_mahler_R1
import Mathlib

-- Step Erdos933.erdos_933.variants.mahler.R1.H2: hypothesis H2 of reduction Erdos933.erdos_933.variants.mahler.R1
-- Credit: @ivillar

/-!
From `F n < n ^ (1 + ε)` eventually for every `ε > 0` to a single exponent `1 + o(1)`:
take `c n` to be the infimum of the admissible `ε` at `n`, plus `1 / n`.
-/
open Filter Asymptotics
open scoped Topology

namespace F2E933

theorem diag : ∀ F : ℕ → ℝ, (∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop, F n < (n : ℝ) ^ (1 + ε)) →
    ∃ c : ℕ → ℝ, (c =o[atTop] (1 : ℕ → ℝ)) ∧ ∀ᶠ n in atTop, F n < (n : ℝ) ^ (1 + c n) := by
  intro F hF
  have hbdd : ∀ n : ℕ, BddBelow {ε : ℝ | 0 < ε ∧ F n < (n : ℝ) ^ (1 + ε)} :=
    fun n => ⟨0, fun ε hε => hε.1.le⟩
  have hnonneg : ∀ n : ℕ, 0 ≤ sInf {ε : ℝ | 0 < ε ∧ F n < (n : ℝ) ^ (1 + ε)} :=
    fun n => Real.sInf_nonneg (fun ε hε => hε.1.le)
  refine ⟨fun n => sInf {ε : ℝ | 0 < ε ∧ F n < (n : ℝ) ^ (1 + ε)} + 1 / (n : ℝ), ?_, ?_⟩
  · have ht : Tendsto (fun n : ℕ => sInf {ε : ℝ | 0 < ε ∧ F n < (n : ℝ) ^ (1 + ε)} + 1 / (n : ℝ))
        atTop (𝓝 0) := by
      rw [Metric.tendsto_atTop]
      intro ε hε
      obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp (hF (ε / 2) (by positivity))
      obtain ⟨N₂, hN₂⟩ := exists_nat_gt (2 / ε)
      refine ⟨max N₁ (max N₂ 1), fun n hn => ?_⟩
      have h1 : N₁ ≤ n := le_trans (le_max_left _ _) hn
      have h2 : N₂ ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn
      have h3 : 1 ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hn
      have hn0 : (0 : ℝ) < n := by exact_mod_cast h3
      have hle : sInf {ε' : ℝ | 0 < ε' ∧ F n < (n : ℝ) ^ (1 + ε')} ≤ ε / 2 :=
        csInf_le (hbdd n) ⟨by positivity, hN₁ n h1⟩
      have hinv : 1 / (n : ℝ) < ε / 2 := by
        have h2' : 2 / ε < n := lt_of_lt_of_le hN₂ (by exact_mod_cast h2)
        rw [div_lt_iff₀ hn0]
        rw [div_lt_iff₀ hε] at h2'
        linarith
      have hpos : 0 ≤ 1 / (n : ℝ) := by positivity
      rw [Real.dist_eq, sub_zero, abs_of_nonneg (add_nonneg (hnonneg n) hpos)]
      linarith
    exact (isLittleO_one_iff ℝ).mpr ht
  · filter_upwards [hF 1 one_pos, eventually_ge_atTop 1] with n hn h1
    have hn0 : (0 : ℝ) < n := by exact_mod_cast h1
    have hne : {ε : ℝ | 0 < ε ∧ F n < (n : ℝ) ^ (1 + ε)}.Nonempty := ⟨1, one_pos, hn⟩
    have hlt : sInf {ε : ℝ | 0 < ε ∧ F n < (n : ℝ) ^ (1 + ε)} <
        sInf {ε : ℝ | 0 < ε ∧ F n < (n : ℝ) ^ (1 + ε)} + 1 / (n : ℝ) := by
      have : 0 < 1 / (n : ℝ) := by positivity
      linarith
    obtain ⟨ε, hε, hεlt⟩ := exists_lt_of_csInf_lt hne hlt
    refine lt_of_lt_of_le hε.2 ?_
    apply Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast h1)
    linarith

end F2E933

theorem OMA.solution : OMA.R_Erdos933_erdos_933_variants_mahler_R1.H2 :=
  F2E933.diag
