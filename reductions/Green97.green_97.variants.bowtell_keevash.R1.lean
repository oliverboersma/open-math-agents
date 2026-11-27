import FormalConjectures.GreensOpenProblems.«97»
import Mathlib

/-! Reduction of the Bowtell-Keevash theorem (`Green97.green_97.variants.bowtell_keevash`) on
the toroidal n-queens count `T(n)` for `n = 1, 5 (mod 6)` to logarithmic upper (H1) and lower
(H2) bounds: `log (T(n)) / n - log n -> -3`. In `main`, we convert the two-sided logarithmic
asymptotic via `Real.continuous_exp` and the identity `exp (log T(n) / n - log n) =
T(n)^(1/n) / n` (valid once `T(n) > 0` and `n > 0`). -/

namespace OMA.R_Green97_green_97_variants_bowtell_keevash_R1

open Filter Topology Green97

/-- Logarithmic upper bound [BoKe21]: along `toroidalDegrees`, eventually
`log (numToroidalQueens n) / n - log n <= -3 + ε`. -/
def H1 : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in toroidalDegrees,
    Real.log (numToroidalQueens n : ℝ) / (n : ℝ) - Real.log (n : ℝ) ≤ -3 + ε

/-- Logarithmic lower bound [BoKe21]: along `toroidalDegrees`, eventually `0 < numToroidalQueens n`
and `-3 - ε <= log (numToroidalQueens n) / n - log n`. -/
def H2 : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in toroidalDegrees,
    0 < numToroidalQueens n ∧
      -3 - ε ≤ Real.log (numToroidalQueens n : ℝ) / (n : ℝ) - Real.log (n : ℝ)

theorem main : H1 → H2 → type_of% @Green97.green_97.variants.bowtell_keevash := by
  intro h1 h2
  have hlog : Tendsto
      (fun n : ℕ ↦ Real.log (numToroidalQueens n : ℝ) / (n : ℝ) - Real.log (n : ℝ))
      toroidalDegrees (𝓝 (-3)) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    have hε2 : 0 < ε / 2 := half_pos hε
    filter_upwards [h1 (ε / 2) hε2, h2 (ε / 2) hε2] with n hu hl
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith [hl.2]
  have hexp := (Real.continuous_exp.tendsto (-3)).comp hlog
  refine hexp.congr' ?_
  have hge1 : ∀ᶠ n : ℕ in toroidalDegrees, 1 ≤ n :=
    Filter.Eventually.filter_mono inf_le_left (eventually_ge_atTop 1)
  filter_upwards [hge1, h2 1 one_pos] with n hn hpos
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.2 (by omega)
  have hT_pos : (0 : ℝ) < (numToroidalQueens n : ℝ) := Nat.cast_pos.2 hpos.1
  simp only [Function.comp_apply]
  rw [Real.exp_sub, Real.exp_log hn_pos, Real.rpow_def_of_pos hT_pos]
  congr 1
  ring

end OMA.R_Green97_green_97_variants_bowtell_keevash_R1
