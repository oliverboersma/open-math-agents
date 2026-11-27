import OMAReductions.R_Erdos968_erdos_968_variants_infinite_decreasingTriples_R1
import Mathlib

/-! Mathlib's Chebyshev bound pi(x) <= (log 4 + 1) x / log x (eventually_primeCounting_le)
is below delta x once log x > (log 4 + 1)/delta. -/

open Filter

namespace OMA.P2b968

theorem sol : OMA.R_Erdos968_erdos_968_variants_infinite_decreasingTriples_R1.H2 := by
  unfold OMA.R_Erdos968_erdos_968_variants_infinite_decreasingTriples_R1.H2
  intro δ hδ
  have h := tendsto_natCast_atTop_atTop.eventually
    (Chebyshev.eventually_primeCounting_le (ε := 1) one_pos)
  have hlog : ∀ᶠ x : ℕ in atTop, (Real.log 4 + 1) / δ < Real.log x :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_gt_atTop _)
  filter_upwards [h, hlog, eventually_ge_atTop 2] with x hx hl hx2
  rw [Nat.floor_natCast] at hx
  have hx2' : (2:ℝ) ≤ x := by exact_mod_cast hx2
  have hlogpos : 0 < Real.log x := Real.log_pos (by linarith)
  have hxpos : (0:ℝ) < x := by linarith
  rw [div_lt_iff₀ hδ] at hl
  calc (x.primeCounting : ℝ) ≤ (Real.log 4 + 1) * x / Real.log x := hx
    _ < δ * x := by
      rw [div_lt_iff₀ hlogpos]
      nlinarith

end OMA.P2b968

theorem OMA.solution : OMA.R_Erdos968_erdos_968_variants_infinite_decreasingTriples_R1.H2 := OMA.P2b968.sol
