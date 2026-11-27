import FormalConjectures.GreensOpenProblems.«87»
import Mathlib

/-! Reduction of `Green87.green_87.variants.order` (Eberhard-Ford-Green 2016) to the uniform
upper bound (H1) and uniform lower bound (H2) on `i n k` for `2 <= k` and `2 * k <= n`.
In `main`, we pass to the limit `n -> infinity` via `le_of_tendsto` and `ge_of_tendsto`,
establish nonnegativity of `p k` and the comparison function for `k >= 2`, and deduce
`IsTheta` (`=Θ[atTop]`). -/

namespace OMA.R_Green87_green_87_variants_order_R1

open Filter Asymptotics Topology Green87

/-- Uniform upper bound [EFG16, Theorem 1.1]: there is a constant `C > 0` such that
`i n k <= C * k^(-δ) * (log k)^(-3/2)` for all `k >= 2` and `n >= 2 * k`. -/
def H1 : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ k : ℕ, 2 ≤ k → ∀ n : ℕ, 2 * k ≤ n →
    i n k ≤ C * ((k : ℝ) ^ (-δ) * (Real.log k) ^ (-(3 / 2 : ℝ)))

/-- Uniform lower bound [EFG16, Theorem 1.1]: there is a constant `c > 0` such that
`c * k^(-δ) * (log k)^(-3/2) <= i n k` for all `k >= 2` and `n >= 2 * k`. -/
def H2 : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ k : ℕ, 2 ≤ k → ∀ n : ℕ, 2 * k ≤ n →
    c * ((k : ℝ) ^ (-δ) * (Real.log k) ^ (-(3 / 2 : ℝ))) ≤ i n k

theorem main : H1 → H2 → type_of% @Green87.green_87.variants.order := by
  rintro ⟨C, hC, hupper⟩ ⟨c, hc, hlower⟩ p hp
  set g : ℕ → ℝ := fun k ↦ (k : ℝ) ^ (-δ) * (Real.log k) ^ (-(3 / 2 : ℝ))
  have hg_pos : ∀ k : ℕ, 2 ≤ k → 0 < g k := by
    intro k hk
    have hk1 : (1 : ℝ) < (k : ℝ) := by exact_mod_cast (show 1 < k by omega)
    have hlog : 0 < Real.log (k : ℝ) := Real.log_pos hk1
    have h1 : 0 < (k : ℝ) ^ (-δ) := Real.rpow_pos_of_pos (by linarith) (-δ)
    have h2 : 0 < (Real.log (k : ℝ)) ^ (-(3 / 2 : ℝ)) := Real.rpow_pos_of_pos hlog _
    exact mul_pos h1 h2
  have hp_le : ∀ k : ℕ, 2 ≤ k → p k ≤ C * g k := by
    intro k hk
    exact le_of_tendsto (hp k) (by
      filter_upwards [eventually_ge_atTop (2 * k)] with n hn
      exact hupper k hk n hn)
  have hp_ge : ∀ k : ℕ, 2 ≤ k → c * g k ≤ p k := by
    intro k hk
    exact ge_of_tendsto (hp k) (by
      filter_upwards [eventually_ge_atTop (2 * k)] with n hn
      exact hlower k hk n hn)
  constructor
  · rw [Asymptotics.isBigO_iff]
    refine ⟨C, ?_⟩
    filter_upwards [eventually_ge_atTop 2] with k hk
    have hgp : 0 ≤ g k := (hg_pos k hk).le
    have hpp : 0 ≤ p k := le_trans (mul_nonneg hc.le hgp) (hp_ge k hk)
    rw [Real.norm_of_nonneg hpp, Real.norm_of_nonneg hgp]
    exact hp_le k hk
  · rw [Asymptotics.isBigO_iff]
    refine ⟨c⁻¹, ?_⟩
    filter_upwards [eventually_ge_atTop 2] with k hk
    have hgp : 0 ≤ g k := (hg_pos k hk).le
    have hpp : 0 ≤ p k := le_trans (mul_nonneg hc.le hgp) (hp_ge k hk)
    rw [Real.norm_of_nonneg hgp, Real.norm_of_nonneg hpp]
    have h := hp_ge k hk
    calc
      g k = c⁻¹ * (c * g k) := by field_simp [hc.ne']
      _ ≤ c⁻¹ * p k := mul_le_mul_of_nonneg_left h (inv_nonneg.2 hc.le)

end OMA.R_Green87_green_87_variants_order_R1
