import OMAReductions.R_CramerConjecture_cramer_conjecture_variants_baker_harman_pintz_R1
import Mathlib

/-! The non-prime part of the von Mangoldt sum over [x, x + 2h) is at most psi(Y) - theta(Y)
with Y = x + 2h <= 9x, which Mathlib bounds by C sqrt Y (psi_sub_theta_le_mul_sqrt);
and sqrt x = o(x^0.525). -/

open Filter Real Asymptotics ArithmeticFunction Finset
open scoped Topology

namespace OMA.P2bCr

theorem sol : OMA.R_CramerConjecture_cramer_conjecture_variants_baker_harman_pintz_R1.H2 := by
  unfold OMA.R_CramerConjecture_cramer_conjecture_variants_baker_harman_pintz_R1.H2
  obtain ⟨C, hC⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  rw [Asymptotics.isLittleO_iff]
  intro ε hε
  have hT : Tendsto (fun x : ℕ => (x:ℝ) ^ (0.025:ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  filter_upwards [hT.eventually (eventually_ge_atTop (3 * |C| / ε)), eventually_ge_atTop 1]
    with x hx hx1
  have hx1' : (1:ℝ) ≤ x := by exact_mod_cast hx1
  have hx0 : (0:ℝ) < x := by linarith
  set H := ⌈2*(x:ℝ)^(0.525:ℝ)⌉₊ with hH
  set Y := x + 2 * H with hY
  have hS0 : 0 ≤ ∑ d ∈ (Ico x Y).filter (fun d => ¬ d.Prime), (Λ d:ℝ) :=
    Finset.sum_nonneg (fun d _ => ArithmeticFunction.vonMangoldt_nonneg)
  have hsub : (Ico x Y).filter (fun d => ¬ d.Prime) ⊆ (Ioc 0 ⌊(Y:ℝ)⌋₊).filter (fun d => ¬ d.Prime) := by
    intro d hd
    rw [Finset.mem_filter, Finset.mem_Ico] at hd
    rw [Finset.mem_filter, Finset.mem_Ioc, Nat.floor_natCast]
    exact ⟨⟨by omega, by omega⟩, hd.2⟩
  have h1 : ∑ d ∈ (Ico x Y).filter (fun d => ¬ d.Prime), (Λ d:ℝ) ≤ C * Real.sqrt Y := by
    calc _ ≤ ∑ d ∈ (Ioc 0 ⌊(Y:ℝ)⌋₊).filter (fun d => ¬ d.Prime), (Λ d:ℝ) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub
            (fun d _ _ => ArithmeticFunction.vonMangoldt_nonneg)
      _ = Chebyshev.psi Y - Chebyshev.theta Y := (Chebyshev.psi_sub_theta_eq_sum_not_prime _).symm
      _ ≤ C * Real.sqrt Y := hC _
  have hp : (x:ℝ) ^ (0.525:ℝ) ≤ x := by
    calc (x:ℝ) ^ (0.525:ℝ) ≤ (x:ℝ) ^ (1:ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hx1' (by norm_num)
      _ = x := Real.rpow_one _
  have hHle : (H:ℝ) ≤ 2 * (x:ℝ) ^ (0.525:ℝ) + 1 :=
    (Nat.ceil_lt_add_one (by positivity)).le
  have hYle : (Y:ℝ) ≤ 9 * x := by
    rw [hY]; push_cast; nlinarith
  have hsqY : Real.sqrt Y ≤ 3 * Real.sqrt x := by
    calc Real.sqrt Y ≤ Real.sqrt (9 * x) := Real.sqrt_le_sqrt hYle
      _ = 3 * Real.sqrt x := by
        rw [Real.sqrt_mul (by norm_num), show (9:ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have hsplit : (x:ℝ) ^ (0.525:ℝ) = Real.sqrt x * (x:ℝ) ^ (0.025:ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hx0]; norm_num
  have hsx : 0 ≤ Real.sqrt x := Real.sqrt_nonneg _
  rw [Real.norm_of_nonneg hS0, Real.norm_of_nonneg (by positivity), hsplit]
  rw [div_le_iff₀ hε] at hx
  calc _ ≤ C * Real.sqrt Y := h1
    _ ≤ |C| * Real.sqrt Y := mul_le_mul_of_nonneg_right (le_abs_self C) (Real.sqrt_nonneg _)
    _ ≤ |C| * (3 * Real.sqrt x) := mul_le_mul_of_nonneg_left hsqY (abs_nonneg C)
    _ = (3 * |C|) * Real.sqrt x := by ring
    _ ≤ ((x:ℝ) ^ (0.025:ℝ) * ε) * Real.sqrt x := mul_le_mul_of_nonneg_right hx hsx
    _ = ε * (Real.sqrt x * (x:ℝ) ^ (0.025:ℝ)) := by ring

end OMA.P2bCr

theorem OMA.solution : OMA.R_CramerConjecture_cramer_conjecture_variants_baker_harman_pintz_R1.H2 := OMA.P2bCr.sol
