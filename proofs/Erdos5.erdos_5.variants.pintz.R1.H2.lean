import OMAReductions.R_Erdos5_erdos_5_variants_pintz_R1
import Mathlib

/-! The n-th prime is between n and 5 n log n for large n, so log p_n / log n tends to 1.
The upper bound comes from the Chebyshev lower bound theta(x) >= x/2.
Same proof as the merged Erdos5.erdos_5.variants.merikoski_measure.R1.H2 (PR #4060, this author).
Credit: the lemma eventually_theta_ge_half is reused from the merged proof
proofs/Erdos32.erdos_32.variants.ruzsa.lean by @mucoucah (PR #3525). -/

open Filter Real
open scoped Topology

namespace OMA.P2bErdos5H2

lemma eventually_theta_ge_half : ∀ᶠ x : ℝ in atTop, x / 2 ≤ Chebyshev.theta x := by
  have hsqrt : Real.sqrt =o[atTop] (id : ℝ → ℝ) := by
    refine Asymptotics.isLittleO_iff.mpr fun ε hε => ?_
    filter_upwards [eventually_ge_atTop ((1 / ε) ^ 2)] with x hx
    have hx0 : 0 ≤ x := (sq_nonneg _).trans hx
    have hh : 1 / ε ≤ Real.sqrt x := Real.le_sqrt_of_sq_le hx
    have he : 1 ≤ ε * Real.sqrt x := by
      rw [div_le_iff₀ hε] at hh
      simpa [mul_comm] using hh
    simp only [id_eq, Real.norm_eq_abs, abs_of_nonneg hx0,
      abs_of_nonneg (Real.sqrt_nonneg x)]
    calc
      Real.sqrt x = 1 * Real.sqrt x := (one_mul _).symm
      _ ≤ (ε * Real.sqrt x) * Real.sqrt x :=
        mul_le_mul_of_nonneg_right he (Real.sqrt_nonneg x)
      _ = ε * x := by rw [mul_assoc, Real.mul_self_sqrt hx0]
  have herr := (Chebyshev.isBigO_psi_sub_theta_sqrt.trans_isLittleO hsqrt).bound
    (show (0 : ℝ) < 1 / 16 by norm_num)
  have hlog := Real.isLittleO_log_id_atTop.bound (show (0 : ℝ) < 1 / 32 by norm_num)
  filter_upwards [herr, hlog, eventually_ge_atTop (32 : ℝ)] with x he hl hx
  have hx0 : 0 ≤ x := by linarith
  simp only [id_eq, Real.norm_eq_abs, abs_of_nonneg hx0] at he hl
  have hl' := (le_abs_self (Real.log x)).trans hl
  have hlogadd : Real.log (x + 2) ≤ Real.log 2 + Real.log x := by
    rw [← Real.log_mul (by norm_num) (by positivity)]
    exact Real.log_le_log (by positivity) (by linarith)
  have hpsi := Chebyshev.psi_ge' hx0
  have hdiff := (le_abs_self (Chebyshev.psi x - Chebyshev.theta x)).trans he
  have hprod := mul_le_mul_of_nonneg_left
    (show (2 / 3 : ℝ) ≤ Real.log 2 by linarith [Real.log_two_gt_d9]) (show 0 ≤ x - 1 by linarith)
  linarith [Real.log_two_lt_d9]

lemma pi_lower : ∀ᶠ x : ℝ in atTop, x / (2 * Real.log x) ≤ (Nat.primeCounting ⌊x⌋₊ : ℝ) := by
  filter_upwards [eventually_theta_ge_half, eventually_ge_atTop (3 : ℝ)] with x hx hx3
  have hlog : 0 < Real.log x := Real.log_pos (by linarith)
  have h1 := Chebyshev.theta_le_psi x
  have h2 := Chebyshev.psi_le_primeCounting_mul_log' x
  rw [div_le_iff₀ (by positivity)]
  nlinarith

lemma tendsto_x : Tendsto (fun n : ℕ => 5 * (n : ℝ) * Real.log n) atTop atTop := by
  have h1 : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have h2 : Tendsto (fun n : ℕ => Real.log n) atTop atTop := Real.tendsto_log_atTop.comp h1
  have h3 := h1.atTop_mul_atTop₀ h2
  have h4 := h3.const_mul_atTop (show (0:ℝ) < 5 by norm_num)
  refine h4.congr fun n => ?_
  ring

lemma nth_le : ∀ᶠ n : ℕ in atTop, (Nat.nth Nat.Prime n : ℝ) ≤ 5 * n * Real.log n := by
  have hA := tendsto_x.eventually pi_lower
  have hB : ∀ᶠ n : ℕ in atTop, Real.log n ≤ 1 / 5 * n := by
    have := Real.isLittleO_log_id_atTop.bound (show (0 : ℝ) < 1 / 5 by norm_num)
    filter_upwards [tendsto_natCast_atTop_atTop.eventually this] with n hn
    simp only [id_eq, Real.norm_eq_abs] at hn
    have h0 : (0:ℝ) ≤ n := Nat.cast_nonneg n
    rw [abs_of_nonneg h0] at hn
    exact (le_abs_self _).trans hn
  filter_upwards [hA, hB, eventually_ge_atTop 4] with n hA hB hn4
  have hn : (4 : ℝ) ≤ n := by exact_mod_cast hn4
  have hlogn : 1 < Real.log n := by
    rw [Real.lt_log_iff_exp_lt (by linarith)]
    linarith [Real.exp_one_lt_d9]
  set x := 5 * (n : ℝ) * Real.log n with hxdef
  have hxpos : 0 < x := by positivity
  have hx2 : x ≤ (n : ℝ) ^ 2 := by
    rw [hxdef, sq]; nlinarith
  have hlogx : Real.log x ≤ 2 * Real.log n := by
    have := Real.log_le_log hxpos hx2
    rwa [Real.log_pow, Nat.cast_ofNat] at this
  have hlogxpos : 0 < Real.log x := Real.log_pos (by nlinarith)
  have hcount : (n : ℝ) + 1 ≤ (Nat.primeCounting ⌊x⌋₊ : ℝ) := by
    refine le_trans ?_ hA
    rw [le_div_iff₀ (by positivity)]
    have : 2 * Real.log x ≤ 4 * Real.log n := by linarith
    calc ((n:ℝ) + 1) * (2 * Real.log x) ≤ ((n:ℝ) + 1) * (4 * Real.log n) := by
          apply mul_le_mul_of_nonneg_left this; positivity
      _ ≤ x := by rw [hxdef]; nlinarith
  have hlt : n < Nat.count Nat.Prime (⌊x⌋₊ + 1) := by
    have : n + 1 ≤ Nat.primeCounting ⌊x⌋₊ := by exact_mod_cast hcount
    unfold Nat.primeCounting Nat.primeCounting' at this
    omega
  have := Nat.nth_lt_of_lt_count hlt
  have h3 : Nat.nth Nat.Prime n ≤ ⌊x⌋₊ := by omega
  calc (Nat.nth Nat.Prime n : ℝ) ≤ (⌊x⌋₊ : ℝ) := by exact_mod_cast h3
    _ ≤ x := Nat.floor_le hxpos.le

theorem sol : Tendsto (fun n : ℕ => log (Nat.nth Nat.Prime n : ℝ) / log n) atTop (𝓝 1) := by
  have hL : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hsmall : Tendsto (fun y : ℝ => (Real.log 5 + Real.log y) / y) atTop (𝓝 0) := by
    have a := (tendsto_const_nhds (x := Real.log 5)).div_atTop tendsto_id
    have b := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
    have := a.add b
    simp only [add_zero] at this
    refine this.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with y hy
    simp [add_div]
  have hup : Tendsto (fun n : ℕ => 1 + (Real.log 5 + Real.log (Real.log n)) / Real.log n) atTop (𝓝 1) := by
    simpa using (hsmall.comp hL).const_add 1
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
  · filter_upwards [eventually_ge_atTop 2] with n hn
    have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have hlog : 0 < Real.log n := Real.log_pos (by linarith)
    rw [le_div_iff₀ hlog, one_mul]
    apply Real.log_le_log (by linarith)
    have := Nat.add_two_le_nth_prime n
    exact_mod_cast (by omega : n ≤ Nat.nth Nat.Prime n)
  · filter_upwards [nth_le, eventually_ge_atTop 3] with n hp hn
    have hn' : (3 : ℝ) ≤ n := by exact_mod_cast hn
    have hlog : 1 < Real.log n := by
      rw [Real.lt_log_iff_exp_lt (by linarith)]
      linarith [Real.exp_one_lt_d9]
    have hppos : (0 : ℝ) < Nat.nth Nat.Prime n := by
      have := Nat.add_two_le_nth_prime n
      exact_mod_cast (by omega : 0 < Nat.nth Nat.Prime n)
    have h1 : Real.log (Nat.nth Nat.Prime n) ≤ Real.log (5 * n * Real.log n) :=
      Real.log_le_log hppos hp
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by norm_num) (by positivity)] at h1
    rw [div_le_iff₀ (by linarith), add_mul, one_mul, div_mul_cancel₀ _ (by linarith)]
    linarith

end OMA.P2bErdos5H2

theorem OMA.solution : OMA.R_Erdos5_erdos_5_variants_pintz_R1.H2 := by
  unfold OMA.R_Erdos5_erdos_5_variants_pintz_R1.H2
  exact OMA.P2bErdos5H2.sol
