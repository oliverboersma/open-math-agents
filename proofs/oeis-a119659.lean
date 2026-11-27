import OMAStatements.S_oeis_a119659
import Mathlib

/-!
Source: PrimeNumberTheoremAnd (https://github.com/AlexKontorovich/PrimeNumberTheoremAnd),
PrimeNumberTheoremAnd/IEANTN/Chebyshev.lean at commit
471f10c8164d59ed782680c5cd5d884e632e43c9, Apache-2.0.
Adaptation: remove blueprint metadata and external numerical log table imports,
and use only Mathlib's certified log estimates.
-/

namespace Chebyshev

open Real Finsupp Finset
open ArithmeticFunction hiding log

private lemma Ioc_eq_Icc (n : ℕ) : Ioc 0 n = Icc 1 n := by
  ext k
  simp
  omega

noncomputable def T (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, log n

theorem T.le (x : ℝ) (hx : 1 ≤ x) : T x ≤ x * log x - x + 1 + log x := by
  rw [T, ← Ico_insert_right <| Nat.one_le_iff_ne_zero.mpr (Nat.floor_pos.mpr hx).ne',
    sum_insert right_notMem_Ico]
  have : MonotoneOn log (Set.Icc (1 : ℕ) ⌊x⌋₊) :=
    fun a ha _ _ hab ↦ log_le_log (lt_of_lt_of_le one_pos (by grind)) hab
  have : ∑ n ∈ Finset.Ico 1 ⌊x⌋₊, log n ≤ ⌊x⌋₊ * log ⌊x⌋₊ - ⌊x⌋₊ + 1 :=
    calc ∑ n ∈ Finset.Ico 1 ⌊x⌋₊, log n
        ≤ ∫ t in (1 : ℕ)..(⌊x⌋₊ : ℕ), log t := this.sum_le_integral_Ico <|
          Nat.one_le_iff_ne_zero.mpr (Nat.floor_pos.mpr hx).ne'
      _ = ⌊x⌋₊ * log ⌊x⌋₊ - ⌊x⌋₊ + 1 := by simp
  have h1 : (1 : ℝ) ≤ ⌊x⌋₊ := by simp_all
  have h3 : ∀ t ∈ interior (Set.Ici 1), DifferentiableWithinAt ℝ (_root_.id * log - _root_.id) (interior (Set.Ici 1)) t := by
    intro t ht
    simp only [Set.nonempty_Iio, interior_Ici', Set.mem_Ioi] at ht
    have hd : DifferentiableAt ℝ (_root_.id * log - _root_.id) t := by
      fun_prop (disch := positivity)
    exact hd.differentiableWithinAt
  have h4 : ∀ t ∈ interior (Set.Ici 1), 0 ≤ deriv (fun t ↦ t * log t - t) t := by
    intro t ht
    simp only [Set.nonempty_Iio, interior_Ici', Set.mem_Ioi] at ht
    have : DifferentiableAt ℝ (fun t ↦ t * log t) t := by fun_prop ( disch := positivity )
    have hderiv : deriv (fun t ↦ t * log t - t) t = log t := by
      simp [show (fun t ↦ t * log t - t) = (fun t ↦ t * log t) - _root_.id by rfl,
        deriv_sub this differentiableAt_id, deriv_mul_log (by linarith)]
    exact hderiv ▸ log_nonneg (le_of_lt ht)
  have h5 : ContinuousOn (fun t ↦ t * log t - t) (Set.Ici 1) := by
    intro t ht
    have ht' : (1 : ℝ) ≤ t := ht
    have hd : DifferentiableAt ℝ (fun u ↦ u * log u - u) t := by
      fun_prop (disch := positivity)
    exact hd.continuousAt.continuousWithinAt
  have h2 : MonotoneOn (fun t ↦ t * log t - t) (Set.Ici 1) :=
    monotoneOn_of_deriv_nonneg (convex_Ici 1) h5 h3 h4
  have : (⌊x⌋₊ : ℝ) * log ⌊x⌋₊ - ⌊x⌋₊ ≤ x * log x - x := by
    exact h2 (Set.mem_Ici.mpr h1) (Set.mem_Ici.mpr hx) <| Nat.floor_le (by grind)
  linarith [log_le_log (by positivity) <| Nat.floor_le (by linarith)]

theorem T.ge (x : ℝ) (hx : 1 ≤ x) : T x ≥ x * log x - x + 1 - log x := by
  have hone_le_floor : 1 ≤ ⌊x⌋₊ := Nat.one_le_iff_ne_zero.mpr (Nat.floor_pos.mpr hx).ne'
  simp only [T, ← Ico_insert_right hone_le_floor, sum_insert right_notMem_Ico]
  have mono_log : MonotoneOn log (Set.Icc (1 : ℕ) ⌊x⌋₊) := fun a ha _ _ hab ↦
    log_le_log (lt_of_lt_of_le one_pos (by simpa using ha.1)) hab
  have h1 : ∀ n ≥ 1, ∑ i ∈ Ico 1 n, log (i + 1 : ℕ) = log n + ∑ i ∈ Ico 1 n, log i := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => simp
    | succ n hn ih => grind [Nat.Ico_succ_right_eq_insert_Ico]
  have sum_shift : ∑ i ∈ Ico 1 ⌊x⌋₊, log (i + 1 : ℕ) = log ⌊x⌋₊ + ∑ i ∈ Ico 1 ⌊x⌋₊, log i := by
    exact h1 ⌊x⌋₊ hone_le_floor
  have int_le_T : ∫ t in (1 : ℕ)..(⌊x⌋₊ : ℕ), log t ≤ log ⌊x⌋₊ + ∑ n ∈ Ico 1 ⌊x⌋₊, log n := by
    linarith [mono_log.integral_le_sum_Ico hone_le_floor]
  have int_eq : ∫ t in (1 : ℕ)..(⌊x⌋₊ : ℕ), log t = ⌊x⌋₊ * log ⌊x⌋₊ - ⌊x⌋₊ + 1 := by simp
  have h2 : ∫ t in (⌊x⌋₊ : ℝ)..x, log t ≤ (x - ⌊x⌋₊) * log x := by
    calc ∫ t in (⌊x⌋₊ : ℝ)..x, log t
      ≤ ∫ _ in (⌊x⌋₊ : ℝ)..x, log x := (intervalIntegral.integral_mono_on (Nat.floor_le <| by linarith) intervalIntegral.intervalIntegrable_log'
            intervalIntegrable_const fun t ht ↦ log_le_log (lt_of_lt_of_le (by positivity) ht.1) ht.2)
      _ = (x - ⌊x⌋₊) * log x := by simp
  have target_le_int : x * log x - x + 1 - log x ≤ ⌊x⌋₊ * log ⌊x⌋₊ - ⌊x⌋₊ + 1 := by
    calc x * log x - x + 1 - log x
        ≤ (x * log x - x + 1) - (x - ⌊x⌋₊) * log x := by nlinarith [log_nonneg hx, Nat.lt_floor_add_one x]
      _ ≤ (x * log x - x + 1) - ∫ t in (⌊x⌋₊ : ℝ)..x, log t := by grind
      _ = ⌊x⌋₊ * log ⌊x⌋₊ - ⌊x⌋₊ + 1 := by grind [integral_log]
  linarith

theorem T.eq_sum_Lambda (x : ℝ) : T x = ∑ n ∈ Icc 1 ⌊x⌋₊, Λ n * ⌊x / n⌋₊ := by
  unfold T
  simp_rw [← log_apply, ← vonMangoldt_mul_zeta]
  rw [← Ioc_eq_Icc, sum_Ioc_mul_zeta_eq_sum]
  simp [Nat.floor_div_natCast]

noncomputable def E (ν : ℕ →₀ ℝ) (x : ℝ) : ℝ := ν.sum (fun m w ↦ w * ⌊ x / m ⌋₊)

theorem T.weighted_eq_sum (ν : ℕ →₀ ℝ) (x : ℝ) : ν.sum (fun m w ↦ w * T (x/m)) = ∑ n ∈ Icc 1 ⌊x⌋₊, Λ n * E ν (x/n) := by
  simp_rw [T.eq_sum_Lambda, E, Finsupp.mul_sum]
  rw [← sum_finsetSum_comm]
  apply Finsupp.sum_congr fun y hy ↦ ?_
  rw [Finset.mul_sum]
  by_cases hy : y = 0
  · simp [hy]
  have one_le_y : 1 ≤ (y : ℝ) := by grind [Nat.one_le_cast]
  by_cases hx : x < 1
  · simp [hx, show x / y < 1 from div_lt_one (by linarith)|>.mpr (by linarith)]
  apply sum_subset_zero_on_sdiff
  · apply Icc_subset_Icc_right
    gcongr
    exact div_le_self (by linarith) one_le_y
  · intro t ht
    simp only [mem_sdiff, mem_Icc, not_and, not_le] at ht
    simp only [mul_eq_zero, Nat.cast_eq_zero, Nat.floor_eq_zero]
    right
    right
    apply div_lt_one (by linarith)|>.mpr
    have := ht.2 ht.1.1
    apply div_lt_iff₀ (by simp; grind)|>.mpr
    rw [Nat.floor_lt <| div_nonneg (by linarith) (by linarith)] at this
    have := div_lt_iff₀ (by linarith)|>.mp this
    rwa [mul_comm] at this
  · grind

open Finsupp in
noncomputable def ν : ℕ →₀ ℝ := single 1 1 - single 2 1 - single 3 1 - single 5 1 + single 30 1

/-- The support of `ν` is `{1, 2, 3, 5, 30}`. Used whenever we need to unfold `ν.sum`. -/
private lemma ν_support : ν.support = {1, 2, 3, 5, 30} := by
  norm_num [ν, Finset.ext_iff]; grind

/-- Unfold `ν.sum (fun m w ↦ w * f m)` into its five-term expansion.
This avoids repeating the `sum_add_index` / `sum_sub_index` chain every time
we need to compute a `ν`-weighted sum. -/
private lemma ν_sum_mul (f : ℕ → ℝ) :
    ν.sum (fun m w ↦ w * f m) = f 1 - f 2 - f 3 - f 5 + f 30 := by
  rw [ν, sum_add_index (by simp) (by intros; ring)]
  grind only [sum_single_index, sum_sub_index]

/-- Unfold `E ν y` into an explicit expression in terms of floors of `y / k`.
This is the key formula repeatedly used to analyse `E ν`. -/
private lemma E_nu_expand (y : ℝ) :
    E ν y = ⌊y⌋₊ - ⌊y / 2⌋₊ - ⌊y / 3⌋₊ - ⌊y / 5⌋₊ + ⌊y / 30⌋₊ := by
  rw [E, ν, sum_add_index' (by grind) (by grind)]
  grind [sum_single_index, sum_sub_index]

/-- The classical sandwich `k * ⌊y/k⌋₊ ≤ ⌊y⌋₊ < k * ⌊y/k⌋₊ + k` for `k ≥ 1` and `y ≥ 0`. -/
private lemma floor_div_bounds {y : ℝ} (hy : 0 ≤ y) {k : ℕ} (hk : 1 ≤ k) :
    k * ⌊y / k⌋₊ ≤ ⌊y⌋₊ ∧ ⌊y⌋₊ < k * ⌊y / k⌋₊ + k := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hdivnn : 0 ≤ y / k := div_nonneg hy hk'.le
  refine ⟨Nat.le_floor ?_, ?_⟩
  · push_cast
    have := Nat.floor_le hdivnn
    calc ((k : ℝ) * ⌊y / k⌋₊) = k * (y / k) - k * (y / k - ⌊y / k⌋₊) := by ring
      _ ≤ k * (y / k) := by nlinarith [Nat.floor_le hdivnn]
      _ = y := mul_div_cancel₀ _ hk'.ne'
  · have hlt : y / k < ⌊y / k⌋₊ + 1 := Nat.lt_floor_add_one (y / k)
    have hy_lt : y < (k : ℝ) * (⌊y / k⌋₊ + 1) := by linarith [(div_lt_iff₀ hk').mp hlt]
    have : (⌊y⌋₊ : ℝ) < (k : ℝ) * (⌊y / k⌋₊ + 1) := (Nat.floor_le hy).trans_lt hy_lt
    exact_mod_cast this

theorem nu_sum_div_eq_zero : ν.sum (fun n w ↦ w / n) = 0 := by
  norm_num [ν, add_div, sum_add_index', sub_div, sum_sub_index]

theorem E_nu_eq_one (x : ℝ) (hx : x ∈ Set.Ico 1 6) : E ν x = 1 := by
  obtain ⟨h1, h6⟩ := hx
  have hx0 : (0 : ℝ) ≤ x := by linarith
  simp only [E_nu_expand, Nat.floor_eq_zero.mpr (by linarith : x / 30 < 1)]
  have hflb : 1 ≤ ⌊x⌋₊ := by rwa [Nat.one_le_floor_iff]
  have hfub : ⌊x⌋₊ ≤ 5 := Nat.lt_succ_iff.mp (Nat.floor_lt' (by grind) |>.mpr h6)
  have h2 := floor_div_bounds hx0 (k := 2) (by norm_num)
  have h3 := floor_div_bounds hx0 (k := 3) (by norm_num)
  have h5 := floor_div_bounds hx0 (k := 5) (by norm_num)
  push_cast at h2 h3 h5
  rw [show ⌊x⌋₊ = ⌊x / 2⌋₊ + ⌊x / 3⌋₊ + ⌊x / 5⌋₊ + 1 by omega]
  grind

theorem E_nu_period (x : ℝ) (hx : x ≥ 0) : E ν (x + 30) = E ν x := by
  have h (k : ℝ) : (x + 30) / k = x / k + (30 / k) := by ring
  simp_rw [E_nu_expand, h 2, h 3, h 5, h 30]
  norm_num
  repeat rw [Nat.floor_add_ofNat (by positivity)]
  rw [Nat.floor_add_one (by positivity)]
  grind

theorem E_nu_bound (x : ℝ) (hx : x ≥ 0) : 0 ≤ E ν x ∧ E ν x ≤ 1 := by
  have : ∀ y, 0 ≤ y → y < 30 → 0 ≤ E ν y ∧ E ν y ≤ 1 := fun y hy0 hy30 ↦ by
    simp only [E_nu_expand, Nat.floor_eq_zero.mpr (by linarith : y / 30 < 1), Nat.cast_zero, add_zero]
    have h2 := floor_div_bounds hy0 (k := 2) (by norm_num)
    have h3 := floor_div_bounds hy0 (k := 3) (by norm_num)
    have h5 := floor_div_bounds hy0 (k := 5) (by norm_num)
    push_cast at h2 h3 h5
    have hfy : ⌊y⌋₊ < 30 := Nat.floor_lt' (by norm_num) |>.mpr (by exact_mod_cast hy30)
    have hlb : ⌊y/2⌋₊ + ⌊y/3⌋₊ + ⌊y/5⌋₊ ≤ ⌊y⌋₊ := by omega
    have hub : ⌊y⌋₊ ≤ ⌊y/2⌋₊ + ⌊y/3⌋₊ + ⌊y/5⌋₊ + 1 := by omega
    have hlb' : ((⌊y/2⌋₊ + ⌊y/3⌋₊ + ⌊y/5⌋₊ : ℕ) : ℝ) ≤ (⌊y⌋₊ : ℝ) := by exact_mod_cast hlb
    have hub' : ((⌊y⌋₊ : ℕ) : ℝ) ≤ ((⌊y/2⌋₊ + ⌊y/3⌋₊ + ⌊y/5⌋₊ + 1 : ℕ) : ℝ) := by exact_mod_cast hub
    push_cast at hlb' hub'
    refine ⟨by linarith, by linarith⟩
  let y := x - ⌊x / 30⌋₊ * 30
  have hy : 0 ≤ y ∧ y < 30 := ⟨by linarith [Nat.floor_le (by positivity : 0 ≤ x/30)], by
    linarith [Nat.lt_floor_add_one (x/30)]⟩
  have hxy : E ν x = E ν y := by
    have : x = y + ⌊x/30⌋₊ * 30 := by ring
    rw [this]; induction ⌊x/30⌋₊ with
    | zero => simp
    | succ n ih => simp [add_mul, ← add_assoc, E_nu_period _ (by linarith : y + n * 30 ≥ 0), ih]
  exact hxy ▸ this y hy.1 hy.2

noncomputable def U (x : ℝ) : ℝ := ν.sum (fun m w ↦ w * T (x/m))

theorem psi_ge_weighted (x : ℝ) (hx : x > 0) : ψ x ≥ U x := by
  unfold U psi
  rw [T.weighted_eq_sum, ← Ioc_eq_Icc]
  gcongr with i
  have := E_nu_bound (x / i) (div_nonneg hx.le (by simp))
  grw [this.2, mul_one]

theorem psi_diff_le_weighted (x : ℝ) (hx : x > 0) : ψ x - ψ (x / 6) ≤ U x := by
  unfold U psi
  rw [T.weighted_eq_sum, ← Ioc_eq_Icc]
  have subset : Ioc 0 ⌊x / 6⌋₊ ⊆ Ioc 0 ⌊x⌋₊ := by
    apply Ioc_subset_Ioc_right
    gcongr
    exact div_le_self hx.le (by norm_num)
  rw [← sum_sdiff_eq_sub subset, ← sum_sdiff subset]
  refine le_add_of_le_of_nonneg (sum_le_sum fun n hn ↦ ?_) (sum_nonneg fun n hn ↦ mul_nonneg vonMangoldt_nonneg ?_)
  · rw [E_nu_eq_one, mul_one]
    simp_all only [gt_iff_lt, Finset.mem_sdiff, Finset.mem_Ioc, not_and, not_le, Set.mem_Ico]
    refine ⟨one_le_div (by simp; grind)|>.mpr <| Nat.le_floor_iff hx.le |>.mp hn.1.2, ?_⟩
    have := hn.2 hn.1.1
    apply div_lt_iff₀ (by simp; grind)|>.mpr
    rw [Nat.floor_lt <| div_nonneg (by linarith) (by linarith)] at this
    have := div_lt_iff₀ (by linarith)|>.mp this
    rwa [mul_comm] at this
  · exact E_nu_bound _ (div_nonneg hx.le (by simp))|>.1

noncomputable def a : ℝ := - ν.sum (fun m w ↦ w * log m / m)

lemma a_simpl : a = (7/15) * Real.log 2 + (3/10) * Real.log 3 + (1/6) * Real.log 5 := by
  norm_num [a, Finsupp.sum, single_apply, ν_support]
  norm_num [Finset.sum, ν]
  grind [show (30 : ℝ) = 2 * 3 * 5 by ring, log_mul, log_mul]

theorem a_bound : a ∈ Set.Icc 0.92129 0.92130 := by
  norm_num [Chebyshev.a_simpl]
  constructor <;> nlinarith [Real.log_two_gt_d9, Real.log_two_lt_d9, Real.log_three_gt_d9, Real.log_three_lt_d9, Real.log_five_gt_d9, Real.log_five_lt_d9]

noncomputable def e (x : ℝ) : ℝ :=
  (T x - (x * log x - x + 1))

lemma U_bound.lemma_1 (x : ℝ) : T x = x * log x - x + 1 + (e x) := by
  unfold e
  ring

lemma U_bound.lemma_2 (x : ℝ) (hx : 1 ≤ x) : |e x| ≤ log x := by
  rw [abs_le]
  unfold e
  constructor <;> linarith [T.ge x hx, T.le x hx]

lemma U_bound.lemma_3 (x : ℝ) :
    U x = ν.sum (fun m w ↦ w * ((x / m) * (log (x / m))))
          - ν.sum (fun m w ↦ w * (x / m))
          + ν.sum (fun _m w ↦ w)
          + ν.sum (fun m w ↦ w * e (x / m)) := by
  simp [U, Finsupp.sum, U_bound.lemma_1, sub_eq_add_neg, add_mul, mul_comm, sum_add_distrib]

lemma U_bound.lemma_4 (x : ℝ) (hx : 0 < x) :
    ν.sum (fun m w ↦ w * ((x / m) * log (x / m))) = a * x := by
  have hx0 : x ≠ 0 := ne_of_gt hx
  have ha : a = -(log 1 / 1 - log 2 / 2 - log 3 / 3 - log 5 / 5 + log 30 / 30) := by
    simp_rw [a, mul_div_assoc]; rw [ν_sum_mul (fun m ↦ log m / m)]; push_cast; rfl
  rw [ν_sum_mul (fun m ↦ (x / m) * log (x / m)), ha]
  simp [Real.log_div hx0]
  ring

lemma U_bound.lemma_5 (x : ℝ) : ν.sum (fun m w ↦ w * (x / m)) = 0 := by
  rw [ν_sum_mul (fun m ↦ x / m)]; push_cast; ring

lemma U_bound.lemma_6 : ν.sum (fun _ w ↦ w) = (-1 : ℝ) := by
  have := ν_sum_mul (fun _ ↦ (1 : ℝ)); simp at this; linarith

lemma Finsupp.abs_sum_le (A : Type*) (ν : A →₀ ℝ) (g : A → ℝ → ℝ) : |ν.sum g| ≤ ν.sum |g| := by
  simp_rw [Finsupp.sum.eq_1]
  exact abs_sum_le_sum_abs (fun i ↦ g i (ν i)) ν.support

theorem U_bound (x : ℝ) (hx : 30 ≤ x) : |U x - a * x| ≤ 5 * log x - 5 := by
  have hxpos : 0 < x := lt_of_lt_of_le (by norm_num) hx
  rw [U_bound.lemma_3, U_bound.lemma_4 x hxpos]
  ring_nf
  have hlin : ν.sum (fun m w ↦ x * w * (↑m)⁻¹) = 0 :=
    by simpa [div_eq_mul_inv, mul_assoc, mul_left_comm] using U_bound.lemma_5 x
  rw [hlin]; ring_nf; rw [U_bound.lemma_6]
  grw [abs_add_le, Finsupp.abs_sum_le]
  norm_num
  have hsupp_eq : ν.support = {1, 2, 3, 5, 30} := ν_support
  have hmem_of_supp : ∀ i ∈ ν.support, 0 < i ∧ i ≤ 30 := fun i hi ↦ by
    have : i ∈ ({1, 2, 3, 5, 30} : Finset ℕ) := hsupp_eq ▸ hi
    simp only [mem_insert, mem_singleton] at this
    constructor <;> omega
  have h : ν.sum |fun m w ↦ w * e (x * (↑m)⁻¹)| ≤ ν.sum (fun m w ↦ |w| * log (x * (↑m)⁻¹)) := by
    apply Finsupp.sum_le_sum
    intro i hi
    simp only [Pi.abs_apply, abs_mul]
    obtain ⟨hi_pos, hi_le⟩ := hmem_of_supp i hi
    have hxi : 1 ≤ x * (↑i)⁻¹ := by
      rw [le_mul_inv_iff₀ (by exact_mod_cast hi_pos)]
      linarith [show (i : ℝ) ≤ 30 from by exact_mod_cast hi_le]
    gcongr; exact U_bound.lemma_2 _ hxi
  grw [h]
  have hlog_split : ν.sum (fun m w ↦ |w| * log (x * (m : ℝ)⁻¹)) =
      log x * ν.sum (fun m w ↦ |w|) - ν.sum (fun m w ↦ |w| * log (↑m : ℝ)) := by
    simp only [Finsupp.sum]
    conv_rhs => rw [Finset.mul_sum, ← sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro m hm
    have hm_pos : (0 : ℝ) < m := by exact_mod_cast (hmem_of_supp m hm).1
    rw [← div_eq_mul_inv, Real.log_div (ne_of_gt hxpos) (ne_of_gt hm_pos)]; ring
  rw [hlog_split]
  -- Once the support of `ν` is known explicitly, both `habs` and `hsum_eq`
  -- reduce to concrete arithmetic over a five-element finset.
  have expand_sum : ∀ f : ℕ → ℝ → ℝ, (∀ n, f n 0 = 0) →
      ν.sum f = f 1 1 + f 2 (-1) + f 3 (-1) + f 5 (-1) + f 30 1 := by
    intro f hf
    rw [Finsupp.sum_of_support_subset _ hsupp_eq.le _ (by intros; simp [hf])]
    simp only [sum_insert (by decide : (1:ℕ) ∉ ({2,3,5,30} : Finset ℕ)),
               sum_insert (by decide : (2:ℕ) ∉ ({3,5,30} : Finset ℕ)),
               sum_insert (by decide : (3:ℕ) ∉ ({5,30} : Finset ℕ)),
               sum_insert (by decide : (5:ℕ) ∉ ({30} : Finset ℕ)),
               sum_singleton, ν, Finsupp.sub_apply, Finsupp.add_apply, Finsupp.single_apply]
    norm_num
    ring
  have habs : ν.sum (fun m w ↦ |w|) = 5 := by
    rw [expand_sum _ (by intros; simp)]; norm_num
  have hgeq6 : ν.sum (fun m w ↦ |w| * log m) ≥ 6 := by
    have hsum_eq : ν.sum (fun m w ↦ |w| * log (m : ℝ)) = log 2 + log 3 + log 5 + log 30 := by
      rw [expand_sum _ (by intros; simp)]
      simp [log_one]
    have hlog30 : log (30 : ℝ) = log 2 + log 3 + log 5 := by
      rw [show (30 : ℝ) = 2 * 3 * 5 by norm_num, Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num)]
    linarith [Real.log_two_gt_d9, Real.log_three_gt_d9, Real.log_five_gt_d9]
  grw [hgeq6]; rw [habs]; linarith

theorem psi_lower (x : ℝ) (hx : 30 ≤ x) : ψ x ≥ a * x - 5 * log x + 5 := by
  have h2 := abs_sub_le_iff.mp (U_bound x hx)
  linarith [psi_ge_weighted x (by linarith), h2.1]

theorem psi_diff_upper (x : ℝ) (hx : 30 ≤ x) : ψ x - ψ (x / 6) ≤ a * x + 5 * log x - 5 := by
  have h2 := abs_sub_le_iff.mp (U_bound x hx)
  linarith [psi_diff_le_weighted x (by linarith), h2.2]

/- Elementary coarse explicit upper bound, avoiding finite computations and any
extra numerical log tables. -/
theorem log_four_add_four_le : Real.log 4 + 4 ≤ (5.5 : ℝ) := by
  rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
  norm_num
  linarith [Real.log_two_lt_d9]

theorem psi_coarse_upper_nat (n : ℕ) (hn : 1 ≤ n) :
    ψ (n : ℝ) ≤ (6*a/5) * n + 5 * (Real.log n)^2 + 165 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    have ha : 0 ≤ a := by linarith [a_bound.1]
    have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
    by_cases hsmall : n < 30
    · have hpsi := psi_le_const_mul_self (x := (n : ℝ)) (by positivity)
      have hmult := mul_le_mul_of_nonneg_right log_four_add_four_le (show (0 : ℝ) ≤ n by positivity)
      have hnn : (n : ℝ) ≤ 30 := by exact_mod_cast hsmall.le
      nlinarith [sq_nonneg (Real.log n), mul_nonneg ha (show (0 : ℝ) ≤ n by positivity)]
    · let m := ⌊(n : ℝ)/6⌋₊
      have hn30 : (30 : ℝ) ≤ n := by exact_mod_cast Nat.le_of_not_gt hsmall
      have hmR : (m : ℝ) ≤ n / 6 := Nat.floor_le (by positivity)
      have hm1 : 1 ≤ m := (Nat.one_le_floor_iff _).mpr (by linarith)
      have hm1R : (1 : ℝ) ≤ m := by exact_mod_cast hm1
      have hmn : m < n := by
        have : (m : ℝ) < n := by linarith
        exact_mod_cast this
      have hm_log : log m ≤ log ((n : ℝ)/6) := log_le_log (by positivity) hmR
      have hm_log0 : 0 ≤ log m := log_nonneg hm1R
      have hlog6 : 1 ≤ log 6 := by
        rw [show (6 : ℝ) = 2 * 3 by norm_num, log_mul (by norm_num) (by norm_num)]
        linarith [log_two_gt_d9, log_three_gt_d9]
      have hlogn : log (n : ℝ) ≥ log 6 := log_le_log (by norm_num) (by linarith)
      have hlogdiv : log ((n : ℝ)/6) = log n - log 6 := Real.log_div (by positivity) (by norm_num)
      have hlogdiff : 5 * (log m)^2 + 5 * log n - 5 ≤ 5 * (log n)^2 := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hm_log) (show 0 ≤ log ((n:ℝ)/6) + log m by linarith),
          mul_nonneg (sub_nonneg.mpr hlogn) (sub_nonneg.mpr hlog6),
          mul_nonneg (sub_nonneg.mpr hlog6) (show 0 ≤ log n by linarith),
          sq_nonneg (log 6 - 1)]
      have hs := psi_diff_upper (n : ℝ) hn30
      rw [psi_eq_psi_coe_floor ((n : ℝ)/6)] at hs
      change ψ (n : ℝ) - ψ (m : ℝ) ≤ _ at hs
      have ih' := ih m hmn hm1
      nlinarith [mul_le_mul_of_nonneg_right hmR ha]

theorem psi_coarse_upper (x : ℝ) (hx : 1 ≤ x) :
    ψ x ≤ (6*a/5) * x + 5 * (Real.log x)^2 + 165 := by
  let n := ⌊x⌋₊
  have hn : 1 ≤ n := (Nat.one_le_floor_iff _).mpr hx
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnx : (n : ℝ) ≤ x := Nat.floor_le (by linarith)
  have hlog := Real.log_le_log (show (0 : ℝ) < n by linarith) hnx
  have ha : 0 ≤ a := by linarith [a_bound.1]
  rw [psi_eq_psi_coe_floor x]
  change ψ (n : ℝ) ≤ _
  nlinarith [psi_coarse_upper_nat n hn, mul_le_mul_of_nonneg_right hnx ha,
    mul_nonneg (sub_nonneg.mpr hlog) (add_nonneg (Real.log_nonneg hx) (Real.log_nonneg hnR))]

theorem log_le_sqrt_scaled (x : ℝ) (hx : (262144 : ℝ) ≤ x) :
    Real.log x ≤ (13.5 / 512) * Real.sqrt x := by
  have hx0 : 0 ≤ x := by linarith
  have hs : (512 : ℝ) ≤ Real.sqrt x := by
    calc (512 : ℝ) = Real.sqrt 262144 := by norm_num
      _ ≤ Real.sqrt x := Real.sqrt_le_sqrt hx
  have hs0 : 0 < Real.sqrt x := by linarith
  have hlog512 : Real.log 512 ≤ 6.75 := by
    rw [show (512 : ℝ) = 2 ^ (9 : ℕ) by norm_num, Real.log_pow]
    norm_num
    linarith [Real.log_two_lt_d9]
  have hlog := Real.log_le_sub_one_of_pos (show 0 < Real.sqrt x / 512 by positivity)
  rw [Real.log_div (by positivity) (by norm_num), Real.log_sqrt hx0] at hlog
  linarith

theorem sqrt_threshold (x : ℝ) (hx : (262144 : ℝ) ≤ x) :
    (512 : ℝ) ≤ Real.sqrt x := by
  calc (512 : ℝ) = Real.sqrt 262144 := by norm_num
    _ ≤ Real.sqrt x := Real.sqrt_le_sqrt hx

theorem psi_explicit_upper_large (x : ℝ) (hx : (262144 : ℝ) ≤ x) :
    ψ x ≤ (1.11 : ℝ) * x := by
  have hx0 : 0 ≤ x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hlog := log_le_sqrt_scaled x hx
  have hlog0 := Real.log_nonneg hx1
  have hs0 := Real.sqrt_nonneg x
  have hsq := Real.sq_sqrt hx0
  have hsqlog : (Real.log x)^2 ≤ (13.5/512 : ℝ)^2 * x := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hlog) (show 0 ≤ (13.5/512 : ℝ) * Real.sqrt x + Real.log x by positivity)]
  have hax := mul_le_mul_of_nonneg_right a_bound.2 hx0
  nlinarith [psi_coarse_upper x hx1]

theorem rpow_third_le_sqrt_quarter (x : ℝ) (hx : (262144 : ℝ) ≤ x) :
    x ^ (3 : ℝ)⁻¹ ≤ Real.sqrt x / 4 := by
  have hx0 : 0 ≤ x := by linarith
  have hxpos : 0 < x := by linarith
  have hbase : (4 : ℝ) ≤ x ^ ((6 : ℝ)⁻¹) := by
    have hpow : ((4 : ℝ) ^ (6 : ℕ)) ^ ((6 : ℝ)⁻¹) = 4 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
      norm_num
    rw [← hpow]
    exact Real.rpow_le_rpow (by positivity) (by norm_num; linarith) (by norm_num)
  have hmul := mul_le_mul_of_nonneg_left hbase (Real.rpow_nonneg hx0 ((3 : ℝ)⁻¹))
  rw [← Real.rpow_add hxpos, show (3 : ℝ)⁻¹ + (6 : ℝ)⁻¹ = 1/2 by norm_num,
    ← Real.sqrt_eq_rpow] at hmul
  linarith

theorem theta_explicit_lower_large (x : ℝ) (hx : (262144 : ℝ) ≤ x) :
    (0.9 : ℝ) * x ≤ θ x := by
  have hx0 : 0 ≤ x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hlog := log_le_sqrt_scaled x hx
  have hlog0 := Real.log_nonneg hx1
  have hs := sqrt_threshold x hx
  have hsq := Real.sq_sqrt hx0
  have hpow3 := rpow_third_le_sqrt_quarter x hx
  have hpow5 : x ^ (5 : ℝ)⁻¹ ≤ Real.sqrt x / 4 :=
    (Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num : (5 : ℝ)⁻¹ ≤ (3 : ℝ)⁻¹)).trans hpow3
  have hpow2 : x ^ (2 : ℝ)⁻¹ = Real.sqrt x := by rw [Real.sqrt_eq_rpow]; norm_num
  have hψ2 : ψ (x ^ (2 : ℝ)⁻¹) ≤ 5.5 * Real.sqrt x := by
    rw [hpow2]
    exact (psi_le_const_mul_self (Real.sqrt_nonneg x)).trans
      (mul_le_mul_of_nonneg_right log_four_add_four_le (Real.sqrt_nonneg x))
  have hψ3 : ψ (x ^ (3 : ℝ)⁻¹) ≤ 5.5 * (Real.sqrt x / 4) := by
    have hn := Real.rpow_nonneg hx0 ((3 : ℝ)⁻¹)
    exact (psi_le_const_mul_self hn).trans ((mul_le_mul_of_nonneg_right log_four_add_four_le hn).trans
      (mul_le_mul_of_nonneg_left hpow3 (by norm_num)))
  have hψ5 : ψ (x ^ (5 : ℝ)⁻¹) ≤ 5.5 * (Real.sqrt x / 4) := by
    have hn := Real.rpow_nonneg hx0 ((5 : ℝ)⁻¹)
    exact (psi_le_const_mul_self hn).trans ((mul_le_mul_of_nonneg_right log_four_add_four_le hn).trans
      (mul_le_mul_of_nonneg_left hpow5 (by norm_num)))
  have hψlower := psi_lower x (by linarith)
  have ha := mul_le_mul_of_nonneg_right a_bound.1 hx0
  have hθ := psi_sub_theta_le_psi_add_psi_add_psi x
  nlinarith [mul_nonneg (sub_nonneg.mpr hs) (Real.sqrt_nonneg x)]

theorem theta_explicit_upper_large (x : ℝ) (hx : (262144 : ℝ) ≤ x) :
    θ x ≤ (1.11 : ℝ) * x := (theta_le_psi x).trans (psi_explicit_upper_large x hx)

end Chebyshev


open scoped BigOperators

namespace PrimeIntervalBridge

theorem theta_interval_le (x y : ℝ) (hxy : x ≤ y) (hy : 0 ≤ y) :
    Chebyshev.theta y - Chebyshev.theta x ≤
      ((Nat.primeCounting ⌊y⌋₊ : ℝ) - (Nat.primeCounting ⌊x⌋₊ : ℝ)) * Real.log y := by
  let s := (⌊x⌋₊ : ℕ).primesLE
  let t := (⌊y⌋₊ : ℕ).primesLE
  have hsub : s ⊆ t := Nat.primesLE_mono (Nat.floor_mono hxy)
  have hcardle : s.card ≤ t.card := Finset.card_le_card hsub
  have hcard : (t \ s).card = t.card - s.card := by
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hsub]
  have hsum : Chebyshev.theta y - Chebyshev.theta x = ∑ p ∈ t \ s, Real.log (p : ℝ) := by
    rw [Chebyshev.theta_eq_sum_primesLE, Chebyshev.theta_eq_sum_primesLE]
    change (∑ p ∈ t, Real.log (p : ℝ)) - (∑ p ∈ s, Real.log (p : ℝ)) = _
    linarith [Finset.sum_sdiff (f := fun p : ℕ => Real.log (p : ℝ)) hsub]
  have hbound : ∑ p ∈ t \ s, Real.log (p : ℝ) ≤ ∑ _p ∈ t \ s, Real.log y := by
    apply Finset.sum_le_sum
    intro p hp
    have hpt : p ∈ t := (Finset.mem_sdiff.mp hp).1
    have hmem : p ≤ ⌊y⌋₊ ∧ p.Prime := Nat.mem_primesLE.mp hpt
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hmem.2.pos
    have hpy : (p : ℝ) ≤ y := (Nat.cast_le.mpr hmem.1).trans (Nat.floor_le hy)
    exact Real.log_le_log hp0 hpy
  rw [hsum]
  calc
    _ ≤ ∑ _p ∈ t \ s, Real.log y := hbound
    _ = (↑((t \ s).card) : ℝ) * Real.log y := by simp [nsmul_eq_mul]
    _ = _ := by
      rw [hcard, Nat.cast_sub hcardle]
      simp only [s, t, Nat.primesLE_card_eq_primeCounting]

theorem primeCounting_le_theta_split (y : ℝ) (hy : 1 < y) :
    (Nat.primeCounting ⌊y⌋₊ : ℝ) ≤ 2 * Chebyshev.theta y / Real.log y + Real.sqrt y := by
  have hy0 : 0 ≤ y := by linarith
  have hlog : 0 < Real.log y := Real.log_pos hy
  have hsqrt : Real.sqrt y ≤ y := (Real.sqrt_le_iff).mpr ⟨hy0, by nlinarith⟩
  let s := (⌊Real.sqrt y⌋₊ : ℕ).primesLE
  let t := (⌊y⌋₊ : ℕ).primesLE
  have hsub : s ⊆ t := Nat.primesLE_mono (Nat.floor_mono hsqrt)
  have hcardle : s.card ≤ t.card := Finset.card_le_card hsub
  have hcard : (t \ s).card = t.card - s.card := by
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hsub]
  have hs_bound : (s.card : ℝ) ≤ Real.sqrt y := by
    have h : s.card ≤ ⌊Real.sqrt y⌋₊ := by
      dsimp [s]
      rw [Nat.primesLE_eq_filter_Icc_one]
      have hc := Finset.card_filter_le (Finset.Icc 1 ⌊Real.sqrt y⌋₊) Nat.Prime
      rw [Nat.card_Icc] at hc
      omega
    exact (Nat.cast_le.mpr h).trans (Nat.floor_le (Real.sqrt_nonneg y))
  have hsum_lower : (↑((t \ s).card) : ℝ) * (Real.log y / 2) ≤ Chebyshev.theta y := by
    have h1 : ∑ _p ∈ t \ s, Real.log (Real.sqrt y) ≤ ∑ p ∈ t \ s, Real.log (p : ℝ) := by
      apply Finset.sum_le_sum
      intro p hp
      have hpt : p ∈ t := (Finset.mem_sdiff.mp hp).1
      have hps : p ∉ s := (Finset.mem_sdiff.mp hp).2
      have hpprime : p.Prime := (Nat.mem_primesLE.mp hpt).2
      have hlt : ⌊Real.sqrt y⌋₊ < p := by
        by_contra h
        have hh : p ≤ ⌊Real.sqrt y⌋₊ := by omega
        exact hps (Nat.mem_primesLE.mpr ⟨hh, hpprime⟩)
      exact Real.log_le_log (Real.sqrt_pos.mpr (by linarith)) (Nat.lt_of_floor_lt hlt).le
    have h2 : ∑ p ∈ t \ s, Real.log (p : ℝ) ≤ Chebyshev.theta y := by
      have hsum := Finset.sum_sdiff (f := fun p : ℕ => Real.log (p : ℝ)) hsub
      rw [Chebyshev.theta_eq_sum_primesLE] at *
      have hs0 : 0 ≤ ∑ p ∈ s, Real.log (p : ℝ) := by
        apply Finset.sum_nonneg
        intro p hp
        exact Real.log_nonneg (by exact_mod_cast (Nat.mem_primesLE.mp hp).2.one_lt.le)
      linarith
    calc
      _ = ∑ _p ∈ t \ s, Real.log (Real.sqrt y) := by rw [Real.log_sqrt hy0]; simp [nsmul_eq_mul]
      _ ≤ ∑ p ∈ t \ s, Real.log (p : ℝ) := h1
      _ ≤ _ := h2
  have hdiv : (↑((t \ s).card) : ℝ) ≤ 2 * Chebyshev.theta y / Real.log y := by
    apply (le_div_iff₀ hlog).mpr
    linarith
  rw [hcard, Nat.cast_sub hcardle] at hdiv
  have htc : (t.card : ℝ) = Nat.primeCounting ⌊y⌋₊ := by simp [t, Nat.primesLE_card_eq_primeCounting]
  linarith

theorem primeCounting_le_theta_split_rpow (y α : ℝ) (hy : 1 < y)
    (ha : 0 < α) (ha1 : α ≤ 1) :
    (Nat.primeCounting ⌊y⌋₊ : ℝ) ≤ Chebyshev.theta y / (α * Real.log y) + y ^ α := by
  have hy0 : 0 ≤ y := by linarith
  have hypos : 0 < y := by linarith
  have hlog : 0 < Real.log y := Real.log_pos hy
  have hden : 0 < α * Real.log y := mul_pos ha hlog
  have hpow : y ^ α ≤ y := by
    calc
      y ^ α ≤ y ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hy.le ha1
      _ = y := Real.rpow_one y
  let s := (⌊y ^ α⌋₊ : ℕ).primesLE
  let t := (⌊y⌋₊ : ℕ).primesLE
  have hsub : s ⊆ t := Nat.primesLE_mono (Nat.floor_mono hpow)
  have hcardle : s.card ≤ t.card := Finset.card_le_card hsub
  have hcard : (t \ s).card = t.card - s.card := by
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hsub]
  have hs_bound : (s.card : ℝ) ≤ y ^ α := by
    have h : s.card ≤ ⌊y ^ α⌋₊ := by
      dsimp [s]
      rw [Nat.primesLE_eq_filter_Icc_one]
      have hc := Finset.card_filter_le (Finset.Icc 1 ⌊y ^ α⌋₊) Nat.Prime
      rw [Nat.card_Icc] at hc
      omega
    exact (Nat.cast_le.mpr h).trans (Nat.floor_le (Real.rpow_nonneg hy0 α))
  have hsum_lower : (↑((t \ s).card) : ℝ) * (α * Real.log y) ≤ Chebyshev.theta y := by
    have h1 : ∑ _p ∈ t \ s, Real.log (y ^ α) ≤ ∑ p ∈ t \ s, Real.log (p : ℝ) := by
      apply Finset.sum_le_sum
      intro p hp
      have hpt : p ∈ t := (Finset.mem_sdiff.mp hp).1
      have hps : p ∉ s := (Finset.mem_sdiff.mp hp).2
      have hpprime : p.Prime := (Nat.mem_primesLE.mp hpt).2
      have hlt : ⌊y ^ α⌋₊ < p := by
        by_contra h
        have hh : p ≤ ⌊y ^ α⌋₊ := by omega
        exact hps (Nat.mem_primesLE.mpr ⟨hh, hpprime⟩)
      exact Real.log_le_log (Real.rpow_pos_of_pos hypos α) (Nat.lt_of_floor_lt hlt).le
    have h2 : ∑ p ∈ t \ s, Real.log (p : ℝ) ≤ Chebyshev.theta y := by
      have hsum := Finset.sum_sdiff (f := fun p : ℕ => Real.log (p : ℝ)) hsub
      rw [Chebyshev.theta_eq_sum_primesLE] at *
      have hs0 : 0 ≤ ∑ p ∈ s, Real.log (p : ℝ) := by
        apply Finset.sum_nonneg
        intro p hp
        exact Real.log_nonneg (by exact_mod_cast (Nat.mem_primesLE.mp hp).2.one_lt.le)
      linarith
    calc
      _ = ∑ _p ∈ t \ s, Real.log (y ^ α) := by rw [Real.log_rpow hypos]; simp [nsmul_eq_mul]
      _ ≤ ∑ p ∈ t \ s, Real.log (p : ℝ) := h1
      _ ≤ _ := h2
  have hdiv : (↑((t \ s).card) : ℝ) ≤ Chebyshev.theta y / (α * Real.log y) := by
    exact (le_div_iff₀ hden).mpr hsum_lower
  rw [hcard, Nat.cast_sub hcardle] at hdiv
  have htc : (t.card : ℝ) = Nat.primeCounting ⌊y⌋₊ := by simp [t, Nat.primesLE_card_eq_primeCounting]
  linarith

theorem primeCounting_le_theta_split_two_thirds (y : ℝ) (hy : 1 < y) :
    (Nat.primeCounting ⌊y⌋₊ : ℝ) ≤ (3/2) * Chebyshev.theta y / Real.log y + y ^ (2/3 : ℝ) := by
  have h := primeCounting_le_theta_split_rpow y (2/3) hy (by norm_num) (by norm_num)
  have hr : Chebyshev.theta y / ((2/3) * Real.log y) = (3/2) * Chebyshev.theta y / Real.log y := by
    field_simp [ne_of_gt (Real.log_pos hy)]
  rw [hr] at h
  exact h

theorem two_primes_imply_count_gap (x y p q : ℕ)
    (hp : p.Prime) (hq : q.Prime) (hxp : x < p) (hpq : p < q) (hqy : q ≤ y) :
    Nat.primeCounting x + 2 ≤ Nat.primeCounting y := by
  have hxy : x ≤ y := by omega
  have hsub : x.primesLE ⊆ y.primesLE := Nat.primesLE_mono hxy
  have hpair : ({p,q} : Finset ℕ) ⊆ y.primesLE \ x.primesLE := by
    intro n hn
    simp only [Finset.mem_insert, Finset.mem_singleton] at hn
    rcases hn with rfl | rfl
    · exact Finset.mem_sdiff.mpr ⟨Nat.mem_primesLE.mpr ⟨by omega, hp⟩,
        fun h => (not_le_of_gt hxp) (Nat.mem_primesLE.mp h).1⟩
    · exact Finset.mem_sdiff.mpr ⟨Nat.mem_primesLE.mpr ⟨hqy, hq⟩,
        fun h => (not_le_of_gt (hxp.trans hpq)) (Nat.mem_primesLE.mp h).1⟩
  have hcard := Finset.card_le_card hpair
  have hne : p ≠ q := Nat.ne_of_lt hpq
  rw [Finset.card_pair hne, Finset.card_sdiff, Finset.inter_eq_left.mpr hsub,
    Nat.primesLE_card_eq_primeCounting, Nat.primesLE_card_eq_primeCounting] at hcard
  omega

end PrimeIntervalBridge


namespace Chebyshev

open Real

theorem log_threshold_lower (x : ℝ) (hx : (262144 : ℝ) ≤ x) :
    (12 : ℝ) ≤ log x := by
  have hlog := Real.log_le_log (show (0 : ℝ) < 262144 by norm_num) hx
  rw [show (262144 : ℝ) = 2 ^ (18 : ℕ) by norm_num, Real.log_pow] at hlog
  norm_num at hlog
  linarith [Real.log_two_gt_d9]

theorem log_scaled_le (x c : ℝ) (hx : 0 < x) (hc : 0 < c) (hc2 : c ≤ 2) :
    log (c * x) ≤ log x + (0.75 : ℝ) := by
  rw [Real.log_mul (ne_of_gt hc) (ne_of_gt hx)]
  linarith [Real.log_le_log hc hc2, Real.log_two_lt_d9]

theorem theta_count_gap_of_bridge (x : ℝ) (hx : (262144 : ℝ) ≤ x) (p q : ℕ)
    (hbridge : θ (5*x/4) - θ x ≤ ((q : ℝ) - p) * log (5*x/4)) :
    p + 2 ≤ q := by
  have hz : (262144 : ℝ) ≤ 5*x/4 := by linarith
  have hθL := theta_explicit_lower_large (5*x/4) hz
  have hθU := theta_explicit_upper_large x hx
  have hlog_scaled : log (5*x/4) ≤ log x + 0.75 := by
    convert log_scaled_le x (5/4) (by linarith) (by norm_num) (by norm_num) using 1
    ring_nf
  have hlog := log_le_sqrt_scaled x hx
  have hs := sqrt_threshold x hx
  have hs0 := Real.sqrt_nonneg x
  have hsq := Real.sq_sqrt (show 0 ≤ x by linarith)
  have hlog0 : 0 ≤ log (5*x/4) := Real.log_nonneg (by linarith)
  have hdom : log (5*x/4) < 0.015*x := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hs) hs0]
  by_contra! hbad
  have hbad' : ((q : ℝ) - p) ≤ 1 := by
    have hh : q ≤ p + 1 := by omega
    have hh' : (q : ℝ) ≤ (p : ℝ) + 1 := by exact_mod_cast hh
    linarith
  have hm := mul_le_mul_of_nonneg_right hbad' hlog0
  linarith

theorem theta_count_ratio_of_bridge (x : ℝ) (hx : (262144 : ℝ) ≤ x) (p q : ℕ)
    (hbridge : θ (48*x/25) - θ x ≤ ((q : ℝ) - p) * log (48*x/25))
    (hsplit : (p : ℝ) * log x ≤ 2 * θ x + Real.sqrt x * log x) :
    5 * p < 4 * q := by
  have hz : (262144 : ℝ) ≤ 48*x/25 := by linarith
  have hθL := theta_explicit_lower_large (48*x/25) hz
  have hθU := theta_explicit_upper_large x hx
  have hlogX := log_threshold_lower x hx
  have hlog0 : 0 < log x := by linarith
  have hlogZ : 0 < log (48*x/25) := by linarith [log_threshold_lower (48*x/25) hz]
  have hlog_scaled : log (48*x/25) ≤ log x + 0.75 := by
    convert log_scaled_le x (48/25) (by linarith) (by norm_num) (by norm_num) using 1
    ring_nf
  have hlogratio : log (48*x/25) ≤ (17/16)* log x := by linarith
  have hlog := log_le_sqrt_scaled x hx
  have hs0 := Real.sqrt_nonneg x
  have hsq := Real.sq_sqrt (show 0 ≤ x by linarith)
  have hslog : Real.sqrt x * log x ≤ (13.5/512)*x := by
    nlinarith [mul_le_mul_of_nonneg_left hlog hs0]
  have hd : (0 : ℝ) ≤ (q : ℝ) - p := by
    by_contra! hneg
    have hm := mul_neg_of_neg_of_pos hneg hlogZ
    linarith
  have hD := mul_le_mul_of_nonneg_left hlogratio hd
  have hfinal : (p : ℝ) * log x < 4*((q : ℝ)-p)*log x := by
    nlinarith
  have hfinal' : (p : ℝ) < 4*((q : ℝ)-p) := by
    by_contra! hn
    have hm := mul_le_mul_of_nonneg_right hn hlog0.le
    linarith
  exact_mod_cast (show (5 : ℝ) * p < 4 * (q : ℝ) by linarith)

theorem primeCounting_gap_large (x : ℝ) (hx : (262144 : ℝ) ≤ x) :
    Nat.primeCounting ⌊x⌋₊ + 2 ≤ Nat.primeCounting ⌊5*x/4⌋₊ := by
  apply theta_count_gap_of_bridge x hx
  exact PrimeIntervalBridge.theta_interval_le x (5*x/4) (by linarith) (by linarith)

theorem primeCounting_ratio_large (x : ℝ) (hx : (262144 : ℝ) ≤ x) :
    5 * Nat.primeCounting ⌊x⌋₊ < 4 * Nat.primeCounting ⌊48*x/25⌋₊ := by
  apply theta_count_ratio_of_bridge x hx
  · exact PrimeIntervalBridge.theta_interval_le x (48*x/25) (by linarith) (by linarith)
  · have hlog : 0 < Real.log x := by linarith [log_threshold_lower x hx]
    calc (Nat.primeCounting ⌊x⌋₊ : ℝ) * Real.log x
        ≤ (2 * θ x / Real.log x + Real.sqrt x) * Real.log x := by
          exact mul_le_mul_of_nonneg_right
            (PrimeIntervalBridge.primeCounting_le_theta_split x (by linarith)) hlog.le
      _ = 2 * θ x + Real.sqrt x * Real.log x := by field_simp

end Chebyshev


namespace Chebyshev

open Real Finset ArithmeticFunction

set_option maxHeartbeats 4000000 in
theorem psi_le_double_small (n : ℕ) (hn : n ≤ 30) : ψ (n : ℝ) ≤ 2 * n := by
  have hmono : Monotone psi := psi_mono
  have hnum : ψ (9 : ℝ) ≤ 10 ∧ ψ (17 : ℝ) ≤ 20 ∧ ψ (30 : ℝ) ≤ 36 := by
    have primes : Λ 2 = Real.log 2 ∧ Λ 3 = Real.log 3 ∧ Λ 5 = Real.log 5 ∧ Λ 7 = Real.log 7 ∧ Λ 11 = Real.log 11 ∧ Λ 13 = Real.log 13 ∧ Λ 17 = Real.log 17 ∧ Λ 19 = Real.log 19 ∧ Λ 23 = Real.log 23 ∧ Λ 29 = Real.log 29 := by
      split_ands <;> exact vonMangoldt_apply_prime (by decide)
    have lam_pow : (Λ (2 ^ 2) = Real.log 2) ∧ Λ (2 ^ 3) = Real.log 2 ∧ Λ (2 ^ 4) = Real.log 2 ∧ Λ (3 ^ 2) = Real.log 3 ∧ Λ (3 ^ 3) = Real.log 3 ∧ Λ (5 ^ 2) = Real.log 5 := by
      split_ands <;> rw [vonMangoldt_apply_pow (by norm_num)] <;> (try rw [primes.1]) <;> simp_all
    have comps : Λ 6 = 0 ∧ Λ 10 = 0 ∧ Λ 12 = 0 ∧ Λ 14 = 0 ∧ Λ 15 = 0 ∧ Λ 18 = 0 ∧ Λ 20 = 0 ∧ Λ 21 = 0 ∧ Λ 22 = 0 ∧ Λ 24 = 0 ∧ Λ 26 = 0 ∧ Λ 28 = 0 ∧ Λ 30 = 0 := by
      split_ands <;> rw [vonMangoldt_eq_zero_iff, isPrimePow_nat_iff_bounded_log] <;> decide
    have hlog_pow (p k : ℕ) (hp : 0 < p) (hpk : p ≤ 2^k) : Real.log p ≤ k * 0.7 := by
      have hh := Real.log_le_log (show (0 : ℝ) < p by exact_mod_cast hp) (show (p : ℝ) ≤ (2 : ℝ)^k by exact_mod_cast hpk)
      rw [Real.log_pow] at hh
      nlinarith [mul_nonneg (show (0 : ℝ) ≤ k by positivity) (show 0 ≤ (0.7 : ℝ) - Real.log 2 by linarith [Real.log_two_lt_d9])]
    have h2 := hlog_pow 2 1 (by decide) (by decide)
    have h3 := hlog_pow 3 2 (by decide) (by decide)
    have h5 := hlog_pow 5 3 (by decide) (by decide)
    have h7 := hlog_pow 7 3 (by decide) (by decide)
    have h11 := hlog_pow 11 4 (by decide) (by decide)
    have h13 := hlog_pow 13 4 (by decide) (by decide)
    have h17 := hlog_pow 17 5 (by decide) (by decide)
    have h19 := hlog_pow 19 5 (by decide) (by decide)
    have h23 := hlog_pow 23 5 (by decide) (by decide)
    have h29 := hlog_pow 29 5 (by decide) (by decide)
    unfold psi
    split_ands <;>
      simp_all only [Nat.reducePow, zero_add, Nat.reduceAdd, Nat.cast_ofNat,
        Nat.floor_ofNat, zero_le, sum_Ioc_succ_top, Nat.Ioc_succ_singleton,
        sum_singleton, vonMangoldt_apply_one, add_zero] <;> nlinarith
  by_cases h18 : 18 ≤ n
  · have hn' : (n : ℝ) ≤ 30 := by exact_mod_cast hn
    have h18' : (18 : ℝ) ≤ n := by exact_mod_cast h18
    linarith [hmono hn', hnum.2.2]
  by_cases h10 : 10 ≤ n
  · have hn' : (n : ℝ) ≤ 17 := by exact_mod_cast (show n ≤ 17 by omega)
    have h10' : (10 : ℝ) ≤ n := by exact_mod_cast h10
    linarith [hmono hn', hnum.2.1]
  by_cases h5 : 5 ≤ n
  · have hn' : (n : ℝ) ≤ 9 := by exact_mod_cast (show n ≤ 9 by omega)
    have h5' : (5 : ℝ) ≤ n := by exact_mod_cast h5
    linarith [hmono hn', hnum.1]
  interval_cases n
  · simp [psi_eq_zero_of_lt_two (by norm_num : (0 : ℝ) < 2)]
  · simp [psi_eq_zero_of_lt_two (by norm_num : (1 : ℝ) < 2)]
  all_goals unfold psi
  all_goals
    norm_num [sum_Ioc_succ_top, vonMangoldt_apply_prime (by decide : Nat.Prime 2),
      vonMangoldt_apply_prime (by decide : Nat.Prime 3),
      show Λ 4 = Real.log 2 from by
        rw [show (4 : ℕ) = 2^2 by decide, vonMangoldt_apply_pow (by decide), vonMangoldt_apply_prime (by decide)]
        norm_num]
    linarith [Real.log_two_lt_d9, Real.log_three_lt_d9]

theorem psi_le_double_nat (n : ℕ) : ψ (n : ℝ) ≤ 2*n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hsmall : n ≤ 30
    · exact psi_le_double_small n hsmall
    · have hn30 : (30 : ℝ) ≤ n := by exact_mod_cast (show 30 ≤ n by omega)
      let m := ⌊(n : ℝ)/6⌋₊
      have hmR : (m : ℝ) ≤ n/6 := Nat.floor_le (by positivity)
      have hmn : m < n := by exact_mod_cast (show (m : ℝ) < n by linarith)
      have ih' := ih m hmn
      have hl := Real.log_le_sub_one_of_pos (show 0 < (n : ℝ)/30 by positivity)
      rw [Real.log_div (by positivity) (by norm_num)] at hl
      have hlog30 : Real.log 30 ≤ 3.5 := by
        have hlog := Real.log_le_log (show (0 : ℝ) < 30 by norm_num) (show (30 : ℝ) ≤ 2 ^ (5 : ℕ) by norm_num)
        rw [Real.log_pow] at hlog
        norm_num at hlog
        linarith [Real.log_two_lt_d9]
      have h := psi_diff_upper (n : ℝ) hn30
      rw [psi_eq_psi_coe_floor ((n : ℝ)/6)] at h
      change ψ (n : ℝ) - ψ (m : ℝ) ≤ _ at h
      nlinarith [mul_le_mul_of_nonneg_right a_bound.2 (show (0 : ℝ) ≤ n by positivity)]

theorem psi_le_double (x : ℝ) (hx : 0 ≤ x) : ψ x ≤ 2*x := by
  rw [psi_eq_psi_coe_floor x]
  linarith [psi_le_double_nat ⌊x⌋₊, Nat.floor_le hx]

theorem psi_refined_upper_nat (n : ℕ) (hn : 1 ≤ n) :
    ψ (n : ℝ) ≤ (6*a/5) * n + 2 * (Real.log n)^2 + 30 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    have ha : 0 ≤ a := by linarith [a_bound.1]
    have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
    by_cases hsmall : n < 30
    · have hpsi := psi_le_double_nat n
      have hnn : (n : ℝ) ≤ 30 := by exact_mod_cast hsmall.le
      have ha' : 1 ≤ 6*a/5 := by linarith [a_bound.1]
      nlinarith [sq_nonneg (Real.log n), mul_nonneg (sub_nonneg.mpr ha') (show (0 : ℝ) ≤ n by positivity)]
    · let m := ⌊(n : ℝ)/6⌋₊
      have hn30 : (30 : ℝ) ≤ n := by exact_mod_cast Nat.le_of_not_gt hsmall
      have hmR : (m : ℝ) ≤ n / 6 := Nat.floor_le (by positivity)
      have hm1 : 1 ≤ m := (Nat.one_le_floor_iff _).mpr (by linarith)
      have hm1R : (1 : ℝ) ≤ m := by exact_mod_cast hm1
      have hmn : m < n := by
        have : (m : ℝ) < n := by linarith
        exact_mod_cast this
      have hm_log : Real.log m ≤ Real.log ((n : ℝ)/6) := log_le_log (by positivity) hmR
      have hm_log0 : 0 ≤ Real.log m := log_nonneg hm1R
      have hlog6 : 1.5 ≤ Real.log 6 := by
        rw [show (6 : ℝ) = 2 * 3 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
        linarith [Real.log_two_gt_d9, Real.log_three_gt_d9]
      have hlogn : Real.log (n : ℝ) ≥ Real.log 6 := log_le_log (by norm_num) (by linarith)
      have hlogdiv : Real.log ((n : ℝ)/6) = Real.log n - Real.log 6 := Real.log_div (by positivity) (by norm_num)
      have hlogdiff : 2 * (Real.log m)^2 + 5 * Real.log n - 5 ≤ 2 * (Real.log n)^2 := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hm_log) (show 0 ≤ Real.log ((n:ℝ)/6) + Real.log m by linarith),
          mul_nonneg (sub_nonneg.mpr hlogn) (show 0 ≤ 4 * Real.log 6 - 5 by linarith),
          sq_nonneg (Real.log 6 - 1.25)]
      have hs := psi_diff_upper (n : ℝ) hn30
      rw [psi_eq_psi_coe_floor ((n : ℝ)/6)] at hs
      change ψ (n : ℝ) - ψ (m : ℝ) ≤ _ at hs
      have ih' := ih m hmn hm1
      nlinarith [mul_le_mul_of_nonneg_right hmR ha]

theorem psi_refined_upper (x : ℝ) (hx : 1 ≤ x) :
    ψ x ≤ (6*a/5) * x + 2 * (Real.log x)^2 + 30 := by
  let n := ⌊x⌋₊
  have hn : 1 ≤ n := (Nat.one_le_floor_iff _).mpr hx
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnx : (n : ℝ) ≤ x := Nat.floor_le (by linarith)
  have hlog := Real.log_le_log (show (0 : ℝ) < n by linarith) hnx
  have ha : 0 ≤ a := by linarith [a_bound.1]
  rw [psi_eq_psi_coe_floor x]
  change ψ (n : ℝ) ≤ _
  nlinarith [psi_refined_upper_nat n hn, mul_le_mul_of_nonneg_right hnx ha,
    mul_nonneg (sub_nonneg.mpr hlog) (add_nonneg (Real.log_nonneg hx) (Real.log_nonneg hnR))]

theorem sqrt_threshold_refined (x : ℝ) (hx : (16384 : ℝ) ≤ x) :
    (128 : ℝ) ≤ Real.sqrt x := by
  calc (128 : ℝ) = Real.sqrt 16384 := by norm_num
    _ ≤ Real.sqrt x := Real.sqrt_le_sqrt hx

theorem log_le_sqrt_refined (x : ℝ) (hx : (16384 : ℝ) ≤ x) :
    Real.log x ≤ (10 / 128) * Real.sqrt x := by
  have hx0 : 0 ≤ x := by linarith
  have hs := sqrt_threshold_refined x hx
  have hs0 : 0 < Real.sqrt x := by linarith
  have hlog128 : Real.log 128 ≤ 5 := by
    rw [show (128 : ℝ) = 2 ^ (7 : ℕ) by norm_num, Real.log_pow]
    norm_num
    linarith [Real.log_two_lt_d9]
  have hlog := Real.log_le_sub_one_of_pos (show 0 < Real.sqrt x / 128 by positivity)
  rw [Real.log_div (by positivity) (by norm_num), Real.log_sqrt hx0] at hlog
  linarith

theorem theta_upper_refined (x : ℝ) (hx : (16384 : ℝ) ≤ x) : θ x ≤ 1.12*x := by
  have hx0 : 0 ≤ x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hlog := log_le_sqrt_refined x hx
  have hlog0 := Real.log_nonneg hx1
  have hs0 := Real.sqrt_nonneg x
  have hsq := Real.sq_sqrt hx0
  have hsqlog : (Real.log x)^2 ≤ (10/128 : ℝ)^2 * x := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hlog) (show 0 ≤ (10/128 : ℝ) * Real.sqrt x + Real.log x by positivity)]
  have hax := mul_le_mul_of_nonneg_right a_bound.2 hx0
  nlinarith [psi_refined_upper x hx1, theta_le_psi x]

theorem rpow_third_le_sqrt_quarter_refined (x : ℝ) (hx : (4096 : ℝ) ≤ x) :
    x ^ (3 : ℝ)⁻¹ ≤ Real.sqrt x / 4 := by
  have hx0 : 0 ≤ x := by linarith
  have hxpos : 0 < x := by linarith
  have hbase : (4 : ℝ) ≤ x ^ ((6 : ℝ)⁻¹) := by
    have hpow : ((4 : ℝ) ^ (6 : ℕ)) ^ ((6 : ℝ)⁻¹) = 4 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
      norm_num
    rw [← hpow]
    exact Real.rpow_le_rpow (by positivity) (by norm_num; linarith) (by norm_num)
  have hmul := mul_le_mul_of_nonneg_left hbase (Real.rpow_nonneg hx0 ((3 : ℝ)⁻¹))
  rw [← Real.rpow_add hxpos, show (3 : ℝ)⁻¹ + (6 : ℝ)⁻¹ = 1/2 by norm_num,
    ← Real.sqrt_eq_rpow] at hmul
  linarith

theorem theta_lower_refined (x : ℝ) (hx : (16384 : ℝ) ≤ x) : 0.894*x ≤ θ x := by
  have hx0 : 0 ≤ x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hlog := log_le_sqrt_refined x hx
  have hs := sqrt_threshold_refined x hx
  have hsq := Real.sq_sqrt hx0
  have hpow3 := rpow_third_le_sqrt_quarter_refined x (by linarith)
  have hpow5 : x ^ (5 : ℝ)⁻¹ ≤ Real.sqrt x / 4 :=
    (Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num : (5 : ℝ)⁻¹ ≤ (3 : ℝ)⁻¹)).trans hpow3
  have hpow2 : x ^ (2 : ℝ)⁻¹ = Real.sqrt x := by rw [Real.sqrt_eq_rpow]; norm_num
  have hψ2 : ψ (x ^ (2 : ℝ)⁻¹) ≤ 2 * Real.sqrt x := by
    rw [hpow2]; exact psi_le_double _ (Real.sqrt_nonneg x)
  have hψ3 : ψ (x ^ (3 : ℝ)⁻¹) ≤ 2 * (Real.sqrt x / 4) := by
    have hn := Real.rpow_nonneg hx0 ((3 : ℝ)⁻¹)
    exact (psi_le_double _ hn).trans (mul_le_mul_of_nonneg_left hpow3 (by norm_num))
  have hψ5 : ψ (x ^ (5 : ℝ)⁻¹) ≤ 2 * (Real.sqrt x / 4) := by
    have hn := Real.rpow_nonneg hx0 ((5 : ℝ)⁻¹)
    exact (psi_le_double _ hn).trans (mul_le_mul_of_nonneg_left hpow5 (by norm_num))
  have hψlower := psi_lower x (by linarith)
  have ha := mul_le_mul_of_nonneg_right a_bound.1 hx0
  have hθ := psi_sub_theta_le_psi_add_psi_add_psi x
  nlinarith [mul_nonneg (sub_nonneg.mpr hs) (Real.sqrt_nonneg x)]

theorem log_threshold_lower_refined (x : ℝ) (hx : (16384 : ℝ) ≤ x) :
    (9 : ℝ) ≤ Real.log x := by
  have hlog := Real.log_le_log (show (0 : ℝ) < 16384 by norm_num) hx
  rw [show (16384 : ℝ) = 2^(14 : ℕ) by norm_num, Real.log_pow] at hlog
  norm_num at hlog
  linarith [Real.log_two_gt_d9]

theorem log_mul_two_thirds_refined (x : ℝ) (hx : (16384 : ℝ) ≤ x) :
    x ^ (2/3 : ℝ) * Real.log x ≤ 0.4*x := by
  have hx0 : 0 < x := by linarith
  have hbase : (25 : ℝ) ≤ x ^ (1/3 : ℝ) := by
    have hpow : ((25 : ℝ) ^ (3 : ℕ)) ^ (1/3 : ℝ) = 25 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
      norm_num
    rw [← hpow]
    exact Real.rpow_le_rpow (by positivity) (by norm_num; linarith) (by norm_num)
  have hlog25 : Real.log 25 ≤ 10/3 := by
    rw [show (25 : ℝ) = 5^2 by norm_num, Real.log_pow]
    norm_num
    linarith [Real.log_five_lt_d9]
  have hlog := Real.log_le_sub_one_of_pos (show 0 < x ^ (1/3 : ℝ) / 25 by positivity)
  rw [Real.log_div (by positivity) (by norm_num), Real.log_rpow hx0] at hlog
  have hb : Real.log x ≤ 0.4 * x ^ (1/3 : ℝ) := by linarith
  have hmul := mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg hx0.le (2/3))
  have hmul' : x ^ (2/3 : ℝ) * x ^ (1/3 : ℝ) = x := by
    rw [← Real.rpow_add hx0, show (2/3 : ℝ) + 1/3 = 1 by norm_num, Real.rpow_one]
  linarith [hmul, show x ^ (2/3 : ℝ) * (0.4 * x ^ (1/3 : ℝ)) = 0.4*x by linear_combination 0.4*hmul']

theorem primeCounting_ratio_refined (x : ℝ) (hx : (16384 : ℝ) ≤ x) :
    5 * Nat.primeCounting ⌊x⌋₊ < 4 * Nat.primeCounting ⌊48*x/25⌋₊ := by
  let p := Nat.primeCounting ⌊x⌋₊
  let q := Nat.primeCounting ⌊48*x/25⌋₊
  change 5*p < 4*q
  have hbridge : θ (48*x/25) - θ x ≤ ((q : ℝ) - p) * Real.log (48*x/25) :=
    PrimeIntervalBridge.theta_interval_le x _ (by linarith) (by linarith)
  have hz : (16384 : ℝ) ≤ 48*x/25 := by linarith
  have hθL := theta_lower_refined (48*x/25) hz
  have hθU := theta_upper_refined x hx
  have hlogX := log_threshold_lower_refined x hx
  have hlog0 : 0 < Real.log x := by linarith
  have hlogZ : 0 < Real.log (48*x/25) := by linarith [log_threshold_lower_refined (48*x/25) hz]
  have hlog_scaled : Real.log (48*x/25) ≤ Real.log x + 0.75 := by
    convert log_scaled_le x (48/25) (by linarith) (by norm_num) (by norm_num) using 1
    ring_nf
  have hlogratio : Real.log (48*x/25) ≤ (13/12)*Real.log x := by linarith
  have hpowlog := log_mul_two_thirds_refined x hx
  have hsplit : (p : ℝ) * Real.log x ≤ (3/2)*θ x + x ^ (2/3 : ℝ) * Real.log x := by
    calc (p : ℝ)*Real.log x ≤ ((3/2)*θ x / Real.log x + x^(2/3 : ℝ)) * Real.log x :=
        mul_le_mul_of_nonneg_right (PrimeIntervalBridge.primeCounting_le_theta_split_two_thirds x (by linarith)) hlog0.le
      _ = _ := by field_simp
  have hd : (0 : ℝ) ≤ (q : ℝ) - p := by
    by_contra! hneg
    have hm := mul_neg_of_neg_of_pos hneg hlogZ
    linarith
  have hD := mul_le_mul_of_nonneg_left hlogratio hd
  have hfinal : (p : ℝ) * Real.log x < 4*((q : ℝ)-p)*Real.log x := by
    nlinarith
  have hfinal' : (p : ℝ) < 4*((q : ℝ)-p) := by
    by_contra! hn
    have hm := mul_le_mul_of_nonneg_right hn hlog0.le
    linarith
  exact_mod_cast (show (5 : ℝ)*p < 4*(q : ℝ) by linarith)

end Chebyshev


/- Explicit finite certificate: two primes in the open interval `(x, 5*x/4)`
    for every natural x between 100 and 262144. -/
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem two_primes_short_interval_finite (x : ℕ) (hx : 100 ≤ x)
    (hx' : x ≤ 262144) :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ x < p ∧ p < q ∧ 4 * q < 5 * x := by
  by_cases h0 : x < 109
  · exact ⟨109, 113, by norm_num, by norm_num, by omega, by norm_num, by omega⟩
  by_cases h1 : x < 127
  · exact ⟨127, 131, by norm_num, by norm_num, by omega, by norm_num, by omega⟩
  by_cases h2 : x < 151
  · exact ⟨151, 157, by norm_num, by norm_num, by omega, by norm_num, by omega⟩
  by_cases h3 : x < 179
  · exact ⟨179, 181, by norm_num, by norm_num, by omega, by norm_num, by omega⟩
  by_cases h4 : x < 211
  · exact ⟨211, 223, by norm_num, by norm_num, by omega, by norm_num, by omega⟩
  by_cases h5 : x < 257
  · exact ⟨257, 263, by norm_num, by norm_num, by omega, by norm_num, by omega⟩
  by_cases h6 : x < 313
  · exact ⟨313, 317, by norm_num, by norm_num, by omega, by norm_num, by omega⟩
  by_cases h7 : x < 383
  · exact ⟨383, 389, by norm_num, by norm_num, by omega, by norm_num, by omega⟩
  by_cases h8 : x < 463
  · exact ⟨463, 467, by norm_num, by norm_num, by omega, by norm_num, by omega⟩
  by_cases h9 : x < 571
  · exact ⟨571, 577, by norm_num, by norm_num, by omega, by norm_num, by omega⟩
  by_cases h10 : x < 701
  · exact ⟨701, 709, by norm_num, by norm_num, by omega, by norm_num, by omega⟩
  by_cases h11 : x < 859
  · exact ⟨859, 863, by norm_num, by norm_num, by omega, by norm_num, by omega⟩
  by_cases h12 : x < 1063
  · exact ⟨1063, 1069, by norm_num, by norm_num, by omega, by norm_num, by omega⟩
  by_cases h13 : x < 1321
  · exact ⟨1321, 1327, by norm_num, by norm_num, by omega, by norm_num, by omega⟩
  by_cases h14 : x < 1627
  · exact ⟨1627, 1637, by norm_num, by norm_num, by omega, by norm_num, by omega⟩
  by_cases h15 : x < 2027
  · exact ⟨2027, 2029, by norm_num, by norm_num, by omega, by norm_num, by omega⟩
  by_cases h16 : x < 2521
  · exact ⟨2521, 2531, by norm_num, by norm_num, by omega, by norm_num, by omega⟩
  by_cases h17 : x < 3121
  · exact ⟨3121, 3137, by norm_num, by norm_num, by omega, by norm_num, by omega⟩
  by_cases h18 : x < 3881
  · exact ⟨3881, 3889, by norm_num, by norm_num, by omega, by norm_num, by omega⟩
  by_cases h19 : x < 4817
  · exact ⟨4817, 4831, by norm_num, by norm_num, by omega, by norm_num, by omega⟩
  by_cases h20 : x < 6007
  · exact ⟨6007, 6011, by norm_num, by norm_num, by omega, by norm_num, by omega⟩
  by_cases h21 : x < 7499
  · exact ⟨7499, 7507, by norm_num, by norm_num, by omega, by norm_num, by omega⟩
  by_cases h22 : x < 9349
  · exact ⟨9349, 9371, by norm_num, by norm_num, by omega, by norm_num, by omega⟩
  by_cases h23 : x < 11677
  · exact ⟨11677, 11681, by norm_num, by norm_num, by omega, by norm_num, by omega⟩
  by_cases h24 : x < 14591
  · exact ⟨14591, 14593, by norm_num, by norm_num, by omega, by norm_num, by omega⟩
  by_cases h25 : x < 18229
  · exact ⟨18229, 18233, by norm_num, by norm_num, by omega, by norm_num, by omega⟩
  by_cases h26 : x < 22777
  · exact ⟨22777, 22783, by norm_num, by norm_num, by omega, by norm_num, by omega⟩
  by_cases h27 : x < 28447
  · exact ⟨28447, 28463, by norm_num, by norm_num, by omega, by norm_num, by omega⟩
  by_cases h28 : x < 35537
  · exact ⟨35537, 35543, by norm_num, by norm_num, by omega, by norm_num, by omega⟩
  by_cases h29 : x < 44389
  · exact ⟨44389, 44417, by norm_num, by norm_num, by omega, by norm_num, by omega⟩
  by_cases h30 : x < 55457
  · exact ⟨55457, 55469, by norm_num, by norm_num, by omega, by norm_num, by omega⟩
  by_cases h31 : x < 69313
  · exact ⟨69313, 69317, by norm_num, by norm_num, by omega, by norm_num, by omega⟩
  by_cases h32 : x < 86627
  · exact ⟨86627, 86629, by norm_num, by norm_num, by omega, by norm_num, by omega⟩
  by_cases h33 : x < 108263
  · exact ⟨108263, 108271, by norm_num, by norm_num, by omega, by norm_num, by omega⟩
  by_cases h34 : x < 135301
  · exact ⟨135301, 135319, by norm_num, by norm_num, by omega, by norm_num, by omega⟩
  by_cases h35 : x < 169097
  · exact ⟨169097, 169111, by norm_num, by norm_num, by omega, by norm_num, by omega⟩
  by_cases h36 : x < 211349
  · exact ⟨211349, 211369, by norm_num, by norm_num, by omega, by norm_num, by omega⟩
  exact ⟨264169, 264179, by norm_num, by norm_num, by omega, by norm_num, by omega⟩


namespace PrimeCountBands

def Good (ps : List ℕ) (m : ℕ) : Prop := ∀ p ∈ ps, ¬ p ∣ m

instance (ps : List ℕ) (m : ℕ) : Decidable (Good ps m) :=
  List.decidableBAll (fun p => ¬ p ∣ m) ps

def GoodSet (ps : List ℕ) (n : ℕ) : Finset ℕ :=
  (Finset.Icc 1 n).filter (Good ps)

theorem mem_goodSet {ps : List ℕ} {m n : ℕ} :
    m ∈ GoodSet ps n ↔ (1 ≤ m ∧ m ≤ n) ∧ Good ps m := by
  simp [GoodSet]

theorem good_cons {p m : ℕ} {ps : List ℕ} :
    Good (p :: ps) m ↔ ¬ p ∣ m ∧ Good ps m := by
  simp [Good]

theorem good_mul {p : ℕ} {ps : List ℕ} (hp : p.Prime)
    (hps : ∀ q ∈ ps, Nat.Prime q) (hd : p ∉ ps) (k : ℕ) :
    Good ps (p*k) ↔ Good ps k := by
  constructor
  · intro h q hq hk
    exact h q hq ((hps q hq).dvd_mul.2 (Or.inr hk))
  · intro h q hq hprod
    rcases (hps q hq).dvd_mul.1 hprod with hqp | hqk
    · rcases (Nat.dvd_prime hp).1 hqp with he | he
      · exact (hps q hq).ne_one he
      · exact hd (he ▸ hq)
    · exact h q hq hqk

theorem goodSet_mul {p n : ℕ} {ps : List ℕ} (hp : p.Prime)
    (hps : ∀ q ∈ ps, Nat.Prime q) (hd : p ∉ ps) :
    (GoodSet ps n).filter (fun m => p ∣ m) =
      (GoodSet ps (n/p)).image (fun k => p*k) := by
  ext m
  rw [Finset.mem_filter, mem_goodSet, Finset.mem_image]
  constructor
  · rintro ⟨⟨hm, hgood⟩, ⟨k, hk⟩⟩
    refine ⟨k, mem_goodSet.2 ⟨⟨?_, ?_⟩, ?_⟩, hk.symm⟩
    · by_contra! h
      have : k = 0 := by omega
      simp [this] at hk
      omega
    · apply (Nat.le_div_iff_mul_le hp.pos).2
      rw [Nat.mul_comm, ← hk]
      exact hm.2
    · apply (good_mul hp hps hd k).1
      rwa [← hk]
  · rintro ⟨k, hk, rfl⟩
    rcases mem_goodSet.1 hk with ⟨⟨hk1, hk2⟩, hgood⟩
    refine ⟨⟨⟨?_, ?_⟩, (good_mul hp hps hd k).2 hgood⟩, ⟨k, rfl⟩⟩
    · exact Nat.mul_pos hp.pos (by omega)
    · rw [Nat.mul_comm]
      exact (Nat.le_div_iff_mul_le hp.pos).1 hk2

theorem goodSet_cons {p n : ℕ} {ps : List ℕ} :
    GoodSet (p::ps) n = (GoodSet ps n).filter (fun m => ¬ p ∣ m) := by
  ext m
  rw [mem_goodSet, Finset.mem_filter, mem_goodSet, good_cons]
  tauto

theorem card_goodSet_cons {p n : ℕ} {ps : List ℕ} (hp : p.Prime)
    (hps : ∀ q ∈ ps, Nat.Prime q) (hd : p ∉ ps) :
    (GoodSet (p::ps) n).card =
      (GoodSet ps n).card - (GoodSet ps (n/p)).card := by
  have h := Finset.card_filter_add_card_filter_not
    (s := GoodSet ps n) (fun m => p ∣ m)
  rw [goodSet_mul hp hps hd, Finset.card_image_of_injective _
    (fun _ _ e => Nat.mul_left_cancel hp.pos e), ← goodSet_cons] at h
  omega

def phi (n : ℕ) (ps : List ℕ) : ℕ :=
  match ps with
  | [] => n
  | p::ps =>
    if n = 0 then 0 else
    if n = 1 then 1 else
    if n < p then phi n ps else phi n ps - phi (n/p) ps

theorem card_goodSet_zero (ps : List ℕ) : (GoodSet ps 0).card = 0 := by
  simp [GoodSet]

theorem card_goodSet_one {ps : List ℕ} (hps : ∀ q ∈ ps, Nat.Prime q) :
    (GoodSet ps 1).card = 1 := by
  have h : Good ps 1 := by
    intro q hq hdiv
    exact (hps q hq).ne_one (Nat.dvd_one.1 hdiv)
  have he : GoodSet ps 1 = {1} := by
    ext m
    simp only [mem_goodSet, Finset.mem_singleton]
    constructor
    · intro hm
      omega
    · rintro rfl
      exact ⟨⟨by omega, by omega⟩, h⟩
  rw [he, Finset.card_singleton]

theorem card_goodSet_eq_phi (ps : List ℕ) (hn : ps.Nodup)
    (hps : ∀ q ∈ ps, Nat.Prime q) (n : ℕ) :
    (GoodSet ps n).card = phi n ps := by
  induction ps generalizing n with
  | nil =>
    have h : GoodSet [] n = Finset.Icc 1 n := by
      ext m
      simp [mem_goodSet, Good]
    simp [h, Nat.card_Icc, phi]
  | cons p ps ih =>
    rcases List.nodup_cons.1 hn with ⟨hd, hn'⟩
    have hp : p.Prime := hps p (by simp)
    have hps' : ∀ q ∈ ps, Nat.Prime q := fun q hq => hps q (by simp [hq])
    rw [phi]
    split
    · subst n
      exact card_goodSet_zero _
    · split
      · rename_i _ e
        subst n
        exact card_goodSet_one hps
      · rw [card_goodSet_cons hp hps' hd, ih hn' hps', ih hn' hps']
        split
        · rename_i e
          have hz := Nat.div_eq_of_lt e
          have hzero := (ih hn' hps' 0).symm.trans (card_goodSet_zero ps)
          simp [hz, hzero]
        · rfl

theorem prime_count_eq (ps : List ℕ) (hn : ps.Nodup)
    (hps : ∀ p ∈ ps, Nat.Prime p) (n B : ℕ)
    (hn1 : 1 ≤ n) (hbound : n < (B+1)^2)
    (hcomplete : ∀ q ≤ B, q.Prime → q ∈ ps)
    (hsmall : ∀ q ∈ ps, q ≤ n) :
    n.primeCounting + 1 = phi n ps + ps.length := by
  have hprime : n.primeCounting = n.primesLE.card := by
    simp [Nat.primeCounting, Nat.primeCounting', Nat.primesLE,
      Nat.primesBelow, Nat.count_eq_card_filter_range]
  have heq : GoodSet ps n ∪ ps.toFinset = insert 1 n.primesLE := by
    ext m
    rw [Finset.mem_union, mem_goodSet, List.mem_toFinset, Finset.mem_insert, Nat.mem_primesLE]
    constructor
    · rintro (⟨⟨hm1, hmn⟩, hg⟩ | hl)
      · by_cases h : m = 1
        · exact Or.inl h
        · refine Or.inr ⟨hmn, ?_⟩
          by_contra hnp
          have hmin := Nat.minFac_sq_le_self (show 0 < m by omega) hnp
          have hb : m.minFac ≤ B := by
            by_contra! e
            have hsq := Nat.pow_le_pow_left (show B+1 ≤ m.minFac by omega) 2
            omega
          exact hg _ (hcomplete _ hb (Nat.minFac_prime h)) (Nat.minFac_dvd m)
      · exact Or.inr ⟨hsmall _ hl, hps _ hl⟩
    · rintro (rfl | ⟨hmn, hp⟩)
      · refine Or.inl ⟨⟨by omega, hn1⟩, ?_⟩
        intro q hq hdiv
        exact (hps q hq).ne_one (Nat.dvd_one.1 hdiv)
      · by_cases h : m ∈ ps
        · exact Or.inr h
        · refine Or.inl ⟨⟨hp.one_lt.le, hmn⟩, ?_⟩
          intro q hq hdiv
          rcases (Nat.dvd_prime hp).1 hdiv with e | e
          · exact (hps q hq).ne_one e
          · exact h (e ▸ hq)
  have hd : Disjoint (GoodSet ps n) ps.toFinset := by
    rw [Finset.disjoint_left]
    intro m hm hl
    exact (mem_goodSet.1 hm).2 m (List.mem_toFinset.1 hl) (Nat.dvd_refl _)
  have hnot : 1 ∉ n.primesLE := by
    intro h
    exact (Nat.mem_primesLE.1 h).2.ne_one rfl
  have hcard := congrArg Finset.card heq
  rw [Finset.card_union_of_disjoint hd, Finset.card_insert_of_notMem hnot,
      List.toFinset_card_of_nodup hn, card_goodSet_eq_phi ps hn hps, ← hprime] at hcard
  exact hcard.symm


private def smallPrimes : List ℕ := [139,137,131,127,113,109,107,103,101,97,89,83,79,73,71,67,61,59,53,47,43,41,37,31,29,23,19,17,13,11,7,5,3,2]

private theorem smallPrimes_nodup : smallPrimes.Nodup := by decide

private theorem smallPrimes_prime (p : ℕ) (hp : p ∈ smallPrimes) : p.Prime := by
  simp only [smallPrimes, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num

private theorem smallPrimes_complete (p : ℕ) (hb : p ≤ 148) (hp : p.Prime) : p ∈ smallPrimes := by
  interval_cases p <;> first | (solve | norm_num at hp) | decide

private theorem smallPrimes_le (p : ℕ) (hp : p ∈ smallPrimes) : p ≤ 148 := by
  simp only [smallPrimes, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega

private theorem prime_count_smallPrimes (n : ℕ) (hn : 148 ≤ n) (hb : n < 149^2) :
    n.primeCounting + 1 = phi n smallPrimes + smallPrimes.length := by
  apply prime_count_eq smallPrimes smallPrimes_nodup smallPrimes_prime n 148
    (by omega) hb smallPrimes_complete
  exact fun p hp => (smallPrimes_le p hp).trans hn

private theorem smallPrimes_length : smallPrimes.length = 34 := by decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem count_732 : Nat.primeCounting 732 = 129 := by
  have h := prime_count_smallPrimes 732 (by decide) (by decide)
  have hp : phi 732 smallPrimes = 96 := by decide
  rw [smallPrimes_length, hp] at h
  omega

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem count_960 : Nat.primeCounting 960 = 162 := by
  have h := prime_count_smallPrimes 960 (by decide) (by decide)
  have hp : phi 960 smallPrimes = 129 := by decide
  rw [smallPrimes_length, hp] at h
  omega

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem count_1060 : Nat.primeCounting 1060 = 177 := by
  have h := prime_count_smallPrimes 1060 (by decide) (by decide)
  have hp : phi 1060 smallPrimes = 144 := by decide
  rw [smallPrimes_length, hp] at h
  omega

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem count_1407 : Nat.primeCounting 1407 = 222 := by
  have h := prime_count_smallPrimes 1407 (by decide) (by decide)
  have hp : phi 1407 smallPrimes = 189 := by decide
  rw [smallPrimes_length, hp] at h
  omega

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem count_1566 : Nat.primeCounting 1566 = 246 := by
  have h := prime_count_smallPrimes 1566 (by decide) (by decide)
  have hp : phi 1566 smallPrimes = 213 := by decide
  rw [smallPrimes_length, hp] at h
  omega

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem count_2037 : Nat.primeCounting 2037 = 308 := by
  have h := prime_count_smallPrimes 2037 (by decide) (by decide)
  have hp : phi 2037 smallPrimes = 275 := by decide
  rw [smallPrimes_length, hp] at h
  omega

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem count_2332 : Nat.primeCounting 2332 = 344 := by
  have h := prime_count_smallPrimes 2332 (by decide) (by decide)
  have hp : phi 2332 smallPrimes = 311 := by decide
  rw [smallPrimes_length, hp] at h
  omega

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem count_3008 : Nat.primeCounting 3008 = 431 := by
  have h := prime_count_smallPrimes 3008 (by decide) (by decide)
  have hp : phi 3008 smallPrimes = 398 := by decide
  rw [smallPrimes_length, hp] at h
  omega

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem count_3466 : Nat.primeCounting 3466 = 485 := by
  have h := prime_count_smallPrimes 3466 (by decide) (by decide)
  have hp : phi 3466 smallPrimes = 452 := by decide
  rw [smallPrimes_length, hp] at h
  omega

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem count_4479 : Nat.primeCounting 4479 = 607 := by
  have h := prime_count_smallPrimes 4479 (by decide) (by decide)
  have hp : phi 4479 smallPrimes = 574 := by decide
  rw [smallPrimes_length, hp] at h
  omega

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem count_5146 : Nat.primeCounting 5146 = 685 := by
  have h := prime_count_smallPrimes 5146 (by decide) (by decide)
  have hp : phi 5146 smallPrimes = 652 := by decide
  rw [smallPrimes_length, hp] at h
  omega

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem count_6656 : Nat.primeCounting 6656 = 857 := by
  have h := prime_count_smallPrimes 6656 (by decide) (by decide)
  have hp : phi 6656 smallPrimes = 824 := by decide
  rw [smallPrimes_length, hp] at h
  omega

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem count_7686 : Nat.primeCounting 7686 = 974 := by
  have h := prime_count_smallPrimes 7686 (by decide) (by decide)
  have hp : phi 7686 smallPrimes = 941 := by decide
  rw [smallPrimes_length, hp] at h
  omega

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem count_9882 : Nat.primeCounting 9882 = 1218 := by
  have h := prime_count_smallPrimes 9882 (by decide) (by decide)
  have hp : phi 9882 smallPrimes = 1185 := by decide
  rw [smallPrimes_length, hp] at h
  omega

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem count_11482 : Nat.primeCounting 11482 = 1383 := by
  have h := prime_count_smallPrimes 11482 (by decide) (by decide)
  have hp : phi 11482 smallPrimes = 1350 := by decide
  rw [smallPrimes_length, hp] at h
  omega

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem count_14759 : Nat.primeCounting 14759 = 1729 := by
  have h := prime_count_smallPrimes 14759 (by decide) (by decide)
  have hp : phi 14759 smallPrimes = 1696 := by decide
  rw [smallPrimes_length, hp] at h
  omega

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem count_17158 : Nat.primeCounting 17158 = 1975 := by
  have h := prime_count_smallPrimes 17158 (by decide) (by decide)
  have hp : phi 17158 smallPrimes = 1942 := by decide
  rw [smallPrimes_length, hp] at h
  omega

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem count_22047 : Nat.primeCounting 22047 = 2470 := by
  have h := prime_count_smallPrimes 22047 (by decide) (by decide)
  have hp : phi 22047 smallPrimes = 2437 := by decide
  rw [smallPrimes_length, hp] at h
  omega

private theorem ratio_of_band {a b z cb cz y : ℕ}
    (hay : a ≤ y) (hyb : y ≤ b) (hz : z ≤ 48*a/25)
    (hcb : Nat.primeCounting b = cb) (hcz : Nat.primeCounting z = cz)
    (hlt : 5*cb < 4*cz) :
    5 * Nat.primeCounting y < 4 * Nat.primeCounting (48*y/25) := by
  have hyb' := Nat.monotone_primeCounting hyb
  have hz' : z ≤ 48*y/25 := by omega
  have hzy := Nat.monotone_primeCounting hz'
  omega

theorem prime_count_ratio_finite (y : ℕ) (hy : 500 ≤ y) (hy' : y ≤ 16384) :
    5 * Nat.primeCounting y < 4 * Nat.primeCounting (48*y/25) := by
  by_cases hb0 : y ≤ 732
  · exact ratio_of_band (a := 500) (b := 732) (z := 960) (cb := 129) (cz := 162)
      (by omega) hb0 (by omega) count_732 count_960 (by omega)
  by_cases hb1 : y ≤ 1060
  · exact ratio_of_band (a := 733) (b := 1060) (z := 1407) (cb := 177) (cz := 222)
      (by omega) hb1 (by omega) count_1060 count_1407 (by omega)
  by_cases hb2 : y ≤ 1566
  · exact ratio_of_band (a := 1061) (b := 1566) (z := 2037) (cb := 246) (cz := 308)
      (by omega) hb2 (by omega) count_1566 count_2037 (by omega)
  by_cases hb3 : y ≤ 2332
  · exact ratio_of_band (a := 1567) (b := 2332) (z := 3008) (cb := 344) (cz := 431)
      (by omega) hb3 (by omega) count_2332 count_3008 (by omega)
  by_cases hb4 : y ≤ 3466
  · exact ratio_of_band (a := 2333) (b := 3466) (z := 4479) (cb := 485) (cz := 607)
      (by omega) hb4 (by omega) count_3466 count_4479 (by omega)
  by_cases hb5 : y ≤ 5146
  · exact ratio_of_band (a := 3467) (b := 5146) (z := 6656) (cb := 685) (cz := 857)
      (by omega) hb5 (by omega) count_5146 count_6656 (by omega)
  by_cases hb6 : y ≤ 7686
  · exact ratio_of_band (a := 5147) (b := 7686) (z := 9882) (cb := 974) (cz := 1218)
      (by omega) hb6 (by omega) count_7686 count_9882 (by omega)
  by_cases hb7 : y ≤ 11482
  · exact ratio_of_band (a := 7687) (b := 11482) (z := 14759) (cb := 1383) (cz := 1729)
      (by omega) hb7 (by omega) count_11482 count_14759 (by omega)
  exact ratio_of_band (a := 11483) (b := 17158) (z := 22047) (cb := 1975) (cz := 2470)
    (by omega) (by omega) (by omega) count_17158 count_22047 (by omega)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem prime_count_lt_157 : Nat.primeCounting' 157 = 36 := by
  change Nat.primeCounting 156 = 36
  have h := prime_count_smallPrimes 156 (by decide) (by decide)
  have hp : phi 156 smallPrimes = 3 := by decide
  rw [smallPrimes_length, hp] at h
  omega

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem prime_count_lt_179 : Nat.primeCounting' 179 = 40 := by
  change Nat.primeCounting 178 = 40
  have h := prime_count_smallPrimes 178 (by decide) (by decide)
  have hp : phi 178 smallPrimes = 7 := by decide
  rw [smallPrimes_length, hp] at h
  omega

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem prime_count_lt_191 : Nat.primeCounting' 191 = 42 := by
  change Nat.primeCounting 190 = 42
  have h := prime_count_smallPrimes 190 (by decide) (by decide)
  have hp : phi 190 smallPrimes = 9 := by decide
  rw [smallPrimes_length, hp] at h
  omega

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem prime_count_lt_211 : Nat.primeCounting' 211 = 46 := by
  change Nat.primeCounting 210 = 46
  have h := prime_count_smallPrimes 210 (by decide) (by decide)
  have hp : phi 210 smallPrimes = 13 := by decide
  rw [smallPrimes_length, hp] at h
  omega

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem prime_count_lt_241 : Nat.primeCounting' 241 = 52 := by
  change Nat.primeCounting 240 = 52
  have h := prime_count_smallPrimes 240 (by decide) (by decide)
  have hp : phi 240 smallPrimes = 19 := by decide
  rw [smallPrimes_length, hp] at h
  omega

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem prime_count_lt_277 : Nat.primeCounting' 277 = 58 := by
  change Nat.primeCounting 276 = 58
  have h := prime_count_smallPrimes 276 (by decide) (by decide)
  have hp : phi 276 smallPrimes = 25 := by decide
  rw [smallPrimes_length, hp] at h
  omega

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem prime_count_lt_283 : Nat.primeCounting' 283 = 60 := by
  change Nat.primeCounting 282 = 60
  have h := prime_count_smallPrimes 282 (by decide) (by decide)
  have hp : phi 282 smallPrimes = 27 := by decide
  rw [smallPrimes_length, hp] at h
  omega

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem prime_count_lt_331 : Nat.primeCounting' 331 = 66 := by
  change Nat.primeCounting 330 = 66
  have h := prime_count_smallPrimes 330 (by decide) (by decide)
  have hp : phi 330 smallPrimes = 33 := by decide
  rw [smallPrimes_length, hp] at h
  omega

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem prime_count_lt_353 : Nat.primeCounting' 353 = 70 := by
  change Nat.primeCounting 352 = 70
  have h := prime_count_smallPrimes 352 (by decide) (by decide)
  have hp : phi 352 smallPrimes = 37 := by decide
  rw [smallPrimes_length, hp] at h
  omega

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem prime_count_lt_367 : Nat.primeCounting' 367 = 72 := by
  change Nat.primeCounting 366 = 72
  have h := prime_count_smallPrimes 366 (by decide) (by decide)
  have hp : phi 366 smallPrimes = 39 := by decide
  rw [smallPrimes_length, hp] at h
  omega

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem prime_count_lt_401 : Nat.primeCounting' 401 = 78 := by
  change Nat.primeCounting 400 = 78
  have h := prime_count_smallPrimes 400 (by decide) (by decide)
  have hp : phi 400 smallPrimes = 45 := by decide
  rw [smallPrimes_length, hp] at h
  omega

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem prime_count_lt_431 : Nat.primeCounting' 431 = 82 := by
  change Nat.primeCounting 430 = 82
  have h := prime_count_smallPrimes 430 (by decide) (by decide)
  have hp : phi 430 smallPrimes = 49 := by decide
  rw [smallPrimes_length, hp] at h
  omega

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem prime_count_lt_461 : Nat.primeCounting' 461 = 88 := by
  change Nat.primeCounting 460 = 88
  have h := prime_count_smallPrimes 460 (by decide) (by decide)
  have hp : phi 460 smallPrimes = 55 := by decide
  rw [smallPrimes_length, hp] at h
  omega

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem prime_count_lt_509 : Nat.primeCounting' 509 = 96 := by
  change Nat.primeCounting 508 = 96
  have h := prime_count_smallPrimes 508 (by decide) (by decide)
  have hp : phi 508 smallPrimes = 63 := by decide
  rw [smallPrimes_length, hp] at h
  omega

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem prime_count_lt_541 : Nat.primeCounting' 541 = 99 := by
  change Nat.primeCounting 540 = 99
  have h := prime_count_smallPrimes 540 (by decide) (by decide)
  have hp : phi 540 smallPrimes = 66 := by decide
  rw [smallPrimes_length, hp] at h
  omega

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem prime_count_lt_547 : Nat.primeCounting' 547 = 100 := by
  change Nat.primeCounting 546 = 100
  have h := prime_count_smallPrimes 546 (by decide) (by decide)
  have hp : phi 546 smallPrimes = 67 := by decide
  rw [smallPrimes_length, hp] at h
  omega

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem prime_count_lt_563 : Nat.primeCounting' 563 = 102 := by
  change Nat.primeCounting 562 = 102
  have h := prime_count_smallPrimes 562 (by decide) (by decide)
  have hp : phi 562 smallPrimes = 69 := by decide
  rw [smallPrimes_length, hp] at h
  omega

end PrimeCountBands

namespace PrimeIntervalBridge

theorem floor_nat_mul_div (a b x : ℕ) :
    ⌊(a : ℝ) * (x : ℝ) / (b : ℝ)⌋₊ = a*x/b := by
  rw [← Nat.cast_mul, Nat.floor_div_natCast, Nat.floor_natCast]

theorem two_prime_count_gap (x : ℕ) (hx : 100 ≤ x) :
    Nat.primeCounting x + 2 ≤ Nat.primeCounting (5*x/4) := by
  by_cases hs : x ≤ 262144
  · obtain ⟨p,q,hp,hq,hxp,hpq,hq'⟩ := two_primes_short_interval_finite x hx hs
    exact two_primes_imply_count_gap x (5*x/4) p q hp hq hxp hpq (by omega)
  · have hxr : (262144 : ℝ) ≤ (x : ℝ) := by exact_mod_cast (show 262144 ≤ x by omega)
    have hfloor : ⌊5 * (x : ℝ) / 4⌋₊ = 5*x/4 := by
      simpa only [Nat.cast_ofNat] using floor_nat_mul_div 5 4 x
    simpa only [Nat.floor_natCast, hfloor] using
      Chebyshev.primeCounting_gap_large (x : ℝ) hxr

theorem prime_count_ratio (x : ℕ) (hx : 500 ≤ x) :
    5 * Nat.primeCounting x < 4 * Nat.primeCounting (48*x/25) := by
  by_cases hs : x ≤ 16384
  · exact PrimeCountBands.prime_count_ratio_finite x hx hs
  · have hxr : (16384 : ℝ) ≤ (x : ℝ) := by exact_mod_cast (show 16384 ≤ x by omega)
    have hfloor : ⌊48 * (x : ℝ) / 25⌋₊ = 48*x/25 := by
      simpa only [Nat.cast_ofNat] using floor_nat_mul_div 48 25 x
    simpa only [Nat.floor_natCast, hfloor] using
      Chebyshev.primeCounting_ratio_refined (x : ℝ) hxr

end PrimeIntervalBridge


/- Generic transfer of a count estimate through a strictly increasing sequence.
The standing count convention is g(f n) = n. -/
namespace CountTransfer

theorem double_index_lt_local
    (f g : ℕ → ℕ) (hf : ∀ {m n}, 1 ≤ m → m < n → f m < f n)
    (k A B C D : ℕ) (hB : 0 < B) (hD : 0 < D)
    (hkstep : 1 ≤ f (k+2))
    (hcount1 : g (f k) = k) (hcount2 : g (f (f k)) = f k)
    (hindex : ∀ n x, 0 < n → n ≤ g x → f n ≤ x)
    (hgap : g (f k) + 2 ≤ g (A * f k / B))
    (hratio : A * g (f (f k)) < B * g (C * f (f k) / D)) :
    D * f (f (k + 2)) < C * f (f k) := by
  rw [hcount1] at hgap
  have hle := hindex (k + 2) (A * f k / B) (by omega) hgap
  rw [hcount2] at hratio
  have hlt : A * f k / B < g (C * f (f k) / D) := by
    exact (Nat.div_lt_iff_lt_mul hB).mpr (by simpa [Nat.mul_comm] using hratio)
  have hstep : f (k + 2) + 1 ≤ g (C * f (f k) / D) := by omega
  have hbound := hindex (f (k + 2) + 1) (C * f (f k) / D) (by omega) hstep
  have hl : f (f (k + 2)) < C * f (f k) / D :=
    (hf hkstep (Nat.lt_succ_self _)).trans_le hbound
  have hdiv : f (f (k + 2)) * D < C * f (f k) := by
    have hm := Nat.mul_lt_mul_of_pos_right hl hD
    exact hm.trans_le (Nat.div_mul_le_self _ _)
  simpa [Nat.mul_comm] using hdiv

theorem double_index_lt
    (f g : ℕ → ℕ) (hf : StrictMono f)
    (hcount : ∀ n, g (f n) = n)
    (hindex : ∀ n x, n ≤ g x → f n ≤ x)
    (k A B C D : ℕ) (hB : 0 < B) (hD : 0 < D)
    (hgap : g (f k) + 2 ≤ g (A * f k / B))
    (hratio : A * g (f (f k)) < B * g (C * f (f k) / D)) :
    D * f (f (k + 2)) < C * f (f k) := by
  have hf' : ∀ {m n}, 1 ≤ m → m < n → f m < f n := fun _ h => hf h
  have hkstep : 1 ≤ f (k+2) := by have hh := hf (show 0 < k+2 by omega); omega
  exact double_index_lt_local f g hf' k A B C D hB hD hkstep (hcount k) (hcount (f k))
    (fun n x _ => hindex n x) hgap hratio

theorem double_index_lt_positive
    (f g : ℕ → ℕ) (hf : ∀ {m n}, 1 ≤ m → m < n → f m < f n)
    (hcount : ∀ n, 1 ≤ n → g (f n) = n)
    (hindex : ∀ n x, 1 ≤ n → n ≤ g x → f n ≤ x)
    (k A B C D : ℕ) (hB : 0 < B) (hD : 0 < D)
    (hk : 1 ≤ k) (hfk : 1 ≤ f k) (hkstep : 1 ≤ f (k+2))
    (hgap : g (f k) + 2 ≤ g (A * f k / B))
    (hratio : A * g (f (f k)) < B * g (C * f (f k) / D)) :
    D * f (f (k + 2)) < C * f (f k) := by
  exact double_index_lt_local f g hf k A B C D hB hD hkstep (hcount k hk)
    (hcount (f k) hfk) (fun n x hn => hindex n x (by omega)) hgap hratio

theorem triangle_of_ratio (x y z C D : ℕ) (hxy : x ≤ y)
    (hCD : C ≤ 2*D) (h : D*z < C*x) : z < x+y := by
  by_contra! hb
  have h1 := Nat.mul_le_mul_left D hb
  have h2 := Nat.mul_le_mul_right x hCD
  have h3 := Nat.mul_le_mul_left D hxy
  rw [Nat.mul_add] at h1
  rw [Nat.mul_assoc] at h2
  omega

theorem double_index_triangle_of_ratio
    (f : ℕ → ℕ) (hf : ∀ {m n}, 1 ≤ m → m < n → f m < f n)
    (k C D : ℕ) (hk : 1 ≤ k) (hfk : 1 ≤ f k)
    (hCD : C ≤ 2*D) (hratio : D*f (f (k+2)) < C*f (f k)) :
    f (f (k+2)) < f (f k) + f (f (k+1)) := by
  have hmono : f (f k) < f (f (k+1)) := hf hfk (hf hk (by omega))
  exact triangle_of_ratio _ _ _ C D hmono.le hCD hratio

end CountTransfer

namespace A119659

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
noncomputable def prime (n : ℕ) : ℕ := Nat.nth Nat.Prime (n - 1)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
noncomputable def pip (n : ℕ) : ℕ := prime (prime n)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
private theorem primes_infinite : {n : ℕ | n.Prime}.Infinite :=
  Nat.infinite_setOfPred_prime

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
private theorem prime_le_of_le {m n : ℕ} (h : m ≤ n) : prime m ≤ prime n := by
  unfold prime
  exact (Nat.nth_strictMono primes_infinite).monotone (by omega)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
private theorem prime_lt_of_lt {m n : ℕ} (hm : 1 ≤ m) (h : m < n) :
    prime m < prime n := by
  unfold prime
  exact Nat.nth_strictMono primes_infinite (by omega)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
private theorem prime_eq_of_count {n p : ℕ}
    (hc : Nat.count Nat.Prime p = n - 1) (hp : p.Prime) : prime n = p := by
  unfold prime
  rw [← hc, Nat.nth_count hp]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
private theorem prime_count_eq (n : ℕ) (hn : 1 ≤ n) : Nat.primeCounting (prime n) = n := by
  unfold prime
  change Nat.count Nat.Prime (Nat.nth Nat.Prime (n - 1) + 1) = n
  rw [Nat.count_nth_succ_of_infinite primes_infinite (n - 1)]
  omega

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
private theorem prime_le_of_count (n x : ℕ) (hn : 1 ≤ n)
    (h : n ≤ Nat.primeCounting x) : prime n ≤ x := by
  have hc : n - 1 < Nat.count Nat.Prime (x + 1) := by
    change n - 1 < Nat.primeCounting x
    omega
  have hp : prime n < x + 1 := Nat.nth_lt_of_lt_count hc
  omega

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
@[local simp] private theorem prime_1 : prime 1 = 2 := by apply prime_eq_of_count <;> decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
@[local simp] private theorem prime_2 : prime 2 = 3 := by apply prime_eq_of_count <;> decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
@[local simp] private theorem prime_3 : prime 3 = 5 := by apply prime_eq_of_count <;> decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
@[local simp] private theorem prime_4 : prime 4 = 7 := by apply prime_eq_of_count <;> decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
@[local simp] private theorem prime_5 : prime 5 = 11 := by apply prime_eq_of_count <;> decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
@[local simp] private theorem prime_6 : prime 6 = 13 := by apply prime_eq_of_count <;> decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
@[local simp] private theorem prime_7 : prime 7 = 17 := by apply prime_eq_of_count <;> decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
@[local simp] private theorem prime_8 : prime 8 = 19 := by apply prime_eq_of_count <;> decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
@[local simp] private theorem prime_9 : prime 9 = 23 := by apply prime_eq_of_count <;> decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
@[local simp] private theorem prime_10 : prime 10 = 29 := by apply prime_eq_of_count <;> decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
@[local simp] private theorem prime_11 : prime 11 = 31 := by apply prime_eq_of_count <;> decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
@[local simp] private theorem prime_12 : prime 12 = 37 := by apply prime_eq_of_count <;> decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
@[local simp] private theorem prime_13 : prime 13 = 41 := by apply prime_eq_of_count <;> decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
@[local simp] private theorem prime_14 : prime 14 = 43 := by apply prime_eq_of_count <;> decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
@[local simp] private theorem prime_15 : prime 15 = 47 := by apply prime_eq_of_count <;> decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
@[local simp] private theorem prime_16 : prime 16 = 53 := by apply prime_eq_of_count <;> decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
@[local simp] private theorem prime_17 : prime 17 = 59 := by apply prime_eq_of_count <;> decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
@[local simp] private theorem prime_18 : prime 18 = 61 := by apply prime_eq_of_count <;> decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
@[local simp] private theorem prime_19 : prime 19 = 67 := by apply prime_eq_of_count <;> decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
@[local simp] private theorem prime_20 : prime 20 = 71 := by apply prime_eq_of_count <;> decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
@[local simp] private theorem prime_21 : prime 21 = 73 := by apply prime_eq_of_count <;> decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
@[local simp] private theorem prime_22 : prime 22 = 79 := by apply prime_eq_of_count <;> decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
@[local simp] private theorem prime_23 : prime 23 = 83 := by apply prime_eq_of_count <;> decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
@[local simp] private theorem prime_24 : prime 24 = 89 := by apply prime_eq_of_count <;> decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
@[local simp] private theorem prime_25 : prime 25 = 97 := by apply prime_eq_of_count <;> decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
@[local simp] private theorem prime_26 : prime 26 = 101 := by apply prime_eq_of_count <;> decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
@[local simp] private theorem prime_27 : prime 27 = 103 := by apply prime_eq_of_count <;> decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
@[local simp] private theorem prime_29 : prime 29 = 109 := by apply prime_eq_of_count <;> decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
@[local simp] private theorem prime_31 : prime 31 = 127 := by apply prime_eq_of_count <;> decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
@[local simp] private theorem prime_37 : prime 37 = 157 := by
  exact prime_eq_of_count PrimeCountBands.prime_count_lt_157 (by norm_num)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
@[local simp] private theorem prime_41 : prime 41 = 179 := by
  exact prime_eq_of_count PrimeCountBands.prime_count_lt_179 (by norm_num)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
@[local simp] private theorem prime_43 : prime 43 = 191 := by
  exact prime_eq_of_count PrimeCountBands.prime_count_lt_191 (by norm_num)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
@[local simp] private theorem prime_47 : prime 47 = 211 := by
  exact prime_eq_of_count PrimeCountBands.prime_count_lt_211 (by norm_num)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
@[local simp] private theorem prime_53 : prime 53 = 241 := by
  exact prime_eq_of_count PrimeCountBands.prime_count_lt_241 (by norm_num)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
@[local simp] private theorem prime_59 : prime 59 = 277 := by
  exact prime_eq_of_count PrimeCountBands.prime_count_lt_277 (by norm_num)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
@[local simp] private theorem prime_61 : prime 61 = 283 := by
  exact prime_eq_of_count PrimeCountBands.prime_count_lt_283 (by norm_num)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
@[local simp] private theorem prime_67 : prime 67 = 331 := by
  exact prime_eq_of_count PrimeCountBands.prime_count_lt_331 (by norm_num)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
@[local simp] private theorem prime_71 : prime 71 = 353 := by
  exact prime_eq_of_count PrimeCountBands.prime_count_lt_353 (by norm_num)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
@[local simp] private theorem prime_73 : prime 73 = 367 := by
  exact prime_eq_of_count PrimeCountBands.prime_count_lt_367 (by norm_num)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
@[local simp] private theorem prime_79 : prime 79 = 401 := by
  exact prime_eq_of_count PrimeCountBands.prime_count_lt_401 (by norm_num)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
@[local simp] private theorem prime_83 : prime 83 = 431 := by
  exact prime_eq_of_count PrimeCountBands.prime_count_lt_431 (by norm_num)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
@[local simp] private theorem prime_89 : prime 89 = 461 := by
  exact prime_eq_of_count PrimeCountBands.prime_count_lt_461 (by norm_num)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
@[local simp] private theorem prime_97 : prime 97 = 509 := by
  exact prime_eq_of_count PrimeCountBands.prime_count_lt_509 (by norm_num)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
@[local simp] private theorem prime_100 : prime 100 = 541 := by
  exact prime_eq_of_count PrimeCountBands.prime_count_lt_541 (by norm_num)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
@[local simp] private theorem prime_101 : prime 101 = 547 := by
  exact prime_eq_of_count PrimeCountBands.prime_count_lt_547 (by norm_num)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
@[local simp] private theorem prime_103 : prime 103 = 563 := by
  exact prime_eq_of_count PrimeCountBands.prime_count_lt_563 (by norm_num)



set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem stronger_from_counts
    (hG : ∀ x : ℕ, 100 ≤ x → Nat.primeCounting x + 2 ≤ Nat.primeCounting (5*x/4))
    (hR : ∀ y : ℕ, 500 ≤ y → 5*Nat.primeCounting y < 4*Nat.primeCounting (48*y/25)) :
    ∀ k : ℕ, 5 ≤ k → 25*pip (k+2) < 48*pip k := by
  intro k hk
  by_cases hs : k ≤ 25
  · interval_cases k <;> norm_num [pip]
  · have hk26 : 26 ≤ k := by omega
    have hm : 100 ≤ prime k := by
      have h := prime_le_of_le hk26
      rw [prime_26] at h
      omega
    have hq : prime 100 ≤ prime (prime k) := prime_le_of_le hm
    rw [prime_100] at hq
    have hy : 500 ≤ pip k := by
      change 500 ≤ prime (prime k)
      omega
    have hmono : prime k ≤ prime (k+2) := prime_le_of_le (by omega)
    exact CountTransfer.double_index_lt_positive prime Nat.primeCounting prime_lt_of_lt
      prime_count_eq prime_le_of_count k 5 4 48 25 (by decide) (by decide)
      (by omega) (by omega) (by omega) (hG (prime k) hm) (hR (pip k) hy)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem main_from_counts
    (hG : ∀ x : ℕ, 100 ≤ x → Nat.primeCounting x + 2 ≤ Nat.primeCounting (5*x/4))
    (hR : ∀ y : ℕ, 500 ≤ y → 5*Nat.primeCounting y < 4*Nat.primeCounting (48*y/25)) :
    ∀ k : ℕ, 1 ≤ k → (pip k + pip (k+1) ≤ pip (k+2) ↔ k=1 ∨ k=2 ∨ k=3) := by
  intro k hk
  by_cases hs : k ≤ 4
  · interval_cases k <;> norm_num [pip]
  · have hstrong := stronger_from_counts hG hR k (by omega)
    have hm : pip k ≤ pip (k+1) := prime_le_of_le (prime_le_of_le (by omega))
    constructor <;> intro h <;> omega

/- Unconditional strengthening of the claimed result. -/
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem ratio_bound (k : ℕ) (hk : 5 ≤ k) : 25*pip (k+2) < 48*pip k :=
  stronger_from_counts PrimeIntervalBridge.two_prime_count_gap PrimeIntervalBridge.prime_count_ratio k hk

/- Precisely the first three positive indices fail the triangle inequality. -/
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem main : ∀ k : ℕ, 1 ≤ k →
    (pip k + pip (k+1) ≤ pip (k+2) ↔ k=1 ∨ k=2 ∨ k=3) :=
  main_from_counts PrimeIntervalBridge.two_prime_count_gap PrimeIntervalBridge.prime_count_ratio

end A119659

theorem OMA.solution : type_of% @OMA.S_oeis_a119659.main := by
  simpa only [OMA.S_oeis_a119659.pip, OMA.S_oeis_a119659.prime,
    A119659.pip, A119659.prime] using A119659.main
