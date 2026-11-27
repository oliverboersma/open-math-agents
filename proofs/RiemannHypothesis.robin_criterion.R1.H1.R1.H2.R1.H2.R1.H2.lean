import OMAReductions.R_RiemannHypothesis_robin_criterion_R1_H1_R1_H2_R1_H2_R1
import Mathlib

/- Copyright (c) 2026 Jonas Whidden. All rights reserved.
Ported from kimihiro64/Robin1984 at e3697139babfe0f6cc7a76a08bf41a92aa7a2978
under Apache-2.0: ZeroConstantBound, ExplicitLogBounds, PrimePowerFirstWeightBounds,
LargeHeightExplicitBounds, WeightedPsiError, and PrimeCostExplicitCoefficient. -/
namespace Robin1984
noncomputable section
theorem robin_log_two_lower : (69314 / 100000 : Real) <= Real.log 2 := by
  have h := Real.sum_range_le_log_div (x := (1 / 3 : Real)) (by norm_num) (by norm_num) 5
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem robin_log_four_pi_lower : (253 / 100 : Real) <= Real.log (4 * Real.pi) := by
  have hSmall := Real.sum_range_le_log_div (x := (57 / 257 : Real)) (by norm_num) (by norm_num) 2
  norm_num [Finset.sum_range_succ] at hSmall
  have hArg : (8 : Real) * (157 / 100) <= 4 * Real.pi := by linarith [Real.pi_gt_d2]
  have hLog := Real.log_le_log (by norm_num : (0 : Real) < 8 * (157 / 100)) hArg
  rw [Real.log_mul (by norm_num : Not ((8 : Real) = 0))
    (by norm_num : Not ((157 / 100 : Real) = 0))] at hLog
  have hEight : Real.log (8 : Real) = 3 * Real.log 2 := by
    rw [show (8 : Real) = 2^3 by norm_num, Real.log_pow]
    norm_num
  rw [hEight] at hLog
  linarith [robin_log_two_lower]

set_option maxRecDepth 2048 in
theorem robin_harmonic_256_upper : (harmonic 256 : Real) <= (15311 / 2500 : Real) := by
  have hRat : harmonic 256 <= (15311 / 2500 : Rat) := by
    norm_num [harmonic, Finset.sum_range_succ]
  have hCast : (harmonic 256 : Real) <= ((15311 / 2500 : Rat) : Real) :=
    Rat.cast_mono hRat
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hCast
  exact hCast

theorem robin_zero_constant_le_one_twentieth :
    Real.eulerMascheroniConstant + 2 - Real.log (4 * Real.pi) <= (1 / 20 : Real) := by
  have hGamma := Real.eulerMascheroniConstant_lt_eulerMascheroniSeq' 256
  change Real.eulerMascheroniConstant < (harmonic 256 : Real) - Real.log (256 : Real) at hGamma
  have hLog256 : Real.log (256 : Real) = 8 * Real.log 2 := by
    rw [show (256 : Real) = 2^8 by norm_num, Real.log_pow]
    norm_num
  rw [hLog256] at hGamma
  linarith [robin_harmonic_256_upper, robin_log_two_lower, robin_log_four_pi_lower]

theorem robin_log_two_upper : Real.log 2 <= (69315 / 100000 : Real) := by
  have h := Real.log_div_le_sum_range_add (x := (1 / 3 : Real)) (by norm_num) (by norm_num) 6
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem robin_log_ten_bounds :
    And ((23 / 10 : Real) <= Real.log 10) (Real.log 10 <= (288 / 125 : Real)) := by
  have hLow := Real.sum_range_le_log_div (x := (1 / 9 : Real)) (by norm_num) (by norm_num) 2
  have hHigh := Real.log_div_le_sum_range_add (x := (1 / 9 : Real)) (by norm_num) (by norm_num) 2
  norm_num [Finset.sum_range_succ] at hLow hHigh
  have hTen : Real.log (10 : Real) = 3 * Real.log 2 + Real.log (5 / 4) := by
    rw [show (10 : Real) = 2^3 * (5 / 4) by norm_num,
      Real.log_mul (by norm_num : Not ((2 : Real)^3 = 0))
        (by norm_num : Not ((5 / 4 : Real) = 0)), Real.log_pow]
    norm_num
  constructor <;> linarith [robin_log_two_lower, robin_log_two_upper]

theorem robin_log_149_div_20_bounds :
    And ((2 : Real) <= Real.log (149 / 20 : Real))
      (Real.log (149 / 20 : Real) <= (201 / 100 : Real)) := by
  have hLow := Real.sum_range_le_log_div
    (x := (129 / 169 : Real)) (by norm_num) (by norm_num) 15
  have hHigh := Real.log_div_le_sum_range_add
    (x := (129 / 169 : Real)) (by norm_num) (by norm_num) 15
  norm_num [Finset.sum_range_succ] at hLow hHigh
  constructor <;> linarith

theorem robin_log_74500_bounds :
    And ((56 / 5 : Real) <= Real.log 74500)
      (Real.log 74500 <= (1123 / 100 : Real)) := by
  have hEq : Real.log (74500 : Real) =
      4 * Real.log 10 + Real.log (149 / 20 : Real) := by
    rw [show (74500 : Real) = 10^4 * (149 / 20) by norm_num,
      Real.log_mul (by norm_num : Not ((10 : Real)^4 = 0))
        (by norm_num : Not ((149 / 20 : Real) = 0)), Real.log_pow]
    norm_num
  rw [hEq]
  constructor
  . linarith [robin_log_ten_bounds.1, robin_log_149_div_20_bounds.1]
  . linarith [robin_log_ten_bounds.2, robin_log_149_div_20_bounds.2]

theorem robin_log_two_pi_upper :
    Real.log (2 * Real.pi) <= (46 / 25 : Real) := by
  have hSeries := Real.log_div_le_sum_range_add
    (x := (1651 / 2276 : Real)) (by norm_num) (by norm_num) 12
  norm_num [Finset.sum_range_succ] at hSeries
  have hArg : 2 * Real.pi <= (3927 / 625 : Real) := by
    linarith [Real.pi_lt_d4]
  have hLog := Real.log_le_log
    (mul_pos (by norm_num : (0 : Real) < 2) Real.pi_pos) hArg
  linarith

theorem robin_rpow_neg_div_le_of_pow
    {x b : Real} {a d : Nat} (hx : 0 < x) (hb : 0 <= b) (hd : 0 < d)
    (h : 1 <= b^d * x^a) : x^(-((a : Real) / (d : Real))) <= b := by
  have hdPos : (0 : Real) < d := by exact_mod_cast hd
  apply (Real.rpow_le_rpow_iff (Real.rpow_nonneg hx.le _) hb hdPos).mp
  rw [<- Real.rpow_mul hx.le]
  have hExp : (-((a : Real) / (d : Real))) * (d : Real) = -(a : Real) := by
    field_simp
  rw [hExp, Real.rpow_neg hx.le, Real.rpow_natCast, Real.rpow_natCast]
  have hPos := pow_pos hx a
  have hCancel : Inv.inv (x^a) * x^a = 1 := by field_simp
  nlinarith

theorem robin_log_mul_rpow_neg_le
    {b x r : Real} (hb : 1 < b) (hbx : b <= x) (hr : 0 < r)
    (hStart : 1 <= r * Real.log b) :
    Real.log x * x^(-r) <= Real.log b * b^(-r) := by
  have hbPos : 0 < b := by linarith
  have hxPos : 0 < x := by linarith
  let t : Real := (x / b)^r
  have ht : 1 <= t := Real.one_le_rpow ((one_le_div hbPos).mpr hbx) hr.le
  have htPos : 0 < t := by linarith
  have hLogT : Real.log t = r * (Real.log x - Real.log b) := by
    dsimp [t]
    rw [Real.log_rpow (div_pos hxPos hbPos), Real.log_div hxPos.ne' hbPos.ne']
  have hLog := Real.log_le_sub_one_of_pos htPos
  have hFirst : Real.log x <= Real.log b * t := by nlinarith
  have hEq : t * x^(-r) = b^(-r) := by
    dsimp [t]
    rw [Real.div_rpow hxPos.le hbPos.le, Real.rpow_neg hxPos.le, Real.rpow_neg hbPos.le]
    have hXPow : Not (x^r = 0) := (Real.rpow_pos_of_pos hxPos r).ne'
    field_simp
  have h := mul_le_mul_of_nonneg_right hFirst (Real.rpow_nonneg hxPos.le (-r))
  calc
    _ <= (Real.log b * t) * x^(-r) := h
    _ = _ := by rw [mul_assoc, hEq]

theorem robin_74500_power_sixth :
    (74500 : Real)^(-(1 / 6 : Real)) <= (1549 / 10000 : Real) := by
  have h := robin_rpow_neg_div_le_of_pow (x := (74500 : Real)) (a := 1) (d := 6)
    (b := (1549 / 10000 : Real)) (by norm_num) (by norm_num) (by omega) (by norm_num)
  norm_num at h
  exact h

theorem robin_log_times_sixth_power_bound {H : Real} (hH : 74500 <= H) :
    Real.log H * H^(-(1 / 6 : Real)) <= (87 / 50 : Real) := by
  have hMono := robin_log_mul_rpow_neg_le (b := (74500 : Real)) (by norm_num) hH
    (r := (1 / 6 : Real)) (by norm_num)
    (by nlinarith [robin_log_74500_bounds.1])
  have hProduct : Real.log (74500 : Real) * (74500 : Real)^(-(1 / 6 : Real)) <=
      (1123 / 100 : Real) * (1549 / 10000 : Real) := by
    exact mul_le_mul robin_log_74500_bounds.2 robin_74500_power_sixth
      (Real.rpow_nonneg (by norm_num : (0 : Real) <= 74500) _)
      (by norm_num : (0 : Real) <= 1123 / 100)
  nlinarith

theorem robin_large_height_log_and_powers {H : Real} (hH : 74500 <= H) :
    And ((56 / 5 : Real) <= Real.log H)
      (And (H^(-(1 / 4 : Real)) <= (61 / 1000 : Real))
        (H^(-(1 / 2 : Real)) <= (1 / 272 : Real))) := by
  have hHPos : 0 < H := by linarith
  have hLog := Real.log_le_log (by norm_num : (0 : Real) < 74500) hH
  have hQuarter := robin_rpow_neg_div_le_of_pow (a := 1) (d := 4) (b := (61 / 1000 : Real))
    hHPos (by norm_num) (by omega) (by norm_num; linarith)
  have hHalf := robin_rpow_neg_div_le_of_pow (a := 1) (d := 2) (b := (1 / 272 : Real))
    hHPos (by norm_num) (by omega) (by norm_num; linarith)
  norm_num at hQuarter hHalf
  exact And.intro (robin_log_74500_bounds.1.trans hLog) (And.intro hQuarter hHalf)

theorem robin_sqrt_two_lower : (7071 / 5000 : Real) <= Real.sqrt 2 := by
  have hSquare := Real.sq_sqrt (by norm_num : (0 : Real) <= 2)
  have hNonneg := Real.sqrt_nonneg (2 : Real)
  nlinarith

theorem robin_fourth_root_two_upper : (2 : Real)^(1 / 4 : Real) <= (119 / 100 : Real) := by
  apply (Real.rpow_le_rpow_iff (by positivity) (by norm_num) (by norm_num : (0 : Real) < 4)).mp
  rw [<- Real.rpow_mul (by norm_num : (0 : Real) <= 2)]
  norm_num [Real.rpow_natCast]

def robinPsiWeightedErrorScalar (n : Nat) (x : Real) : Real :=
  (Real.eulerMascheroniConstant + 2 - Real.log (4 * Real.pi)) *
    (x ^ ((1 / 2 : Real) - (n : Real)) * Inv.inv (Real.log x) *
      ((n : Real) + Inv.inv (Real.log x) +
        4 * Inv.inv (((2 * n - 1 : Nat) : Real) * (Real.log x)^2)))

theorem robin_large_log_ratios {H : Real} (hH : 74500 <= H) :
    And ((16 / 17 : Real) <= Real.log H / (Real.log H + Real.log 2))
      (And (Real.log H / (Real.log H + Real.log 2) <= 1)
        (And (Inv.inv (Real.log H + Real.log 2) <= (17 / 202 : Real))
          (Real.log H / (Real.log H - Real.log 2) <= (107 / 100 : Real)))) := by
  have hL := (robin_large_height_log_and_powers hH).1
  have hTwoLower : (69 / 100 : Real) <= Real.log 2 := by linarith [robin_log_two_lower]
  have hTwoUpper : Real.log 2 <= (7 / 10 : Real) := by linarith [robin_log_two_upper]
  have hPlus : 0 < Real.log H + Real.log 2 := by linarith
  have hMinus : 0 < Real.log H - Real.log 2 := by linarith
  have hUeq : (Real.log H / (Real.log H + Real.log 2)) *
      (Real.log H + Real.log 2) = Real.log H := by field_simp
  have hWeq : (Real.log H / (Real.log H - Real.log 2)) *
      (Real.log H - Real.log 2) = Real.log H := by field_simp
  have hUlo : (16 / 17 : Real) <= Real.log H / (Real.log H + Real.log 2) := by
    nlinarith
  have hUhi : Real.log H / (Real.log H + Real.log 2) <= 1 := by
    apply (div_le_one hPlus).mpr
    linarith
  have hV := one_div_le_one_div_of_le (by norm_num : (0 : Real) < 202 / 17)
    (show (202 / 17 : Real) <= Real.log H + Real.log 2 by linarith)
  norm_num only [one_div, inv_div, inv_inv] at hV
  have hW : Real.log H / (Real.log H - Real.log 2) <= (107 / 100 : Real) := by
    nlinarith
  exact And.intro hUlo (And.intro hUhi (And.intro hV hW))

theorem robin_prime_cost_products {H : Real} (hH : 74500 <= H) :
    And
      (H^(-(1 / 4 : Real)) * (Real.log H / (Real.log H + Real.log 2)) <=
        (573 / 10000 : Real))
      (And
        (H^(-(1 / 2 : Real)) * (Real.log H / (Real.log H + Real.log 2)) <=
          (7 / 2000 : Real))
        (H^(-(1 / 2 : Real)) * (Real.log H / (Real.log H - Real.log 2)) <=
          (197 / 50000 : Real))) := by
  have hHPos : 0 < H := by linarith
  have hRatios := robin_large_log_ratios hH
  have hQuarterAtCutoff :
      (74500 : Real)^(-(1 / 4 : Real)) <= (303 / 5000 : Real) := by
    have h := robin_rpow_neg_div_le_of_pow
      (x := (74500 : Real)) (a := 1) (d := 4) (b := (303 / 5000 : Real))
      (by norm_num) (by norm_num) (by omega) (by norm_num)
    norm_num at h
    exact h
  have hQuarterMono := robin_log_mul_rpow_neg_le
    (b := (74500 : Real)) (by norm_num) hH
    (r := (1 / 4 : Real)) (by norm_num)
    (by nlinarith [robin_log_74500_bounds.1])
  have hQuarterNumerator : Real.log H * H^(-(1 / 4 : Real)) <=
      (1123 / 100 : Real) * (303 / 5000 : Real) := by
    have hAtCutoff : Real.log (74500 : Real) * (74500 : Real)^(-(1 / 4 : Real)) <=
        (1123 / 100 : Real) * (303 / 5000 : Real) := by
      exact mul_le_mul robin_log_74500_bounds.2 hQuarterAtCutoff
        (Real.rpow_nonneg (by norm_num : (0 : Real) <= 74500) _)
        (by norm_num : (0 : Real) <= 1123 / 100)
    exact hQuarterMono.trans hAtCutoff
  have hHalfMono := robin_log_mul_rpow_neg_le
    (b := (74500 : Real)) (by norm_num) hH
    (r := (1 / 2 : Real)) (by norm_num)
    (by nlinarith [robin_log_74500_bounds.1])
  have hHalfNumerator : Real.log H * H^(-(1 / 2 : Real)) <=
      (1123 / 100 : Real) * (1 / 272 : Real) := by
    have hAtCutoff : Real.log (74500 : Real) * (74500 : Real)^(-(1 / 2 : Real)) <=
        (1123 / 100 : Real) * (1 / 272 : Real) := by
      exact mul_le_mul robin_log_74500_bounds.2
        ((robin_large_height_log_and_powers (show (74500 : Real) <= 74500 by norm_num)).2.2)
        (Real.rpow_nonneg (by norm_num : (0 : Real) <= 74500) _)
        (by norm_num : (0 : Real) <= 1123 / 100)
    exact hHalfMono.trans hAtCutoff
  have hPlus : 0 < Real.log H + Real.log 2 := by
    nlinarith [(robin_large_height_log_and_powers hH).1, robin_log_two_lower]
  have hMinus : 0 < Real.log H - Real.log 2 := by
    nlinarith [(robin_large_height_log_and_powers hH).1, robin_log_two_upper]
  have hW : 0 <= Real.log H / (Real.log H - Real.log 2) := by
    exact div_nonneg (Real.log_nonneg (by linarith)) hMinus.le
  have hQuarterEq : H^(-(1 / 4 : Real)) *
      (Real.log H / (Real.log H + Real.log 2)) =
      (Real.log H * H^(-(1 / 4 : Real))) * Inv.inv (Real.log H + Real.log 2) := by
    field_simp
  have hHalfEq : H^(-(1 / 2 : Real)) *
      (Real.log H / (Real.log H + Real.log 2)) =
      (Real.log H * H^(-(1 / 2 : Real))) * Inv.inv (Real.log H + Real.log 2) := by
    field_simp
  have hQuarter : H^(-(1 / 4 : Real)) *
      (Real.log H / (Real.log H + Real.log 2)) <= (573 / 10000 : Real) := by
    rw [hQuarterEq]
    calc
      _ <= ((1123 / 100 : Real) * (303 / 5000 : Real)) * (17 / 202 : Real) := by
        exact mul_le_mul hQuarterNumerator hRatios.2.2.1 (inv_nonneg.mpr hPlus.le)
          (by positivity)
      _ <= _ := by norm_num
  have hHalf : H^(-(1 / 2 : Real)) *
      (Real.log H / (Real.log H + Real.log 2)) <= (7 / 2000 : Real) := by
    rw [hHalfEq]
    calc
      _ <= ((1123 / 100 : Real) * (1 / 272 : Real)) * (17 / 202 : Real) := by
        exact mul_le_mul hHalfNumerator hRatios.2.2.1 (inv_nonneg.mpr hPlus.le)
          (by positivity)
      _ <= _ := by norm_num
  have hFar : H^(-(1 / 2 : Real)) *
      (Real.log H / (Real.log H - Real.log 2)) <= (197 / 50000 : Real) := by
    calc
      _ <= (1 / 272 : Real) * (107 / 100 : Real) := by
        exact mul_le_mul (robin_large_height_log_and_powers hH).2.2 hRatios.2.2.2
          hW (by norm_num)
      _ <= _ := by norm_num
  exact And.intro hQuarter (And.intro hHalf hFar)

def robinPrimeCostNormalized (H : Real) : Real :=
  2 * Real.sqrt 2 * (Real.log H / (Real.log H + Real.log 2)) *
      (1 - Inv.inv (Real.log H + Real.log 2)) -
    (9 / 4 : Real) * (2 : Real)^(1 / 4 : Real) * H^(-(1 / 4 : Real)) *
      (Real.log H / (Real.log H + Real.log 2)) -
    Real.log (2 * Real.pi) * H^(-(1 / 2 : Real)) *
      (Real.log H / (Real.log H + Real.log 2)) -
    4 * H^(-(1 / 2 : Real)) *
      (Real.log H / (Real.log H - Real.log 2)) -
    (Real.eulerMascheroniConstant + 2 - Real.log (4 * Real.pi)) *
      (2 * Real.sqrt 2) * H^(-(1 : Real)) *
      (Real.log H / (Real.log H - Real.log 2)) *
      (2 + Inv.inv (Real.log H - Real.log 2) +
        (4 / 3 : Real) * (Inv.inv (Real.log H - Real.log 2))^2)

theorem robinPrimeCostNormalized_ge
    {H : Real} (hH : 74500 <= H) :
    (113 / 50 : Real) <= robinPrimeCostNormalized H := by
  have hHPos : 0 < H := by linarith
  have hData := robin_large_height_log_and_powers hH
  have hRatios := robin_large_log_ratios hH
  have hProducts := robin_prime_cost_products hH
  have hLogTwoPos : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
  have hLogHPos : 0 < Real.log H := by linarith [hData.1]
  have hU : 0 <= Real.log H / (Real.log H + Real.log 2) := by positivity
  have hW : 0 <= Real.log H / (Real.log H - Real.log 2) := by
    have hMinus : 0 < Real.log H - Real.log 2 := by linarith [hData.1, robin_log_two_upper]
    positivity
  have hV : 0 <= 1 - Inv.inv (Real.log H + Real.log 2) := by linarith [hRatios.2.2.1]
  have hMain : 2 * (7071 / 5000 : Real) * (16 / 17 : Real) *
      (1 - (17 / 202 : Real)) <=
      2 * Real.sqrt 2 * (Real.log H / (Real.log H + Real.log 2)) *
        (1 - Inv.inv (Real.log H + Real.log 2)) := by
    have hOne := mul_le_mul_of_nonneg_left robin_sqrt_two_lower (by norm_num : (0 : Real) <= 2)
    have hTwo := mul_le_mul hOne hRatios.1 (by norm_num : (0 : Real) <= 16 / 17)
      (by positivity : (0 : Real) <= 2 * Real.sqrt 2)
    exact mul_le_mul hTwo (sub_le_sub_left hRatios.2.2.1 1)
      (by norm_num : (0 : Real) <= 1 - 17 / 202) (by positivity)
  have hRoot : (9 / 4 : Real) * (2 : Real)^(1 / 4 : Real) * H^(-(1 / 4 : Real)) *
      (Real.log H / (Real.log H + Real.log 2)) <=
        (9 / 4 : Real) * (119 / 100 : Real) * (573 / 10000 : Real) := by
    calc
      _ = (9 / 4 : Real) * (2 : Real)^(1 / 4 : Real) *
          (H^(-(1 / 4 : Real)) * (Real.log H / (Real.log H + Real.log 2))) := by ring
      _ <= _ := by
        have hCoeff : (9 / 4 : Real) * (2 : Real)^(1 / 4 : Real) <=
            (9 / 4 : Real) * (119 / 100 : Real) :=
          mul_le_mul_of_nonneg_left robin_fourth_root_two_upper (by norm_num)
        exact mul_le_mul hCoeff hProducts.1
          (mul_nonneg (Real.rpow_nonneg hHPos.le _) hU)
          (by positivity)
  have hPi : Real.log (2 * Real.pi) * H^(-(1 / 2 : Real)) *
      (Real.log H / (Real.log H + Real.log 2)) <=
        (46 / 25 : Real) * (7 / 2000 : Real) := by
    calc
      _ = Real.log (2 * Real.pi) *
          (H^(-(1 / 2 : Real)) * (Real.log H / (Real.log H + Real.log 2))) := by ring
      _ <= _ := by
        exact mul_le_mul robin_log_two_pi_upper hProducts.2.1
          (mul_nonneg (Real.rpow_nonneg hHPos.le _) hU)
          (by norm_num)
  have hFar : 4 * H^(-(1 / 2 : Real)) *
      (Real.log H / (Real.log H - Real.log 2)) <=
        4 * (197 / 50000 : Real) := by nlinarith [hProducts.2.2]
  have hSqrtUpper : Real.sqrt 2 <= (3 / 2 : Real) := by
    have hSquare := Real.sq_sqrt (by norm_num : (0 : Real) <= 2)
    have hNonneg := Real.sqrt_nonneg (2 : Real)
    nlinarith
  have hInvH : H^(-(1 : Real)) <= (1 / 74500 : Real) := by
    rw [Real.rpow_neg_one]
    simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0 : Real) < 74500) hH
  have hQMinus : Inv.inv (Real.log H - Real.log 2) <= (2 / 21 : Real) := by
    have hDen : (21 / 2 : Real) <= Real.log H - Real.log 2 := by
      nlinarith [hData.1, robin_log_two_upper]
    have h := one_div_le_one_div_of_le (by norm_num : (0 : Real) < 21 / 2) hDen
    norm_num only [one_div, inv_div, inv_inv] at h
    exact h
  have hQMinusNonneg : 0 <= Inv.inv (Real.log H - Real.log 2) := by
    exact inv_nonneg.mpr (by nlinarith [hData.1, robin_log_two_upper])
  have hQMinusSq : (Inv.inv (Real.log H - Real.log 2))^2 <= (2 / 21 : Real)^2 := by
    nlinarith [mul_self_le_mul_self hQMinusNonneg hQMinus]
  have hTailPoly : 2 + Inv.inv (Real.log H - Real.log 2) +
      (4 / 3 : Real) * (Inv.inv (Real.log H - Real.log 2))^2 <= (211 / 100 : Real) := by
    nlinarith
  have hTailPolyNonneg : 0 <= 2 + Inv.inv (Real.log H - Real.log 2) +
      (4 / 3 : Real) * (Inv.inv (Real.log H - Real.log 2))^2 := by positivity
  have hInvHNonneg : 0 <= H^(-(1 : Real)) :=
    Real.rpow_nonneg hHPos.le (-(1 : Real))
  have hTail :
      (Real.eulerMascheroniConstant + 2 - Real.log (4 * Real.pi)) *
        (2 * Real.sqrt 2) * H^(-(1 : Real)) *
        (Real.log H / (Real.log H - Real.log 2)) *
        (2 + Inv.inv (Real.log H - Real.log 2) +
          (4 / 3 : Real) * (Inv.inv (Real.log H - Real.log 2))^2) <=
          (1 / 10000 : Real) := by
    have hFirst := mul_le_mul_of_nonneg_right robin_zero_constant_le_one_twentieth
      (mul_nonneg (mul_nonneg (mul_nonneg (by positivity : 0 <= 2 * Real.sqrt 2)
        hInvHNonneg) hW) hTailPolyNonneg)
    have hSqrtFactor : (1 / 20 : Real) * (2 * Real.sqrt 2) <=
        (1 / 20 : Real) * (2 * (3 / 2 : Real)) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hSqrtUpper (by norm_num)) (by norm_num)
    have hWithH : (1 / 20 : Real) * (2 * Real.sqrt 2) * H^(-(1 : Real)) <=
        (1 / 20 : Real) * (2 * (3 / 2 : Real)) * (1 / 74500 : Real) := by
      exact mul_le_mul hSqrtFactor hInvH hInvHNonneg (by positivity)
    have hWithW : (1 / 20 : Real) * (2 * Real.sqrt 2) * H^(-(1 : Real)) *
        (Real.log H / (Real.log H - Real.log 2)) <=
        (1 / 20 : Real) * (2 * (3 / 2 : Real)) * (1 / 74500 : Real) *
          (107 / 100 : Real) := by
      exact mul_le_mul hWithH hRatios.2.2.2 hW (by positivity)
    have hWithPoly : (1 / 20 : Real) * (2 * Real.sqrt 2) * H^(-(1 : Real)) *
        (Real.log H / (Real.log H - Real.log 2)) *
        (2 + Inv.inv (Real.log H - Real.log 2) +
          (4 / 3 : Real) * (Inv.inv (Real.log H - Real.log 2))^2) <=
        (1 / 20 : Real) * (2 * (3 / 2 : Real)) * (1 / 74500 : Real) *
          (107 / 100 : Real) * (211 / 100 : Real) := by
      exact mul_le_mul hWithW hTailPoly hTailPolyNonneg (by positivity)
    calc
      _ <= (1 / 20 : Real) * (2 * Real.sqrt 2) * H^(-(1 : Real)) *
          (Real.log H / (Real.log H - Real.log 2)) *
          (2 + Inv.inv (Real.log H - Real.log 2) +
            (4 / 3 : Real) * (Inv.inv (Real.log H - Real.log 2))^2) := by
        simpa only [mul_assoc] using hFirst
      _ <= (1 / 20 : Real) * (2 * (3 / 2 : Real)) * (1 / 74500 : Real) *
          (107 / 100 : Real) * (211 / 100 : Real) := by
        exact hWithPoly
      _ <= _ := by norm_num
  unfold robinPrimeCostNormalized
  nlinarith

theorem robin_prime_cost_block_normalized {H : Real} (hH : 74500 <= H) :
    (let s := Real.sqrt (2 * H)
     let b := H / 2
     2 * s^(-(1 : Real)) * Inv.inv (Real.log s) -
       s^(-(1 : Real)) * Inv.inv ((Real.log s)^2) -
       (9 / 4 : Real) * s^(-(3 / 2 : Real)) * Inv.inv (Real.log s) -
       Real.log (2 * Real.pi) * s^(-(2 : Real)) * Inv.inv (Real.log s) -
       2 * b^(-(1 : Real)) * Inv.inv (Real.log b) -
       robinPsiWeightedErrorScalar 2 b) =
      (H^(-(1 / 2 : Real)) * Inv.inv (Real.log H)) *
        robinPrimeCostNormalized H := by
  have hHPos : 0 < H := by linarith
  have hLogHPos : 0 < Real.log H := Real.log_pos (by linarith)
  have hPlus : Not (Real.log H + Real.log 2 = 0) := by positivity
  have hMinus : Not (Real.log H - Real.log 2 = 0) := by
    have hL := (robin_large_height_log_and_powers hH).1
    have hU := robin_log_two_upper
    linarith
  have hRootPow (r : Real) : (Real.sqrt (2 * H))^r =
      (2 : Real)^(r / 2) * H^(r / 2) := by
    rw [Real.sqrt_eq_rpow, <- Real.rpow_mul (show 0 <= 2 * H by linarith),
      show (1 / 2 : Real) * r = r / 2 by ring,
      Real.mul_rpow (by norm_num) hHPos.le]
  have hHalfTwo : (2 : Real)^(-(1 / 2 : Real)) = Real.sqrt 2 / 2 := by
    rw [Real.rpow_neg (by norm_num : (0 : Real) <= 2), <- Real.sqrt_eq_rpow]
    have hSq := Real.sq_sqrt (by norm_num : (0 : Real) <= 2)
    have hPos := Real.sqrt_pos.mpr (by norm_num : (0 : Real) < 2)
    field_simp
    nlinarith
  have hQuarterTwo : (2 : Real)^(-(3 / 4 : Real)) =
      (2 : Real)^(1 / 4 : Real) / 2 := by
    have h := Real.rpow_add (by norm_num : (0 : Real) < 2)
      (1 / 4 : Real) (-1 : Real)
    norm_num at h
    linarith
  have hThreeQuarter : H^(-(3 / 4 : Real)) =
      H^(-(1 / 2 : Real)) * H^(-(1 / 4 : Real)) := by
    rw [<- Real.rpow_add hHPos]
    norm_num
  have hFull : H^(-(1 : Real)) =
      H^(-(1 / 2 : Real)) * H^(-(1 / 2 : Real)) := by
    rw [<- Real.rpow_add hHPos]
    norm_num
  have hThreeFull : H^(-(3 / 2 : Real)) =
      H^(-(1 / 2 : Real)) * H^(-(1 : Real)) := by
    rw [<- Real.rpow_add hHPos]
    norm_num
  have hOne : (Real.sqrt (2 * H))^(-(1 : Real)) =
      (Real.sqrt 2 / 2) * H^(-(1 / 2 : Real)) := by
    have h := hRootPow (-1)
    rw [show (-1 : Real) / 2 = -(1 / 2 : Real) by norm_num, hHalfTwo] at h
    exact h
  have hThree : (Real.sqrt (2 * H))^(-(3 / 2 : Real)) =
      ((2 : Real)^(1 / 4 : Real) / 2) *
        (H^(-(1 / 2 : Real)) * H^(-(1 / 4 : Real))) := by
    have h := hRootPow (-(3 / 2 : Real))
    rw [show (-(3 / 2 : Real)) / 2 = -(3 / 4 : Real) by norm_num,
      hQuarterTwo, hThreeQuarter] at h
    exact h
  have hTwo : (Real.sqrt (2 * H))^(-(2 : Real)) =
      (1 / 2 : Real) * H^(-(1 : Real)) := by
    have h := hRootPow (-2)
    norm_num at h
    norm_num
    exact h
  have hB : (H / 2)^(-(1 : Real)) = 2 * H^(-(1 : Real)) := by
    rw [Real.div_rpow hHPos.le (by norm_num)]
    norm_num
    ring
  have hTwoScaled : (Real.sqrt (2 * H))^(-(2 : Real)) =
      (1 / 2 : Real) *
        (H^(-(1 / 2 : Real)) * H^(-(1 / 2 : Real))) := by
    rw [hTwo, hFull]
  have hBScaled : (H / 2)^(-(1 : Real)) =
      2 * (H^(-(1 / 2 : Real)) * H^(-(1 / 2 : Real))) := by
    rw [hB, hFull]
  have hTwoThree : (2 : Real)^(-(3 / 2 : Real)) = Real.sqrt 2 / 4 := by
    rw [show (-(3 / 2 : Real)) = -(1 / 2 : Real) + (-1 : Real) by ring,
      Real.rpow_add (by norm_num : (0 : Real) < 2), hHalfTwo]
    norm_num
    ring
  have hBThree : (H / 2)^(-(3 / 2 : Real)) =
      (2 * Real.sqrt 2) * (H^(-(1 / 2 : Real)) * H^(-(1 : Real))) := by
    rw [Real.div_rpow hHPos.le (by norm_num), hTwoThree, hThreeFull]
    have hSq := Real.sq_sqrt (by norm_num : (0 : Real) <= 2)
    have hPos := Real.sqrt_pos.mpr (by norm_num : (0 : Real) < 2)
    field_simp
    nlinarith
  have hLogS : Real.log (Real.sqrt (2 * H)) =
      (1 / 2 : Real) * (Real.log H + Real.log 2) := by
    rw [Real.sqrt_eq_rpow, Real.log_rpow (show 0 < 2 * H by linarith),
      Real.log_mul (by norm_num : Not ((2 : Real) = 0)) hHPos.ne']
    ring
  have hLogB : Real.log (H / 2) = Real.log H - Real.log 2 :=
    Real.log_div hHPos.ne' (by norm_num)
  have hScalar : robinPsiWeightedErrorScalar 2 (H / 2) =
      (Real.eulerMascheroniConstant + 2 - Real.log (4 * Real.pi)) *
        ((H / 2)^(-(3 / 2 : Real)) * Inv.inv (Real.log (H / 2)) *
          (2 + Inv.inv (Real.log (H / 2)) +
            4 * Inv.inv (3 * (Real.log (H / 2))^2))) := by
    unfold robinPsiWeightedErrorScalar
    norm_num
  dsimp only
  rw [hScalar, hOne, hThree, hTwoScaled, hBScaled, hBThree, hLogS, hLogB]
  unfold robinPrimeCostNormalized
  field_simp [hLogHPos.ne', hPlus, hMinus]
  ring

end
end Robin1984

open Real Robin1984 in
theorem OMA.solution : OMA.R_RiemannHypothesis_robin_criterion_R1_H1_R1_H2_R1_H2_R1.H2 := by
  intro H hH
  have large : 74500 ≤ H := by
    have h : (2:ℝ)^30 ≤ (exp 1)^30 := by gcongr; exact exp_one_gt_two.le
    have he : (exp 1)^30 = exp 30 := by rw [← Real.exp_nat_mul]; norm_num
    rw [he] at h
    linarith
  have hpos : 0 < H := by linarith
  have hlog : 0 < log H := log_pos (by linarith)
  have hscale : 0 ≤ H^(-(1/2:ℝ)) * (log H)⁻¹ := by positivity
  have h := mul_le_mul_of_nonneg_right (robinPrimeCostNormalized_ge large) hscale
  have norm := robin_prime_cost_block_normalized large
  dsimp only at norm
  rw [mul_comm (robinPrimeCostNormalized H), ← norm] at h
  simpa only [robinPsiWeightedErrorScalar, Nat.cast_ofNat, Nat.reduceMul,
    Nat.reduceSub, Nat.cast_one, div_eq_mul_inv] using h
