import OMAStatements.S_oeis_a002457
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination

/-! Joseph M. Shunia's square-root formula for OEIS A002457.
Source: https://oeis.org/A002457/internal -/

open Finset Filter
open scoped Topology

namespace OpenMath.A002457

private theorem choose_step (a : ℝ) (k : ℕ) :
    ((k : ℝ) + 1) * Ring.choose a (k + 1) = Ring.choose a k * (a - k) := by
  simpa only [Nat.choose_succ_self_right, nsmul_eq_mul, Nat.cast_add, Nat.cast_one,
    Nat.add_sub_cancel_left, Ring.choose_one_right] using
    Ring.choose_smul_choose a (n := k + 1) (k := k) (Nat.le_succ k)

private theorem negative_half (k : ℕ) :
    (4 : ℝ) ^ k * Ring.choose (-(1 / 2) : ℝ) k = (-1 : ℝ) ^ k * k.centralBinom := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hcb : ((k : ℝ) + 1) * ((k + 1).centralBinom : ℝ) =
        2 * (2 * (k : ℝ) + 1) * k.centralBinom := by
      exact_mod_cast Nat.succ_mul_centralBinom_succ k
    apply mul_left_cancel₀ (show (k : ℝ) + 1 ≠ 0 by positivity)
    calc
      _ = (4 : ℝ) ^ k * 4 * (((k : ℝ) + 1) * Ring.choose (-(1 / 2) : ℝ) (k + 1)) := by
        rw [pow_succ (4 : ℝ)]
        ring
      _ = (-2 * (2 * (k : ℝ) + 1)) * ((4 : ℝ) ^ k * Ring.choose (-(1 / 2) : ℝ) k) := by
        rw [choose_step]
        ring
      _ = _ := by
        rw [ih, pow_succ (-1 : ℝ)]
        linear_combination ((-1 : ℝ) ^ k) * hcb

/-- Scaling by `4^k` makes every half-integer binomial coefficient integral. -/
private theorem scaled_integral (n k : ℕ) :
    ∃ z : ℤ, (z : ℝ) = (4 : ℝ) ^ k * Ring.choose ((n : ℝ) - 1 / 2) k := by
  induction n generalizing k with
  | zero =>
    refine ⟨(-1 : ℤ) ^ k * (k.centralBinom : ℤ), ?_⟩
    push_cast
    simpa using (negative_half k).symm
  | succ n ih =>
    cases k with
    | zero => exact ⟨1, by simp⟩
    | succ k =>
      obtain ⟨u, hu⟩ := ih k
      obtain ⟨v, hv⟩ := ih (k + 1)
      refine ⟨4 * u + v, ?_⟩
      push_cast
      rw [show (n : ℝ) + 1 - 1 / 2 = ((n : ℝ) - 1 / 2) + 1 by ring,
        Ring.choose_succ_succ, hu, hv, pow_succ (4 : ℝ)]
      ring

private theorem first_omitted (n : ℕ) :
    (4 : ℝ) ^ (n + 1) * Ring.choose ((n : ℝ) + 1 / 2) (n + 1) = (n + 1).centralBinom := by
  have h := Ring.choose_neg (1 / 2 : ℝ) (n + 1)
  rw [show (1 / 2 : ℝ) + ((n + 1 : ℕ) : ℝ) - 1 = (n : ℝ) + 1 / 2 by push_cast; ring,
    Units.smul_def, zsmul_eq_mul, Int.cast_negOnePow_natCast] at h
  have e := negative_half (n + 1)
  rw [h] at e
  refine mul_left_cancel₀ (pow_ne_zero (n + 1) (by norm_num : (-1 : ℝ) ≠ 0)) ?_
  linear_combination e

private theorem constant_term (n : ℕ) :
    (4 : ℝ) ^ n * Ring.choose ((n : ℝ) + 1 / 2) n = (2 * (n : ℝ) + 1) * n.centralBinom := by
  have hcb : ((n : ℝ) + 1) * ((n + 1).centralBinom : ℝ) =
      2 * (2 * (n : ℝ) + 1) * n.centralBinom := by
    exact_mod_cast Nat.succ_mul_centralBinom_succ n
  have e := choose_step ((n : ℝ) + 1 / 2) n
  have h := first_omitted n
  rw [pow_succ (4 : ℝ)] at h
  linear_combination -(2 * (4 : ℝ) ^ n) * e + (((n : ℝ) + 1) / 2) * h + (1 / 2 : ℝ) * hcb

private theorem choose_nonneg (n k : ℕ) (hk : k ≤ n + 1) :
    0 ≤ Ring.choose ((n : ℝ) + 1 / 2) k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have he := choose_step ((n : ℝ) + 1 / 2) k
    rw [← mul_nonneg_iff_of_pos_left (show 0 < (k : ℝ) + 1 by positivity), he]
    have hkn : (k : ℝ) ≤ n := by exact_mod_cast (show k ≤ n by omega)
    exact mul_nonneg (ih (by omega)) (by linarith)

private theorem truncated_binomial (n : ℕ) (t : ℝ) (ht : 0 < t) (ht' : t < 1) :
    let u := fun j : ℕ => Ring.choose ((n : ℝ) + 1 / 2) j * t ^ j
    (∑ j ∈ range (n + 1), u j) ≤ (1 + t) ^ ((n : ℝ) + 1 / 2) ∧
      (1 + t) ^ ((n : ℝ) + 1 / 2) ≤ (∑ j ∈ range (n + 1), u j) + u (n + 1) := by
  dsimp only
  let u := fun j : ℕ => Ring.choose ((n : ℝ) + 1 / 2) j * t ^ j
  have hball : t ∈ Metric.eball (0 : ℝ) 1 := by
    simpa [Metric.mem_eball, edist_dist, Real.dist_0_eq_abs, abs_of_pos ht, ENNReal.ofReal_lt_one]
      using ht'
  have hs : HasSum u ((1 + t) ^ ((n : ℝ) + 1 / 2)) := by
    simpa [u, binomialSeries, mul_comm] using
      (Real.one_add_rpow_hasFPowerSeriesOnBall_zero (a := (n : ℝ) + 1 / 2)).hasSum hball
  let v := fun k : ℕ => (-1 : ℝ) ^ k * u (n + 1 + k)
  have hstep (k : ℕ) :
      v (k + 1) = v k * (t * ((k : ℝ) + 1 / 2) / ((n + 1 + k : ℕ) + 1)) := by
    have h := choose_step ((n : ℝ) + 1 / 2) (n + 1 + k)
    have hne : ((n + 1 + k : ℕ) : ℝ) + 1 ≠ 0 := by positivity
    have hnext : Ring.choose ((n : ℝ) + 1 / 2) (n + 1 + k + 1) =
        Ring.choose ((n : ℝ) + 1 / 2) (n + 1 + k) * ((n : ℝ) + 1 / 2 - (n + 1 + k : ℕ)) /
          (((n + 1 + k : ℕ) : ℝ) + 1) := (eq_div_iff hne).2 (by simpa [mul_comm] using h)
    dsimp [v, u]
    rw [← Nat.add_assoc, hnext, pow_succ (-1 : ℝ), pow_succ t]
    push_cast
    ring
  have hv0 : 0 ≤ v 0 := by
    simpa [v, u] using mul_nonneg (choose_nonneg n (n + 1) le_rfl) (pow_nonneg ht.le (n + 1))
  have hfactor (k : ℕ) :
      0 ≤ t * ((k : ℝ) + 1 / 2) / ((n + 1 + k : ℕ) + 1) ∧
        t * ((k : ℝ) + 1 / 2) / ((n + 1 + k : ℕ) + 1) ≤ 1 := by
    refine ⟨by positivity, ?_⟩
    rw [div_le_iff₀ (by positivity)]
    push_cast
    calc
      _ ≤ 1 * ((k : ℝ) + 1 / 2) := mul_le_mul_of_nonneg_right ht'.le (by positivity)
      _ ≤ _ := by linarith [Nat.cast_nonneg (α := ℝ) n]
  have hnneg (k : ℕ) : 0 ≤ v k := by
    induction k with
    | zero => exact hv0
    | succ k ih => rw [hstep]; exact mul_nonneg ih (hfactor k).1
  have hanti : Antitone v := antitone_nat_of_succ_le fun k => by
    rw [hstep]
    exact mul_le_of_le_one_right (hnneg k) (hfactor k).2
  have hsign (k : ℕ) : (-1 : ℝ) ^ k * v k = u (n + 1 + k) := by
    simp only [v, ← mul_assoc, ← mul_pow, neg_mul_neg, one_mul, one_pow]
  have hsum : Summable (fun k : ℕ => u (n + 1 + k)) := by
    simpa only [Nat.add_comm (n + 1)] using (summable_nat_add_iff (n + 1)).2 hs.summable
  let R := ∑' k : ℕ, u (n + 1 + k)
  have hlim : Tendsto (fun m : ℕ => ∑ i ∈ range m, (-1 : ℝ) ^ i * v i) atTop (𝓝 R) := by
    simp_rw [hsign]
    exact hsum.tendsto_sum_tsum_nat
  have hlow : 0 ≤ R := by simpa using hanti.alternating_series_le_tendsto hlim 0
  have hupp : R ≤ u (n + 1) := by simpa [v] using hanti.tendsto_le_alternating_series hlim 0
  have he : (∑ j ∈ range (n + 1), u j) + R = (1 + t) ^ ((n : ℝ) + 1 / 2) := by
    simpa [R, Nat.add_comm (n + 1), hs.tsum_eq] using hs.summable.sum_add_tsum_nat_add (n + 1)
  change (∑ j ∈ range (n + 1), u j) ≤ _ ∧ _ ≤ (∑ j ∈ range (n + 1), u j) + u (n + 1)
  constructor <;> linarith

private theorem scaled_coefficient (n j : ℕ) (hj : j ≤ n) :
    ∃ c : ℕ, (c : ℝ) = (4 : ℝ) ^ n * Ring.choose ((n : ℝ) + 1 / 2) j := by
  obtain ⟨z, hz⟩ := scaled_integral (n + 1) j
  rw [show ((n + 1 : ℕ) : ℝ) - 1 / 2 = (n : ℝ) + 1 / 2 by push_cast; ring] at hz
  let w : ℤ := (4 : ℤ) ^ (n - j) * z
  have hw : (w : ℝ) = (4 : ℝ) ^ n * Ring.choose ((n : ℝ) + 1 / 2) j := by
    dsimp [w]
    push_cast
    rw [hz, ← mul_assoc, ← pow_add, Nat.sub_add_cancel hj]
  have hw' : 0 ≤ w := by
    have h : (0 : ℝ) ≤ (w : ℝ) := by
      rw [hw]
      exact mul_nonneg (by positivity) (choose_nonneg n j (by omega))
    exact_mod_cast h
  refine ⟨w.toNat, ?_⟩
  calc
    (w.toNat : ℝ) = ((w.toNat : ℤ) : ℝ) := by norm_cast
    _ = _ := by rw [Int.toNat_of_nonneg hw', hw]

private theorem indexBound (n : ℕ) (hn : 0 < n) : 2 * n + 1 < 4 ^ n := by
  induction n with
  | zero => omega
  | succ k ih =>
    by_cases hk : k = 0
    · subst k; decide
    · have h := ih (by omega)
      rw [pow_succ]
      omega

private theorem square_root_remainder (n : ℕ) (hn : 0 < n) :
    Nat.sqrt (((16 : ℕ) ^ n + 1) ^ (2 * n + 1)) % (16 ^ n) =
      (2 * n + 1) * (2 * n).choose n := by
  let B : ℕ := 16 ^ n
  let b : ℝ := B
  let d : ℝ := 4 ^ n
  let t := b⁻¹
  have hb1 : 1 < b := by
    change (1 : ℝ) < ((16 ^ n : ℕ) : ℝ)
    push_cast
    exact one_lt_pow₀ (by norm_num) hn.ne'
  have hb : 0 < b := lt_trans zero_lt_one hb1
  have hd : 1 < d := one_lt_pow₀ (by norm_num) hn.ne'
  have hdb : d ^ 2 = b := by
    change ((4 : ℝ) ^ n) ^ 2 = ((16 ^ n : ℕ) : ℝ)
    push_cast
    rw [← pow_mul, Nat.mul_comm n 2, pow_mul]
    norm_num
  have ht : 0 < t := inv_pos.mpr hb
  have ht' : t < 1 := inv_lt_one_of_one_lt₀ hb1
  let scale := d * b ^ n
  have hscale : 0 < scale := mul_pos (lt_trans zero_lt_one hd) (pow_pos hb n)
  let u := fun j : ℕ => Ring.choose ((n : ℝ) + 1 / 2) j * t ^ j
  let c (j : ℕ) : ℕ := if hj : j ≤ n then (scaled_coefficient n j hj).choose else 0
  have hc (j : ℕ) (hj : j ≤ n) : (c j : ℝ) = d * Ring.choose ((n : ℝ) + 1 / 2) j := by
    dsimp only [c]
    rw [dif_pos hj]
    exact (scaled_coefficient n j hj).choose_spec
  let S : ℕ := ∑ j ∈ range (n + 1), c j * B ^ (n - j)
  have hS : (S : ℝ) = scale * (∑ j ∈ range (n + 1), u j) := by
    simp only [S, Nat.cast_sum, Nat.cast_mul, Nat.cast_pow, mul_sum]
    apply sum_congr rfl
    intro j hj
    have hle := Nat.le_of_lt_succ (mem_range.mp hj)
    rw [hc j hle]
    change _ = d * b ^ n * (Ring.choose ((n : ℝ) + 1 / 2) j * (b⁻¹) ^ j)
    rw [inv_pow, ← div_eq_mul_inv, ← mul_div_assoc]
    apply (eq_div_iff (pow_ne_zero j hb.ne')).2
    have hp : b ^ (n - j) * b ^ j = b ^ n := by rw [← pow_add, Nat.sub_add_cancel hle]
    linear_combination d * Ring.choose ((n : ℝ) + 1 / 2) j * hp
  have hcoef : Ring.choose ((n : ℝ) + 1 / 2) (n + 1) ≤ 1 := by
    rw [← mul_le_mul_iff_of_pos_left (show 0 < (4 : ℝ) ^ (n + 1) by positivity),
      first_omitted, mul_one]
    exact_mod_cast Nat.centralBinom_le_four_pow (n + 1)
  have htail : scale * u (n + 1) < 1 := by
    calc
      _ ≤ scale * t ^ (n + 1) := by
        apply mul_le_mul_of_nonneg_left _ hscale.le
        dsimp [u]
        exact mul_le_of_le_one_left (pow_nonneg ht.le _) hcoef
      _ = d / b := by
        dsimp [scale, t]
        rw [inv_pow, pow_succ b]
        field_simp
      _ < 1 := (div_lt_one hb).2 (by
        rw [← hdb]
        simpa [pow_two] using mul_lt_mul_of_pos_right hd (lt_trans zero_lt_one hd))
  let y := scale * (1 + t) ^ ((n : ℝ) + 1 / 2)
  have hy0 : 0 ≤ y := mul_nonneg hscale.le (Real.rpow_nonneg (by positivity) _)
  obtain ⟨hlo, hhi⟩ := truncated_binomial n t ht ht'
  change (∑ j ∈ range (n + 1), u j) ≤ _ at hlo
  change _ ≤ (∑ j ∈ range (n + 1), u j) + u (n + 1) at hhi
  have hylo : (S : ℝ) ≤ y := hS.trans_le (mul_le_mul_of_nonneg_left hlo hscale.le)
  have hyhi : y < (S : ℝ) + 1 := by
    calc
      _ ≤ scale * ((∑ j ∈ range (n + 1), u j) + u (n + 1)) :=
        mul_le_mul_of_nonneg_left hhi hscale.le
      _ = (S : ℝ) + scale * u (n + 1) := by rw [mul_add, hS]
      _ < _ := by linarith
  have hysq : y ^ 2 = (((B + 1) ^ (2 * n + 1) : ℕ) : ℝ) := by
    have hp : ((1 + t) ^ ((n : ℝ) + 1 / 2)) ^ 2 = (1 + t) ^ (2 * n + 1 : ℕ) := by
      rw [← Real.rpow_mul_natCast (show 0 ≤ 1 + t by positivity),
        show ((n : ℝ) + 1 / 2) * ((2 : ℕ) : ℝ) = ((2 * n + 1 : ℕ) : ℝ) by push_cast; ring,
        Real.rpow_natCast]
    have hsp : scale ^ 2 = b ^ (2 * n + 1) := by
      dsimp [scale]
      rw [mul_pow, hdb, ← pow_mul, Nat.mul_comm n 2, pow_succ b, mul_comm b]
    have hbt : b * (1 + t) = b + 1 := by
      dsimp [t]
      rw [mul_add, mul_one, mul_inv_cancel₀ hb.ne']
    rw [show y = scale * (1 + t) ^ ((n : ℝ) + 1 / 2) by rfl,
      mul_pow, hp, hsp, ← mul_pow, hbt]
    push_cast
    rfl
  have hsqrt : S = Nat.sqrt ((B + 1) ^ (2 * n + 1)) := by
    apply Nat.eq_sqrt'.2
    have h1 := (sq_le_sq₀ (Nat.cast_nonneg S) hy0).2 hylo
    have h2 := (sq_lt_sq₀ hy0 (show 0 ≤ (S : ℝ) + 1 by positivity)).2 hyhi
    rw [hysq] at h1 h2
    exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩
  have hlast : c n = (2 * n + 1) * n.centralBinom := by
    have h := hc n le_rfl
    rw [show d = (4 : ℝ) ^ n by rfl, constant_term] at h
    exact_mod_cast h
  have hsmall : c n < B := by
    rw [hlast]
    have hfour := indexBound n hn
    calc
      _ ≤ (2 * n + 1) * 4 ^ n := Nat.mul_le_mul_left _ (Nat.centralBinom_le_four_pow n)
      _ < 4 ^ n * 4 ^ n := Nat.mul_lt_mul_of_pos_right hfour (by positivity)
      _ = B := by
        dsimp [B]
        rw [← pow_add, ← two_mul, pow_mul]
        norm_num
  have hdiv : B ∣ ∑ j ∈ range n, c j * B ^ (n - j) := by
    apply Finset.dvd_sum
    intro j hj
    have hj' := mem_range.mp hj
    have hp : B ∣ B ^ (n - j) := by
      simpa only [pow_one] using pow_dvd_pow B (show 1 ≤ n - j by omega)
    exact dvd_trans hp (dvd_mul_left _ _)
  change Nat.sqrt ((B + 1) ^ (2 * n + 1)) % B = _
  rw [← hsqrt]
  dsimp only [S]
  rw [sum_range_succ, Nat.sub_self, pow_zero, mul_one, Nat.add_mod, Nat.mod_eq_zero_of_dvd hdiv,
    zero_add, Nat.mod_mod, Nat.mod_eq_of_lt hsmall, hlast, Nat.centralBinom_eq_two_mul_choose]

/-- Shunia's formula in the original factorial form of A002457. -/
theorem main (n : ℕ) (hn : 0 < n) :
    Nat.sqrt (((16 : ℕ) ^ n + 1) ^ (2 * n + 1)) % (16 ^ n) =
      (2 * n + 1).factorial / n.factorial ^ 2 := by
  rw [square_root_remainder n hn]
  have he : (2 * n).choose n * n.factorial ^ 2 = (2 * n).factorial := by
    simpa only [pow_two, Nat.mul_assoc, show 2 * n - n = n by omega] using
      Nat.choose_mul_factorial_mul_factorial (show n ≤ 2 * n by omega)
  apply Nat.eq_div_of_mul_eq_right (pow_ne_zero 2 n.factorial_ne_zero)
  rw [Nat.mul_comm (n.factorial ^ 2), Nat.mul_assoc, he, Nat.factorial_succ]

end OpenMath.A002457

theorem OMA.solution : type_of% @OMA.S_oeis_a002457.main := by
  intro n hn
  exact OpenMath.A002457.main n hn
