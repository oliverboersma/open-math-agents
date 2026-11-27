import FormalConjectures.OEIS.«69004»
import Mathlib.NumberTheory.LegendreSymbol.ZModChar
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.NumberTheory.Divisors
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.Tactic.Ring
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Prime.Basic

/-! The explicit prime cutoff is from Anmol Sahu’s manuscript and the accompanying ChatGPT Astra handoff. The extracted sieve theorem and its proof are due to PastaPastaPasta, upstream pull request 2963, original commit bcea01aab3f3a3f6ba41afd1207183477f35bade. -/


/-!
Disproof of `OeisA69004.conjecture2.variants.without_upper_bound`.

We show that `∃ n > 1, 5 * OeisA69004.a n < Nat.primeCounting n` unconditionally by taking
`n = M₃^10`, where `M₃` is the product of a sufficiently large finite set `S` of primes
congruent to `3 (mod 4)`, and applying the Selberg sieve (via `BoundingSieve`) together with
Chebyshev's lower bound on `π(n)`, an elementary lower bound on the Selberg denominator via sums
of two squares, and the divergence of `∏_{p ≡ 3 (mod 4)} p / (p - 1)`.
-/

namespace OeisA69004Disproof

open Finset Real Filter Topology ArithmeticFunction
open scoped ArithmeticFunction.Moebius

/- ### Part 1: Divergence of ∏_{p ≡ 3 (mod 4)} p / (p - 1) -/

private def chi4 (n : ℕ) : ℝ :=
  if n % 4 = 1 then 1 else if n % 4 = 3 then -1 else 0

private lemma chi4_zero : chi4 0 = 0 := by simp [chi4]
private lemma chi4_one : chi4 1 = 1 := by simp [chi4]

private lemma chi4_mul (m n : ℕ) : chi4 (m * n) = chi4 m * chi4 n := by
  unfold chi4
  have h : (m * n) % 4 = ((m % 4) * (n % 4)) % 4 := Nat.mul_mod m n 4
  rw [h]
  have hm : m % 4 = 0 ∨ m % 4 = 1 ∨ m % 4 = 2 ∨ m % 4 = 3 := by omega
  have hn : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3 := by omega
  rcases hm with h1 | h1 | h1 | h1 <;> rcases hn with h2 | h2 | h2 | h2 <;>
    simp [h1, h2]

private lemma abs_chi4_le_one (n : ℕ) : |chi4 n| ≤ 1 := by
  unfold chi4
  split_ifs <;> norm_num

private noncomputable def rpowHom (s : ℝ) (hs : 0 < s) : ℕ →*₀ ℝ where
  toFun n := (n : ℝ) ^ (-s)
  map_zero' := by simp [Real.zero_rpow (by linarith : (-s) ≠ 0)]
  map_one' := by simp
  map_mul' m n := by
    rw [Nat.cast_mul, Real.mul_rpow (Nat.cast_nonneg m) (Nat.cast_nonneg n)]

private noncomputable def chi4RpowHom (s : ℝ) : ℕ →*₀ ℝ where
  toFun n := chi4 n * (n : ℝ) ^ (-s)
  map_zero' := by simp [chi4_zero]
  map_one' := by simp [chi4_one]
  map_mul' m n := by
    rw [chi4_mul, Nat.cast_mul, Real.mul_rpow (Nat.cast_nonneg m) (Nat.cast_nonneg n)]
    ring

private lemma summable_rpowHom {s : ℝ} (hs : 1 < s) :
    Summable (fun n : ℕ => ‖rpowHom s (by linarith) n‖) := by
  have hsum : Summable (fun n : ℕ => ((n : ℝ) ^ s)⁻¹) :=
    Real.summable_nat_rpow_inv.mpr hs
  refine hsum.congr fun n => ?_
  simp only [rpowHom, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk, Real.norm_eq_abs,
    Real.rpow_neg (Nat.cast_nonneg n)]
  exact (abs_of_nonneg (inv_nonneg.mpr (Real.rpow_nonneg (Nat.cast_nonneg n) s))).symm

private lemma summable_chi4RpowHom {s : ℝ} (hs : 1 < s) :
    Summable (fun n : ℕ => ‖chi4RpowHom s n‖) := by
  refine (summable_rpowHom hs).of_nonneg_of_le (fun _ => norm_nonneg _) fun n => ?_
  simp only [chi4RpowHom, rpowHom, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk,
    Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)]
  calc |chi4 n| * (n : ℝ) ^ (-s)
      ≤ 1 * (n : ℝ) ^ (-s) := by
        gcongr
        exact abs_chi4_le_one n
    _ = (n : ℝ) ^ (-s) := one_mul _

private lemma sum_chi4_rpow_le_one {s : ℝ} (hs : 1 < s) (M : ℕ) :
    ∑ n ∈ Finset.range (4 * M + 2), chi4 n * (n : ℝ) ^ (-s) ≤ 1 := by
  induction M with
  | zero =>
    simp [Finset.sum_range_succ, chi4]
  | succ M ih =>
    have h4 : 4 * (M + 1) + 2 = (4 * M + 2) + 4 := by omega
    rw [h4, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ]
    have hc2 : chi4 (4 * M + 2) = 0 := by
      unfold chi4
      have h1 : (4 * M + 2) % 4 ≠ 1 := by omega
      have h3 : (4 * M + 2) % 4 ≠ 3 := by omega
      simp [h1, h3]
    have hc3 : chi4 (4 * M + 2 + 1) = -1 := by
      unfold chi4
      have h1 : (4 * M + 2 + 1) % 4 ≠ 1 := by omega
      have h3 : (4 * M + 2 + 1) % 4 = 3 := by omega
      simp [h1, h3]
    have hc4 : chi4 (4 * M + 2 + 2) = 0 := by
      unfold chi4
      have h1 : (4 * M + 2 + 2) % 4 ≠ 1 := by omega
      have h3 : (4 * M + 2 + 2) % 4 ≠ 3 := by omega
      simp [h1, h3]
    have hc5 : chi4 (4 * M + 2 + 3) = 1 := by
      unfold chi4
      have h1 : (4 * M + 2 + 3) % 4 = 1 := by omega
      simp [h1]
    have hstep : ((4 * M + 2 + 3 : ℕ) : ℝ) ^ (-s) ≤ ((4 * M + 2 + 1 : ℕ) : ℝ) ^ (-s) := by
      rw [Real.rpow_neg (Nat.cast_nonneg _), Real.rpow_neg (Nat.cast_nonneg _)]
      exact inv_anti₀ (Real.rpow_pos_of_pos (by positivity) s)
        (Real.rpow_le_rpow (Nat.cast_nonneg _)
          (by exact_mod_cast (by omega : 4 * M + 2 + 1 ≤ 4 * M + 2 + 3)) (by linarith))
    have heq2 : 4 * M + 2 + 1 + 1 = 4 * M + 2 + 2 := by omega
    have heq3 : 4 * M + 2 + 1 + 1 + 1 = 4 * M + 2 + 3 := by omega
    rw [heq2, heq3, hc2, hc3, hc4, hc5]
    linarith

private lemma tsum_chi4_rpow_le_one {s : ℝ} (hs : 1 < s) :
    ∑' n : ℕ, chi4 n * (n : ℝ) ^ (-s) ≤ 1 := by
  have hsum : Summable (fun n : ℕ => chi4 n * (n : ℝ) ^ (-s)) :=
    (summable_chi4RpowHom hs).of_norm
  have htend : Tendsto (fun M : ℕ => ∑ n ∈ Finset.range (4 * M + 2), chi4 n * (n : ℝ) ^ (-s))
      atTop (𝓝 (∑' n : ℕ, chi4 n * (n : ℝ) ^ (-s))) :=
    hsum.hasSum.tendsto_sum_nat.comp
      (Filter.tendsto_atTop_mono (fun M => by omega : ∀ M : ℕ, M ≤ 4 * M + 2) tendsto_id)
  exact le_of_tendsto htend (Eventually.of_forall (sum_chi4_rpow_le_one hs))

private lemma factor_bound_mod4_eq3 {p : ℕ} (hp : p.Prime) (hp3 : p % 4 = 3)
    {s : ℝ} (hs : 1 < s) :
    (1 - (p : ℝ) ^ (-s))⁻¹ ≤ ((p : ℝ) / ((p : ℝ) - 1)) ^ 2 * (1 + (p : ℝ) ^ (-s))⁻¹ := by
  have hp_ge3 : (3 : ℝ) ≤ p := by exact_mod_cast (by have := hp.two_le; omega : 3 ≤ p)
  have hp_pos : (0 : ℝ) < p := by linarith
  have hps_pos : 0 < (p : ℝ) ^ (-s) := Real.rpow_pos_of_pos hp_pos _
  have hps_le : (p : ℝ) ^ (-s) ≤ (p : ℝ)⁻¹ := by
    rw [Real.rpow_neg hp_pos.le]
    have h1 : (p : ℝ) ^ (1 : ℝ) ≤ (p : ℝ) ^ s :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) hs.le
    rw [Real.rpow_one] at h1
    exact inv_anti₀ hp_pos h1
  have h1m : 0 < 1 - (p : ℝ) ^ (-s) := by
    have : (p : ℝ)⁻¹ ≤ 1 / 3 := by
      rw [one_div]
      exact inv_anti₀ (by norm_num) hp_ge3
    linarith
  have h1p : 0 < 1 + (p : ℝ) ^ (-s) := by linarith
  have hpm1 : 0 < (p : ℝ) - 1 := by linarith
  rw [le_mul_inv_iff₀ h1p, inv_mul_le_iff₀ h1m]
  have hnum : 1 + (p : ℝ) ^ (-s) ≤ 1 + (p : ℝ)⁻¹ := by linarith
  have hden : 1 - (p : ℝ)⁻¹ ≤ 1 - (p : ℝ) ^ (-s) := by linarith
  have hkey : 1 + (p : ℝ)⁻¹ ≤ ((p : ℝ) / ((p : ℝ) - 1)) ^ 2 * (1 - (p : ℝ)⁻¹) := by
    have hp0 : (p : ℝ) ≠ 0 := by linarith
    have hpm10 : (p : ℝ) - 1 ≠ 0 := by linarith
    field_simp
    nlinarith
  calc 1 + (p : ℝ) ^ (-s)
      ≤ 1 + (p : ℝ)⁻¹ := hnum
    _ ≤ ((p : ℝ) / ((p : ℝ) - 1)) ^ 2 * (1 - (p : ℝ)⁻¹) := hkey
    _ ≤ ((p : ℝ) / ((p : ℝ) - 1)) ^ 2 * (1 - (p : ℝ) ^ (-s)) := by gcongr
    _ = (1 - (p : ℝ) ^ (-s)) * ((p : ℝ) / ((p : ℝ) - 1)) ^ 2 := mul_comm _ _

private lemma exists_finset_primes_mod4_eq3_prod_gt (B : ℝ) :
    ∃ S : Finset ℕ, (∀ p ∈ S, p.Prime ∧ p % 4 = 3) ∧
      200000 ≤ ∏ p ∈ S, p ∧ B < ∏ p ∈ S, ((p : ℝ) / ((p : ℝ) - 1)) := by
  set C : ℝ := max (max B 200000) 1
  have hC_ge1 : 1 ≤ C := le_max_right _ _
  have hC_pos : 0 < C := by linarith
  suffices h : ∃ S : Finset ℕ, (∀ p ∈ S, p.Prime ∧ p % 4 = 3) ∧
      C < ∏ p ∈ S, ((p : ℝ) / ((p : ℝ) - 1)) by
    obtain ⟨S, hS, hprod⟩ := h
    refine ⟨S, hS, ?_, lt_of_le_of_lt (le_trans (le_max_left B 200000) (le_max_left _ 1)) hprod⟩
    have hle : ∏ p ∈ S, ((p : ℝ) / ((p : ℝ) - 1)) ≤ ((∏ p ∈ S, p : ℕ) : ℝ) := by
      rw [Nat.cast_prod]
      refine Finset.prod_le_prod (fun p hp => ?_) (fun p hp => ?_)
      · have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (hS p hp).1.two_le
        exact div_nonneg (by linarith) (by linarith)
      · have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (hS p hp).1.two_le
        rw [div_le_iff₀ (by linarith)]
        nlinarith
    have h200 : (200000 : ℝ) < ((∏ p ∈ S, p : ℕ) : ℝ) :=
      lt_of_le_of_lt (le_trans (le_max_right B 200000) (le_max_left _ 1)) (lt_of_lt_of_le hprod hle)
    exact_mod_cast h200.le
  by_contra hnot
  push Not at hnot
  have hbound : ∀ s : ℝ, 1 < s → ∑' n : ℕ, (n : ℝ) ^ (-s) ≤ 2 * C ^ 2 := by
    intro s hs
    have hs0 : 0 < s := by linarith
    have ht1 := EulerProduct.eulerProduct_completely_multiplicative (summable_rpowHom hs)
    have ht2 := EulerProduct.eulerProduct_completely_multiplicative (summable_chi4RpowHom hs)
    have hstep : ∀ N : ℕ,
        ∏ p ∈ N.primesBelow, (1 - rpowHom s hs0 p)⁻¹ ≤
        (2 * C ^ 2) * ∏ p ∈ N.primesBelow, (1 - chi4RpowHom s p)⁻¹ := by
      intro N
      set S3 := N.primesBelow.filter (fun p => p % 4 = 3)
      have hS3 : ∀ p ∈ S3, p.Prime ∧ p % 4 = 3 := fun p hp => by
        simp only [S3, mem_filter] at hp
        exact ⟨Nat.prime_of_mem_primesBelow hp.1, hp.2⟩
      have hS3_le : ∏ p ∈ S3, ((p : ℝ) / ((p : ℝ) - 1)) ≤ C := hnot S3 hS3
      have hS3_nonneg : 0 ≤ ∏ p ∈ S3, ((p : ℝ) / ((p : ℝ) - 1)) :=
        Finset.prod_nonneg fun p hp => by
          have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (hS3 p hp).1.two_le
          exact div_nonneg (by linarith) (by linarith)
      have hfactor : ∀ p ∈ N.primesBelow,
          (1 - rpowHom s hs0 p)⁻¹ ≤
            (if p = 2 then (2 : ℝ)
             else if p % 4 = 3 then ((p : ℝ) / ((p : ℝ) - 1)) ^ 2
             else 1) * (1 - chi4RpowHom s p)⁻¹ := by
        intro p hp
        have hpp : p.Prime := Nat.prime_of_mem_primesBelow hp
        simp only [rpowHom, chi4RpowHom, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk]
        by_cases hp2 : p = 2
        · subst hp2
          simp only [ite_true, Nat.cast_ofNat]
          have hchi2 : chi4 2 = 0 := by simp [chi4]
          rw [hchi2, zero_mul, sub_zero, inv_one, mul_one]
          have h2s : (2 : ℝ) ^ (-s) ≤ (2 : ℝ)⁻¹ := by
            rw [Real.rpow_neg (by norm_num)]
            have h1 : (2 : ℝ) ^ (1 : ℝ) ≤ (2 : ℝ) ^ s :=
              Real.rpow_le_rpow_of_exponent_le (by norm_num) hs.le
            rw [Real.rpow_one] at h1
            exact inv_anti₀ (by norm_num) h1
          have hpos : 0 < 1 - (2 : ℝ) ^ (-s) := by linarith
          rw [inv_le_iff_one_le_mul₀ hpos]
          linarith
        · simp only [hp2, ite_false]
          have hodd : p % 4 = 1 ∨ p % 4 = 3 := by
            rcases hpp.eq_two_or_odd with rfl | hodd
            · exact (hp2 rfl).elim
            · omega
          rcases hodd with hp1 | hp3
          · have hnot3 : p % 4 ≠ 3 := by omega
            simp only [hnot3, ite_false, one_mul]
            have hchi1 : chi4 p = 1 := by simp [chi4, hp1]
            rw [hchi1, one_mul]
          · simp only [hp3, ite_true]
            have hchi3 : chi4 p = -1 := by
              unfold chi4
              have h1 : p % 4 ≠ 1 := by omega
              simp [h1, hp3]
            rw [hchi3, neg_one_mul, sub_neg_eq_add]
            exact factor_bound_mod4_eq3 hpp hp3 hs
      have hprod_le :
          ∏ p ∈ N.primesBelow, (1 - rpowHom s hs0 p)⁻¹ ≤
          (∏ p ∈ N.primesBelow,
            (if p = 2 then (2 : ℝ)
             else if p % 4 = 3 then ((p : ℝ) / ((p : ℝ) - 1)) ^ 2
             else 1)) *
          ∏ p ∈ N.primesBelow, (1 - chi4RpowHom s p)⁻¹ := by
        rw [← Finset.prod_mul_distrib]
        refine Finset.prod_le_prod (fun p hp => ?_) hfactor
        have hpp : p.Prime := Nat.prime_of_mem_primesBelow hp
        simp only [rpowHom, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk]
        have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hpp.two_le
        have hps : (p : ℝ) ^ (-s) < 1 := by
          rw [Real.rpow_neg (by linarith)]
          exact inv_lt_one_of_one_lt₀ (Real.one_lt_rpow (by linarith) hs0)
        exact inv_nonneg.mpr (by linarith)
      have hmid :
          ∏ p ∈ N.primesBelow,
            (if p = 2 then (2 : ℝ)
             else if p % 4 = 3 then ((p : ℝ) / ((p : ℝ) - 1)) ^ 2
             else 1) ≤ 2 * C ^ 2 := by
        have hsplit :
            ∏ p ∈ N.primesBelow,
              (if p = 2 then (2 : ℝ)
               else if p % 4 = 3 then ((p : ℝ) / ((p : ℝ) - 1)) ^ 2
               else 1) =
            (∏ p ∈ N.primesBelow, if p = 2 then (2 : ℝ) else 1) *
            (∏ p ∈ N.primesBelow, if p % 4 = 3 then ((p : ℝ) / ((p : ℝ) - 1)) ^ 2 else 1) := by
          rw [← Finset.prod_mul_distrib]
          refine Finset.prod_congr rfl fun p _ => ?_
          split_ifs with h1 h2
          · omega
          · ring
          · ring
          · ring
        rw [hsplit]
        have hpart1 : (∏ p ∈ N.primesBelow, if p = 2 then (2 : ℝ) else 1) ≤ 2 := by
          rw [Finset.prod_ite_eq']
          split_ifs <;> norm_num
        have hpart2 :
            (∏ p ∈ N.primesBelow, if p % 4 = 3 then ((p : ℝ) / ((p : ℝ) - 1)) ^ 2 else 1) ≤ C ^ 2 := by
          rw [← Finset.prod_filter, Finset.prod_pow]
          exact pow_le_pow_left₀ hS3_nonneg hS3_le 2
        have hpart2_nn : 0 ≤ ∏ p ∈ N.primesBelow,
            if p % 4 = 3 then ((p : ℝ) / ((p : ℝ) - 1)) ^ 2 else 1 :=
          Finset.prod_nonneg fun _ _ => by split_ifs <;> positivity
        exact mul_le_mul hpart1 hpart2 hpart2_nn (by norm_num)
      have hchi_prod_nn : 0 ≤ ∏ p ∈ N.primesBelow, (1 - chi4RpowHom s p)⁻¹ := by
        refine Finset.prod_nonneg fun p hp => ?_
        have hpp : p.Prime := Nat.prime_of_mem_primesBelow hp
        have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hpp.two_le
        simp only [chi4RpowHom, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk]
        have hps : (p : ℝ) ^ (-s) < 1 := by
          rw [Real.rpow_neg (by linarith)]
          exact inv_lt_one_of_one_lt₀ (Real.one_lt_rpow (by linarith) hs0)
        have hle : chi4 p * (p : ℝ) ^ (-s) ≤ (p : ℝ) ^ (-s) := by
          calc chi4 p * (p : ℝ) ^ (-s)
              ≤ |chi4 p| * (p : ℝ) ^ (-s) := by
                gcongr
                exact le_abs_self _
            _ ≤ 1 * (p : ℝ) ^ (-s) := by gcongr; exact abs_chi4_le_one p
            _ = (p : ℝ) ^ (-s) := one_mul _
        exact inv_nonneg.mpr (by linarith)
      exact hprod_le.trans (mul_le_mul_of_nonneg_right hmid hchi_prod_nn)
    have ht_rhs := ht2.const_mul (2 * C ^ 2)
    have htsum_le : ∑' n : ℕ, rpowHom s hs0 n ≤ (2 * C ^ 2) * ∑' n : ℕ, chi4RpowHom s n :=
      le_of_tendsto_of_tendsto ht1 ht_rhs (Eventually.of_forall hstep)
    have hchi_le1 : ∑' n : ℕ, chi4RpowHom s n ≤ 1 := tsum_chi4_rpow_le_one hs
    calc ∑' n : ℕ, (n : ℝ) ^ (-s)
        = ∑' n : ℕ, rpowHom s hs0 n := rfl
      _ ≤ (2 * C ^ 2) * ∑' n : ℕ, chi4RpowHom s n := htsum_le
      _ ≤ (2 * C ^ 2) * 1 := by gcongr
      _ = 2 * C ^ 2 := mul_one _
  have hharm : ¬ Summable (fun n : ℕ => ((n : ℝ)⁻¹)) := Real.not_summable_natCast_inv
  have hex : ∃ K : ℕ, 2 ≤ K ∧ 4 * C ^ 2 < ∑ n ∈ Finset.Icc 1 K, (n : ℝ)⁻¹ := by
    by_contra hall
    push Not at hall
    apply hharm
    refine summable_of_sum_range_le (fun n => by positivity) (c := 4 * C ^ 2 + 2) fun N => ?_
    rcases le_or_gt N 2 with hN | hN
    · have : Finset.range N ⊆ Finset.range 3 := Finset.range_mono (by omega)
      calc ∑ n ∈ Finset.range N, (n : ℝ)⁻¹
          ≤ ∑ n ∈ Finset.range 3, (n : ℝ)⁻¹ :=
            Finset.sum_le_sum_of_subset_of_nonneg this (fun _ _ _ => by positivity)
        _ = 3 / 2 := by simp [Finset.sum_range_succ]; norm_num
        _ ≤ 4 * C ^ 2 + 2 := by nlinarith
    · have hsub : Finset.range N ⊆ insert 0 (Finset.Icc 1 N) := by
        intro x hx
        simp only [mem_range, mem_insert, mem_Icc] at hx ⊢
        omega
      calc ∑ n ∈ Finset.range N, (n : ℝ)⁻¹
          ≤ ∑ n ∈ insert 0 (Finset.Icc 1 N), (n : ℝ)⁻¹ :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
        _ = ∑ n ∈ Finset.Icc 1 N, (n : ℝ)⁻¹ := by
            rw [Finset.sum_insert (by simp)]
            simp
        _ ≤ 4 * C ^ 2 := hall N (by omega)
        _ ≤ 4 * C ^ 2 + 2 := by linarith
  obtain ⟨K, hK2, hKsum⟩ := hex
  have hK_real : (2 : ℝ) ≤ K := by exact_mod_cast hK2
  have hlogK_pos : 0 < Real.log K := Real.log_pos (by linarith)
  set s : ℝ := 1 + Real.log 2 / Real.log K
  have hs : 1 < s := by
    have : 0 < Real.log 2 / Real.log K := div_pos (Real.log_pos (by norm_num)) hlogK_pos
    linarith
  have hKs : (K : ℝ) ^ (s - 1) = 2 := by
    have hsub : s - 1 = Real.log 2 / Real.log K := by simp [s]
    rw [hsub, Real.rpow_def_of_pos (by linarith), mul_div_cancel₀ _ hlogK_pos.ne',
      Real.exp_log (by norm_num)]
  have hterm : ∀ n ∈ Finset.Icc 1 K, (1 / 2 : ℝ) * (n : ℝ)⁻¹ ≤ (n : ℝ) ^ (-s) := by
    intro n hn
    simp only [mem_Icc] at hn
    have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn.1
    have hn_le : (n : ℝ) ≤ K := by exact_mod_cast hn.2
    have hns : (n : ℝ) ^ (s - 1) ≤ 2 := by
      calc (n : ℝ) ^ (s - 1) ≤ (K : ℝ) ^ (s - 1) :=
            Real.rpow_le_rpow hn_pos.le hn_le (by linarith)
        _ = 2 := hKs
    have hsplit : (n : ℝ) ^ (-s) = (n : ℝ)⁻¹ * ((n : ℝ) ^ (s - 1))⁻¹ := by
      rw [← Real.rpow_neg_one (n : ℝ), ← Real.rpow_neg hn_pos.le, ← Real.rpow_add hn_pos]
      congr 1; ring
    rw [hsplit, one_div, mul_comm (2 : ℝ)⁻¹]
    gcongr
  have hsum_le_tsum : ∑ n ∈ Finset.Icc 1 K, (n : ℝ) ^ (-s) ≤ ∑' n : ℕ, (n : ℝ) ^ (-s) := by
    have hsum_s : Summable (fun n : ℕ => (n : ℝ) ^ (-s)) := (summable_rpowHom hs).of_norm
    exact hsum_s.sum_le_tsum (Finset.Icc 1 K) (fun n _ => Real.rpow_nonneg (Nat.cast_nonneg n) _)
  have hfinal : 2 * C ^ 2 < ∑' n : ℕ, (n : ℝ) ^ (-s) := calc
    2 * C ^ 2 = (1 / 2 : ℝ) * (4 * C ^ 2) := by ring
    _ < (1 / 2 : ℝ) * ∑ n ∈ Finset.Icc 1 K, (n : ℝ)⁻¹ := by gcongr
    _ = ∑ n ∈ Finset.Icc 1 K, (1 / 2 : ℝ) * (n : ℝ)⁻¹ := by rw [Finset.mul_sum]
    _ ≤ ∑ n ∈ Finset.Icc 1 K, (n : ℝ) ^ (-s) := Finset.sum_le_sum hterm
    _ ≤ ∑' n : ℕ, (n : ℝ) ^ (-s) := hsum_le_tsum
  linarith [hbound s hs]

/- ### Part 2: Sums of two squares bound and lower bound on S₁(X) -/

private def rho (m : ℕ) : ℕ :=
  ((Finset.Icc 1 m ×ˢ Finset.range (m + 1)).filter fun p => p.1 ^ 2 + p.2 ^ 2 = m).card

private def rhoBound (m : ℕ) : ℕ :=
  ∏ p ∈ m.primeFactors.filter (fun p => p % 4 = 1), (m.factorization p + 1)

private def rotG (z : GaussianInt) : GaussianInt :=
  if 0 < z.re ∧ 0 ≤ z.im then z
  else if z.re ≤ 0 ∧ 0 < z.im then ⟨z.im, -z.re⟩
  else if z.re < 0 ∧ z.im ≤ 0 then -z
  else ⟨-z.im, z.re⟩

private lemma norm_gaussian_eq (z : GaussianInt) : z.norm = z.re ^ 2 + z.im ^ 2 := by
  simp [Zsqrtd.norm_def, sq]

private lemma norm_eq_one_cases {u : GaussianInt} (hu : u.norm = 1) :
    u = 1 ∨ u = -1 ∨ u = ⟨0, 1⟩ ∨ u = ⟨0, -1⟩ := by
  rw [norm_gaussian_eq] at hu
  have hre_bnd : -1 ≤ u.re ∧ u.re ≤ 1 := by
    have := sq_nonneg u.im
    constructor <;> nlinarith
  have him_bnd : -1 ≤ u.im ∧ u.im ≤ 1 := by
    have := sq_nonneg u.re
    constructor <;> nlinarith
  have hre : u.re = 0 ∨ u.re = 1 ∨ u.re = -1 := by omega
  have him : u.im = 0 ∨ u.im = 1 ∨ u.im = -1 := by omega
  rcases hre with h1 | h1 | h1 <;> rcases him with h2 | h2 | h2 <;>
    (try nlinarith)
  · right; right; left; ext <;> simp [h1, h2]
  · right; right; right; ext <;> simp [h1, h2]
  · left; ext <;> simp [h1, h2]
  · right; left; ext <;> simp [h1, h2]

private lemma rotG_in_Q1 {z : GaussianInt} (hz : z ≠ 0) :
    0 < (rotG z).re ∧ 0 ≤ (rotG z).im := by
  have hne : z.re ≠ 0 ∨ z.im ≠ 0 := by
    by_contra h
    push Not at h
    exact hz (by ext <;> simp [h.1, h.2])
  unfold rotG
  split_ifs with h1 h2 h3
  · exact h1
  · simp; omega
  · simp; omega
  · simp; omega

private lemma rotG_eq_unit_mul (z : GaussianInt) :
    ∃ u : GaussianInt, u.norm = 1 ∧ rotG z = u * z := by
  unfold rotG
  split_ifs
  · exact ⟨1, by simp [norm_gaussian_eq], by simp⟩
  · exact ⟨⟨0, -1⟩, by simp [norm_gaussian_eq], by ext <;> simp⟩
  · exact ⟨-1, by simp [norm_gaussian_eq], by simp⟩
  · exact ⟨⟨0, 1⟩, by simp [norm_gaussian_eq], by ext <;> simp⟩

private lemma eq_of_unit_mul_Q1 {z₁ z₂ u : GaussianInt} (hu : u.norm = 1)
    (h1 : 0 < z₁.re ∧ 0 ≤ z₁.im) (h2 : 0 < z₂.re ∧ 0 ≤ z₂.im) (heq : z₁ = u * z₂) :
    z₁ = z₂ := by
  rcases norm_eq_one_cases hu with rfl | rfl | rfl | rfl
  · simpa using heq
  · have : z₁.re = -z₂.re := by simp [heq]
    omega
  · have hre : z₁.re = -z₂.im := by simp [heq]
    omega
  · have him : z₁.im = -z₂.re := by simp [heq]
    omega

private lemma gaussian_prime_of_norm_prime {g : GaussianInt} {p : ℕ} (hp : p.Prime)
    (hnorm : g.norm = p) : Prime g := by
  refine irreducible_iff_prime.mp ⟨?_, ?_⟩
  · intro hu
    obtain ⟨v, hv⟩ := hu.exists_right_inv
    have hmul : g.norm * v.norm = 1 := by
      have := congrArg Zsqrtd.norm hv
      simpa using this
    rw [hnorm] at hmul
    have hp2 : (2 : ℤ) ≤ p := by exact_mod_cast hp.two_le
    have hv0 : 0 ≤ v.norm := GaussianInt.norm_nonneg v
    have hv_cases : v.norm = 0 ∨ 1 ≤ v.norm := by omega
    rcases hv_cases with h0 | h1 <;> nlinarith
  · intro a b hab
    have hmul : a.norm * b.norm = p := by
      have := congrArg Zsqrtd.norm hab
      simpa [hnorm] using this.symm
    have ha0 : 0 ≤ a.norm := GaussianInt.norm_nonneg a
    have hb0 : 0 ≤ b.norm := GaussianInt.norm_nonneg b
    have hnat : a.norm.natAbs * b.norm.natAbs = p := by
      zify
      rw [abs_of_nonneg ha0, abs_of_nonneg hb0]
      exact hmul
    rcases hp.eq_one_or_self_of_dvd a.norm.natAbs ⟨b.norm.natAbs, hnat.symm⟩ with h1 | h2
    · left
      have ha1 : a.norm = 1 := by omega
      have hmul1 : a * star a = 1 := by
        ext <;> simp [Zsqrtd.norm_def] at ha1 ⊢ <;> linarith
      exact isUnit_iff_exists_inv.mpr ⟨star a, hmul1⟩
    · right
      have hb1 : b.norm.natAbs = 1 := by
        have hp0 : 0 < p := hp.pos
        nlinarith
      have hb1' : b.norm = 1 := by omega
      have hmul1 : b * star b = 1 := by
        ext <;> simp [Zsqrtd.norm_def] at hb1' ⊢ <;> linarith
      exact isUnit_iff_exists_inv.mpr ⟨star b, hmul1⟩

private lemma gaussian_factor_split {p : ℕ} (hp : p.Prime) {g : GaussianInt}
    (hnorm : g.norm = p) :
    ∀ (e : ℕ) (z : GaussianInt), (p : ℤ) ^ e ∣ z.norm →
      ∃ j ≤ e, g ^ j * (star g) ^ (e - j) ∣ z := by
  have hgp : Prime g := gaussian_prime_of_norm_prime hp hnorm
  have hgmul : g * star g = (p : GaussianInt) := by
    ext
    · simp [Zsqrtd.norm_def] at hnorm ⊢; linarith
    · simp; ring
  have hsnorm : (star g).norm = p := by
    simpa [norm_gaussian_eq] using hnorm
  intro e
  induction e with
  | zero =>
    intro z _
    exact ⟨0, le_rfl, by simp⟩
  | succ e ih =>
    intro z hdvd
    have hpdvd : (p : ℤ) ∣ z.norm := dvd_trans (dvd_pow_self _ (Nat.succ_ne_zero e)) hdvd
    have hzmul : z * star z = (z.norm : GaussianInt) := by
      ext
      · simp [Zsqrtd.norm_def]
      · simp; ring
    have hgdvd : g ∣ z * star z := by
      obtain ⟨t, ht⟩ := hpdvd
      refine ⟨star g * (t : GaussianInt), ?_⟩
      calc z * star z = (z.norm : GaussianInt) := hzmul
        _ = ((p : ℤ) * t : ℤ) := by rw [ht]
        _ = (p : GaussianInt) * (t : GaussianInt) := by push_cast; rfl
        _ = (g * star g) * (t : GaussianInt) := by rw [hgmul]
        _ = g * (star g * (t : GaussianInt)) := by ring
    rcases hgp.dvd_or_dvd hgdvd with h1 | h2
    · obtain ⟨z', rfl⟩ := h1
      have hzn : (p : ℤ) ^ e ∣ z'.norm := by
        rw [Zsqrtd.norm_mul, hnorm, pow_succ'] at hdvd
        exact (mul_dvd_mul_iff_left (by exact_mod_cast hp.ne_zero)).mp hdvd
      obtain ⟨j, hje, hj⟩ := ih z' hzn
      refine ⟨j + 1, Nat.succ_le_succ hje, ?_⟩
      obtain ⟨w, hw⟩ := hj
      refine ⟨w, ?_⟩
      rw [show e + 1 - (j + 1) = e - j by omega, pow_succ', hw]
      ring
    · have hs : star g ∣ z := by
        obtain ⟨z', hz'⟩ := h2
        refine ⟨star z', ?_⟩
        have := congrArg star hz'
        simpa [star_mul, mul_comm] using this
      obtain ⟨z', rfl⟩ := hs
      have hzn : (p : ℤ) ^ e ∣ z'.norm := by
        rw [Zsqrtd.norm_mul, hsnorm, pow_succ'] at hdvd
        exact (mul_dvd_mul_iff_left (by exact_mod_cast hp.ne_zero)).mp hdvd
      obtain ⟨j, hje, hj⟩ := ih z' hzn
      refine ⟨j, Nat.le_succ_of_le hje, ?_⟩
      obtain ⟨w, hw⟩ := hj
      refine ⟨w, ?_⟩
      rw [show e + 1 - j = (e - j) + 1 by omega, pow_succ', hw]
      ring

private lemma rotG_to_Q1_pair {m' : ℕ} (hm' : 0 < m') {w : GaussianInt} (hw : w.norm = m') :
    ((rotG w).re.toNat, (rotG w).im.toNat) ∈
      (Finset.Icc 1 m' ×ˢ Finset.range (m' + 1)).filter (fun x => x.1 ^ 2 + x.2 ^ 2 = m') := by
  have hw_ne : w ≠ 0 := fun h0 => by
    have : (0 : ℤ) = m' := by simpa [h0, norm_gaussian_eq] using hw
    omega
  have hq1 := rotG_in_Q1 hw_ne
  obtain ⟨u0, hu0, hrot⟩ := rotG_eq_unit_mul w
  have hrnorm : (rotG w).norm = m' := by
    rw [hrot, Zsqrtd.norm_mul, hu0, one_mul, hw]
  have hre_eq : ((rotG w).re.toNat : ℤ) = (rotG w).re := Int.toNat_of_nonneg (by omega)
  have him_eq : ((rotG w).im.toNat : ℤ) = (rotG w).im := Int.toNat_of_nonneg hq1.2
  have hsum_eq : (rotG w).re.toNat ^ 2 + (rotG w).im.toNat ^ 2 = m' := by
    zify
    rw [hre_eq, him_eq, ← norm_gaussian_eq]
    exact hrnorm
  simp only [mem_filter, mem_product, mem_Icc, mem_range]
  refine ⟨⟨⟨by omega, ?_⟩, ?_⟩, hsum_eq⟩
  · nlinarith
  · nlinarith

private lemma eq_of_rotG_pair_eq {m' : ℕ} (hm' : 0 < m') {c w₁ w₂ : GaussianInt}
    {x₁ x₂ : ℕ × ℕ} (hx₁_pos : 1 ≤ x₁.1) (hx₂_pos : 1 ≤ x₂.1)
    (hw₁ : (⟨x₁.1, x₁.2⟩ : GaussianInt) = c * w₁ ∧ w₁.norm = m')
    (hw₂ : (⟨x₂.1, x₂.2⟩ : GaussianInt) = c * w₂ ∧ w₂.norm = m')
    (heq : ((rotG w₁).re.toNat, (rotG w₁).im.toNat) = ((rotG w₂).re.toNat, (rotG w₂).im.toNat)) :
    x₁ = x₂ := by
  have hw₁_ne : w₁ ≠ 0 := fun h0 => by
    have : (0 : ℤ) = m' := by simpa [h0, norm_gaussian_eq] using hw₁.2
    omega
  have hw₂_ne : w₂ ≠ 0 := fun h0 => by
    have : (0 : ℤ) = m' := by simpa [h0, norm_gaussian_eq] using hw₂.2
    omega
  have hq₁ := rotG_in_Q1 hw₁_ne
  have hq₂ := rotG_in_Q1 hw₂_ne
  have hrot_eq : rotG w₁ = rotG w₂ := by
    have h1 := congrArg Prod.fst heq
    have h2 := congrArg Prod.snd heq
    dsimp only at h1 h2
    ext
    · have := congrArg (fun k : ℕ => (k : ℤ)) h1
      rwa [Int.toNat_of_nonneg (by omega), Int.toNat_of_nonneg (by omega)] at this
    · have := congrArg (fun k : ℕ => (k : ℤ)) h2
      rwa [Int.toNat_of_nonneg hq₁.2, Int.toNat_of_nonneg hq₂.2] at this
  obtain ⟨u₁, hu₁, hru₁⟩ := rotG_eq_unit_mul w₁
  obtain ⟨u₂, hu₂, hru₂⟩ := rotG_eq_unit_mul w₂
  have hsu₁ : star u₁ * u₁ = 1 := by
    ext <;> simp [Zsqrtd.norm_def] at hu₁ ⊢ <;> linarith
  have hw_rel : w₁ = (star u₁ * u₂) * w₂ := by
    calc w₁ = 1 * w₁ := (one_mul _).symm
      _ = (star u₁ * u₁) * w₁ := by rw [hsu₁]
      _ = star u₁ * (u₁ * w₁) := by ring
      _ = star u₁ * (u₂ * w₂) := by rw [← hru₁, hrot_eq, hru₂]
      _ = (star u₁ * u₂) * w₂ := by ring
  have hmul_u : (⟨x₁.1, x₁.2⟩ : GaussianInt) =
      (star u₁ * u₂) * (⟨x₂.1, x₂.2⟩ : GaussianInt) := by
    rw [hw₁.1, hw₂.1, hw_rel]
    ring
  have hunorm : (star u₁ * u₂).norm = 1 := by
    rw [Zsqrtd.norm_mul]
    have : (star u₁).norm = u₁.norm := by simp [norm_gaussian_eq]
    rw [this, hu₁, hu₂, one_mul]
  have hzeq := eq_of_unit_mul_Q1 hunorm
    ⟨by dsimp only; omega, by simp⟩
    ⟨by dsimp only; omega, by simp⟩ hmul_u
  ext
  · have hre := congrArg Zsqrtd.re hzeq
    dsimp only at hre
    exact_mod_cast hre
  · have him := congrArg Zsqrtd.im hzeq
    dsimp only at him
    exact_mod_cast him

private lemma rho_le_rhoBound :
    ∀ m : ℕ, 0 < m → (∀ p ∈ m.primeFactors, p % 4 ≠ 3) → rho m ≤ rhoBound m := by
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro hm hno3
    by_cases hm1 : m = 1
    · subst hm1
      have h1 : rho 1 = 1 := by decide
      have h2 : rhoBound 1 = 1 := by simp [rhoBound]
      omega
    · have hgt1 : 1 < m := by omega
      have hne_pf : m.primeFactors.Nonempty := Nat.nonempty_primeFactors.mpr hgt1
      obtain ⟨p, hp_mem⟩ := hne_pf
      have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp_mem
      have hpm : p ∣ m := Nat.dvd_of_mem_primeFactors hp_mem
      have hp_ne3 : p % 4 ≠ 3 := hno3 p hp_mem
      have : Fact p.Prime := ⟨hpp⟩
      obtain ⟨u, v, huv⟩ := Nat.Prime.sq_add_sq hp_ne3
      set gp : GaussianInt := ⟨u, v⟩
      have hgp_norm : gp.norm = p := by
        simp only [gp, norm_gaussian_eq]
        exact_mod_cast huv
      by_cases hp2 : p = 2
      · subst hp2
        set m' := m / 2
        have hm'_eq : 2 * m' = m := Nat.mul_div_cancel' hpm
        have hm'_pos : 0 < m' := by omega
        have hm'_lt : m' < m := by omega
        have hno3' : ∀ q ∈ m'.primeFactors, q % 4 ≠ 3 := fun q hq => by
          apply hno3 q
          rw [Nat.mem_primeFactors] at hq ⊢
          exact ⟨hq.1, dvd_trans hq.2.1 ⟨2, by omega⟩, by omega⟩
        have hrb : rhoBound m = rhoBound m' := by
          unfold rhoBound
          have heq_set : m.primeFactors.filter (fun q => q % 4 = 1) =
              m'.primeFactors.filter (fun q => q % 4 = 1) := by
            ext q
            simp only [mem_filter, Nat.mem_primeFactors, ne_eq]
            constructor
            · rintro ⟨⟨hq, hqm, _⟩, hq1⟩
              refine ⟨⟨hq, ?_, by omega⟩, hq1⟩
              have hq2 : q ≠ 2 := by omega
              rw [← hm'_eq] at hqm
              exact (hq.dvd_mul.mp hqm).resolve_left
                (fun h => hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp h))
            · rintro ⟨⟨hq, hqm', _⟩, hq1⟩
              exact ⟨⟨hq, dvd_trans hqm' ⟨2, by omega⟩, by omega⟩, hq1⟩
          rw [heq_set]
          refine Finset.prod_congr rfl fun q hq => ?_
          simp only [mem_filter, Nat.mem_primeFactors] at hq
          have hq2 : q ≠ 2 := by omega
          rw [← hm'_eq, Nat.factorization_mul (by norm_num) (by omega), Finsupp.add_apply]
          have : (2 : ℕ).factorization q = 0 := by
            rw [Nat.factorization_eq_zero_iff]
            right; left
            intro h
            exact hq2 ((Nat.prime_dvd_prime_iff_eq hq.1.1 Nat.prime_two).mp h)
          rw [this, zero_add]
        set A := (Finset.Icc 1 m ×ˢ Finset.range (m + 1)).filter fun x => x.1 ^ 2 + x.2 ^ 2 = m
        set B := (Finset.Icc 1 m' ×ˢ Finset.range (m' + 1)).filter fun x => x.1 ^ 2 + x.2 ^ 2 = m'
        set g2i : GaussianInt := ⟨1, 1⟩
        have hdiv : ∀ x ∈ A, ∃ w : GaussianInt,
            (⟨x.1, x.2⟩ : GaussianInt) = g2i * w ∧ w.norm = m' := by
          intro x hx
          simp only [A, mem_filter] at hx
          have hpar : (x.1 + x.2) % 2 = 0 := by
            have hsum_even : (x.1 ^ 2 + x.2 ^ 2) % 2 = 0 := by omega
            have h1 : x.1 % 2 = 0 ∨ x.1 % 2 = 1 := by omega
            have h2 : x.2 % 2 = 0 ∨ x.2 % 2 = 1 := by omega
            rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
            · omega
            · have : (x.1 ^ 2 + x.2 ^ 2) % 2 = 1 := by
                simp [Nat.add_mod, sq, Nat.mul_mod, h1, h2]
              omega
            · have : (x.1 ^ 2 + x.2 ^ 2) % 2 = 1 := by
                simp [Nat.add_mod, sq, Nat.mul_mod, h1, h2]
              omega
            · omega
          have h1 : (2 : ℤ) ∣ (x.1 : ℤ) + (x.2 : ℤ) := by omega
          have h2 : (2 : ℤ) ∣ (x.2 : ℤ) - (x.1 : ℤ) := by omega
          obtain ⟨r, hr⟩ := h1
          obtain ⟨t, ht⟩ := h2
          refine ⟨⟨r, t⟩, ?_, ?_⟩
          · ext <;> simp [g2i] <;> omega
          · rw [norm_gaussian_eq]
            have hsq : ((x.1 : ℤ) ^ 2 + (x.2 : ℤ) ^ 2) = 2 * (m' : ℤ) := by
              exact_mod_cast (by omega : x.1 ^ 2 + x.2 ^ 2 = 2 * m')
            nlinarith
        have hcard : A.card ≤ B.card := by
          let f : ℕ × ℕ → ℕ × ℕ := fun x =>
            if hx : x ∈ A then
              let w := rotG (Classical.choose (hdiv x hx))
              (w.re.toNat, w.im.toNat)
            else (0, 0)
          refine Finset.card_le_card_of_injOn f ?_ ?_
          · intro x hx
            have hxA : x ∈ A := Finset.mem_coe.mp hx
            rw [Finset.mem_coe]
            simp only [f, dif_pos hxA]
            exact rotG_to_Q1_pair hm'_pos (Classical.choose_spec (hdiv x hxA)).2
          · intro x₁ hx₁ x₂ hx₂ heq
            have hx₁A : x₁ ∈ A := Finset.mem_coe.mp hx₁
            have hx₂A : x₂ ∈ A := Finset.mem_coe.mp hx₂
            simp only [f, dif_pos hx₁A, dif_pos hx₂A] at heq
            have h1pos : 1 ≤ x₁.1 := (Finset.mem_Icc.mp (Finset.mem_product.mp (Finset.mem_filter.mp hx₁A).1).1).1
            have h2pos : 1 ≤ x₂.1 := (Finset.mem_Icc.mp (Finset.mem_product.mp (Finset.mem_filter.mp hx₂A).1).1).1
            exact eq_of_rotG_pair_eq hm'_pos h1pos h2pos
              (Classical.choose_spec (hdiv x₁ hx₁A))
              (Classical.choose_spec (hdiv x₂ hx₂A)) heq
        calc rho m = A.card := rfl
          _ ≤ B.card := hcard
          _ = rho m' := rfl
          _ ≤ rhoBound m' := ih m' hm'_lt hm'_pos hno3'
          _ = rhoBound m := hrb.symm
      · have hp1 : p % 4 = 1 := by
          rcases hpp.eq_two_or_odd with rfl | hodd
          · exact (hp2 rfl).elim
          · omega
        set e := m.factorization p
        have he_pos : 0 < e := Nat.Prime.factorization_pos_of_dvd hpp (by omega) hpm
        have hpe_dvd : p ^ e ∣ m := Nat.ordProj_dvd m p
        set m' := m / p ^ e
        have hm'_eq : p ^ e * m' = m := Nat.mul_div_cancel' hpe_dvd
        have hm'_pos : 0 < m' :=
          Nat.div_pos (Nat.le_of_dvd hm hpe_dvd) (pow_pos hpp.pos e)
        have hpe_gt1 : 1 < p ^ e := one_lt_pow₀ hpp.one_lt (by omega)
        have hm'_lt : m' < m := by nlinarith
        have hp_ndvd_m' : ¬ p ∣ m' := by
          intro h
          have : p ^ (e + 1) ∣ m := by
            obtain ⟨k, hk⟩ := h
            exact ⟨k, by rw [← hm'_eq, hk, pow_succ]; ring⟩
          exact Nat.pow_succ_factorization_not_dvd (by omega) hpp this
        have hno3' : ∀ q ∈ m'.primeFactors, q % 4 ≠ 3 := fun q hq => by
          apply hno3 q
          rw [Nat.mem_primeFactors] at hq ⊢
          exact ⟨hq.1, dvd_trans hq.2.1 ⟨p ^ e, by rw [← hm'_eq, mul_comm]⟩, by omega⟩
        have hrb : rhoBound m = (e + 1) * rhoBound m' := by
          unfold rhoBound
          have hp_in : p ∈ m.primeFactors.filter (fun q => q % 4 = 1) := by
            simp [hp_mem, hp1]
          rw [← Finset.mul_prod_erase _ _ hp_in]
          congr 1
          have herase : (m.primeFactors.filter (fun q => q % 4 = 1)).erase p =
              m'.primeFactors.filter (fun q => q % 4 = 1) := by
            ext q
            simp only [mem_erase, mem_filter, Nat.mem_primeFactors, ne_eq]
            constructor
            · rintro ⟨hqp, ⟨hq, hqm, _⟩, hq1⟩
              refine ⟨⟨hq, ?_, by omega⟩, hq1⟩
              rw [← hm'_eq] at hqm
              exact (hq.dvd_mul.mp hqm).resolve_left fun hd =>
                hqp ((Nat.prime_dvd_prime_iff_eq hq hpp).mp (hq.dvd_of_dvd_pow hd))
            · rintro ⟨⟨hq, hqm', _⟩, hq1⟩
              refine ⟨fun h => hp_ndvd_m' (h ▸ hqm'),
                ⟨hq, dvd_trans hqm' ⟨p ^ e, by rw [← hm'_eq, mul_comm]⟩, by omega⟩, hq1⟩
          rw [herase]
          refine Finset.prod_congr rfl fun q hq => ?_
          simp only [mem_filter, Nat.mem_primeFactors] at hq
          have hqp : q ≠ p := fun h => hp_ndvd_m' (h ▸ hq.1.2.1)
          rw [← hm'_eq, Nat.factorization_mul (pow_ne_zero e hpp.ne_zero) (by omega),
            Finsupp.add_apply, Nat.Prime.factorization_pow hpp]
          simp [Finsupp.single_apply, hqp.symm]
        set A := (Finset.Icc 1 m ×ˢ Finset.range (m + 1)).filter fun x => x.1 ^ 2 + x.2 ^ 2 = m
        set B := (Finset.Icc 1 m' ×ˢ Finset.range (m' + 1)).filter fun x => x.1 ^ 2 + x.2 ^ 2 = m'
        have hsplit : ∀ x ∈ A, ∃ j ≤ e, ∃ w : GaussianInt,
            (⟨x.1, x.2⟩ : GaussianInt) = gp ^ j * (star gp) ^ (e - j) * w ∧ w.norm = m' := by
          intro x hx
          simp only [A, mem_filter] at hx
          have hzn : (⟨x.1, x.2⟩ : GaussianInt).norm = m := by
            simp only [norm_gaussian_eq]
            exact_mod_cast hx.2
          have hdvd : (p : ℤ) ^ e ∣ (⟨x.1, x.2⟩ : GaussianInt).norm := by
            rw [hzn, ← hm'_eq]
            exact ⟨m', by push_cast; rfl⟩
          obtain ⟨j, hje, w, hw⟩ := gaussian_factor_split hpp hgp_norm e ⟨x.1, x.2⟩ hdvd
          refine ⟨j, hje, w, hw, ?_⟩
          have hsnorm : (star gp).norm = p := by simpa [norm_gaussian_eq] using hgp_norm
          have hnorm_pow : ∀ (g : GaussianInt) (k : ℕ), (g ^ k).norm = g.norm ^ k := by
            intro g k
            induction k with
            | zero => simp
            | succ k ihk => rw [pow_succ, Zsqrtd.norm_mul, ihk, pow_succ]
          have hnorm_eq : (p : ℤ) ^ e * (m' : ℤ) = (p : ℤ) ^ e * w.norm := by
            have hnw := congrArg Zsqrtd.norm hw
            simp only [Zsqrtd.norm_mul, hnorm_pow, hgp_norm, hsnorm] at hnw
            rw [← pow_add, show j + (e - j) = e by omega] at hnw
            rw [← hnw, hzn, ← hm'_eq]
            push_cast; rfl
          exact mul_left_cancel₀ (pow_ne_zero e (by exact_mod_cast hpp.ne_zero)) hnorm_eq.symm
        have hcard : A.card ≤ (Finset.range (e + 1) ×ˢ B).card := by
          let f : ℕ × ℕ → ℕ × (ℕ × ℕ) := fun x =>
            if hx : x ∈ A then
              let j := Classical.choose (hsplit x hx)
              let w0 := Classical.choose (Classical.choose_spec (hsplit x hx)).2
              let w := rotG w0
              (j, (w.re.toNat, w.im.toNat))
            else (0, (0, 0))
          refine Finset.card_le_card_of_injOn f ?_ ?_
          · intro x hx
            have hxA : x ∈ A := Finset.mem_coe.mp hx
            rw [Finset.mem_coe]
            simp only [f, dif_pos hxA, mem_product, mem_range]
            have hj := Classical.choose_spec (hsplit x hxA)
            exact ⟨Nat.lt_succ_of_le hj.1, rotG_to_Q1_pair hm'_pos (Classical.choose_spec hj.2).2⟩
          · intro x₁ hx₁ x₂ hx₂ heq
            have hx₁A : x₁ ∈ A := Finset.mem_coe.mp hx₁
            have hx₂A : x₂ ∈ A := Finset.mem_coe.mp hx₂
            simp only [f, dif_pos hx₁A, dif_pos hx₂A] at heq
            set j₁ := Classical.choose (hsplit x₁ hx₁A)
            set w₁ := Classical.choose (Classical.choose_spec (hsplit x₁ hx₁A)).2
            set j₂ := Classical.choose (hsplit x₂ hx₂A)
            set w₂ := Classical.choose (Classical.choose_spec (hsplit x₂ hx₂A)).2
            have hj_eq : j₁ = j₂ := congrArg Prod.fst heq
            have hpair_eq := congrArg Prod.snd heq
            dsimp only at hpair_eq
            have h1pos : 1 ≤ x₁.1 := (Finset.mem_Icc.mp (Finset.mem_product.mp (Finset.mem_filter.mp hx₁A).1).1).1
            have h2pos : 1 ≤ x₂.1 := (Finset.mem_Icc.mp (Finset.mem_product.mp (Finset.mem_filter.mp hx₂A).1).1).1
            have hw₁ := Classical.choose_spec (Classical.choose_spec (hsplit x₁ hx₁A)).2
            have hw₂ := Classical.choose_spec (Classical.choose_spec (hsplit x₂ hx₂A)).2
            have hw₁' : (⟨x₁.1, x₁.2⟩ : GaussianInt) = gp ^ j₂ * (star gp) ^ (e - j₂) * w₁ := by
              have hc_eq : gp ^ j₁ * (star gp) ^ (e - j₁) = gp ^ j₂ * (star gp) ^ (e - j₂) := by
                rw [hj_eq]
              rw [← hc_eq]
              exact hw₁.1
            exact eq_of_rotG_pair_eq hm'_pos h1pos h2pos ⟨hw₁', hw₁.2⟩ hw₂ hpair_eq
        rw [Finset.card_product, Finset.card_range] at hcard
        calc rho m = A.card := rfl
          _ ≤ (e + 1) * B.card := hcard
          _ = (e + 1) * rho m' := rfl
          _ ≤ (e + 1) * rhoBound m' := Nat.mul_le_mul_left _ (ih m' hm'_lt hm'_pos hno3')
          _ = rhoBound m := hrb.symm

private lemma dvd_both_of_sq_add_sq_mod4_eq3 {p a b : ℕ} (hp : p.Prime) (hp3 : p % 4 = 3)
    (hdvd : p ∣ a ^ 2 + b ^ 2) : p ∣ a ∧ p ∣ b := by
  have : Fact p.Prime := ⟨hp⟩
  have hzero : ((a : ZMod p) ^ 2 + (b : ZMod p) ^ 2) = 0 := by
    have := (ZMod.natCast_eq_zero_iff (a ^ 2 + b ^ 2) p).mpr hdvd
    simpa [Nat.cast_add, Nat.cast_pow] using this
  by_cases hb : (b : ZMod p) = 0
  · have hpb : p ∣ b := (ZMod.natCast_eq_zero_iff b p).mp hb
    rw [hb, zero_pow two_ne_zero, add_zero] at hzero
    have ha0 : (a : ZMod p) = 0 := eq_zero_of_pow_eq_zero hzero
    exact ⟨(ZMod.natCast_eq_zero_iff a p).mp ha0, hpb⟩
  · exfalso
    have hsq : ((a : ZMod p) * (b : ZMod p)⁻¹) ^ 2 = -1 := by
      rw [mul_pow, inv_pow]
      have h1 : (a : ZMod p) ^ 2 = -((b : ZMod p) ^ 2) := eq_neg_of_add_eq_zero_left hzero
      rw [h1, neg_mul, mul_inv_cancel₀ (pow_ne_zero 2 hb)]
    have his : IsSquare (-1 : ZMod p) := ⟨(a : ZMod p) * (b : ZMod p)⁻¹, by rw [← sq, hsq]⟩
    exact (ZMod.exists_sq_eq_neg_one_iff.mp his) hp3

private lemma rho_decomp :
    ∀ m : ℕ, 0 < m →
      rho m = 0 ∨ ∃ d m0 : ℕ, 0 < d ∧ 0 < m0 ∧ m = d ^ 2 * m0 ∧
        (∀ p ∈ d.primeFactors, p % 4 = 3) ∧
        (∀ p ∈ m0.primeFactors, p % 4 ≠ 3) ∧ rho m = rho m0 := by
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro hm
    by_cases hall : ∀ p ∈ m.primeFactors, p % 4 ≠ 3
    · right
      exact ⟨1, m, one_pos, hm, by ring, by simp, hall, rfl⟩
    · push Not at hall
      obtain ⟨p, hp_mem, hp3⟩ := hall
      have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp_mem
      have hpm : p ∣ m := Nat.dvd_of_mem_primeFactors hp_mem
      by_cases hp2 : p ^ 2 ∣ m
      · set m' := m / p ^ 2
        have hm'_eq : p ^ 2 * m' = m := Nat.mul_div_cancel' hp2
        have hp2_gt1 : 1 < p ^ 2 := one_lt_pow₀ hpp.one_lt two_ne_zero
        have hm'_pos : 0 < m' := Nat.div_pos (Nat.le_of_dvd hm hp2) (pow_pos hpp.pos 2)
        have hm'_lt : m' < m := by nlinarith
        have hrho_eq : rho m = rho m' := by
          unfold rho
          refine Finset.card_bij (fun x _ => (x.1 / p, x.2 / p)) ?_ ?_ ?_
          · intro x hx
            simp only [mem_filter, mem_product, mem_Icc, mem_range] at hx ⊢
            have hboth := dvd_both_of_sq_add_sq_mod4_eq3 hpp hp3 (hx.2.symm ▸ hpm)
            have hx1 : p * (x.1 / p) = x.1 := Nat.mul_div_cancel' hboth.1
            have hx2 : p * (x.2 / p) = x.2 := Nat.mul_div_cancel' hboth.2
            have hsum : (x.1 / p) ^ 2 + (x.2 / p) ^ 2 = m' := by
              have hmul : p ^ 2 * ((x.1 / p) ^ 2 + (x.2 / p) ^ 2) = p ^ 2 * m' := by
                calc p ^ 2 * ((x.1 / p) ^ 2 + (x.2 / p) ^ 2)
                    = (p * (x.1 / p)) ^ 2 + (p * (x.2 / p)) ^ 2 := by ring
                  _ = x.1 ^ 2 + x.2 ^ 2 := by rw [hx1, hx2]
                  _ = m := hx.2
                  _ = p ^ 2 * m' := hm'_eq.symm
              exact Nat.eq_of_mul_eq_mul_left (pow_pos hpp.pos 2) hmul
            refine ⟨⟨⟨?_, ?_⟩, ?_⟩, hsum⟩
            · exact Nat.pos_of_ne_zero fun hzero => by
                rw [hzero, mul_zero] at hx1
                omega
            · nlinarith
            · nlinarith
          · intro x₁ hx₁ x₂ hx₂ heq
            simp only [mem_filter] at hx₁ hx₂
            have hb₁ := dvd_both_of_sq_add_sq_mod4_eq3 hpp hp3 (hx₁.2.symm ▸ hpm)
            have hb₂ := dvd_both_of_sq_add_sq_mod4_eq3 hpp hp3 (hx₂.2.symm ▸ hpm)
            have h1 := congrArg Prod.fst heq
            have h2 := congrArg Prod.snd heq
            dsimp only at h1 h2
            ext
            · rw [← Nat.mul_div_cancel' hb₁.1, ← Nat.mul_div_cancel' hb₂.1, h1]
            · rw [← Nat.mul_div_cancel' hb₁.2, ← Nat.mul_div_cancel' hb₂.2, h2]
          · intro y hy
            simp only [mem_filter, mem_product, mem_Icc, mem_range] at hy
            refine ⟨(p * y.1, p * y.2), ?_, ?_⟩
            · simp only [mem_filter, mem_product, mem_Icc, mem_range]
              have hsum : (p * y.1) ^ 2 + (p * y.2) ^ 2 = m := by
                calc (p * y.1) ^ 2 + (p * y.2) ^ 2
                    = p ^ 2 * (y.1 ^ 2 + y.2 ^ 2) := by ring
                  _ = p ^ 2 * m' := by rw [hy.2]
                  _ = m := hm'_eq
              refine ⟨⟨⟨?_, ?_⟩, ?_⟩, hsum⟩
              · have := hpp.two_le; nlinarith
              · nlinarith
              · nlinarith
            · ext
              · exact Nat.mul_div_cancel_left y.1 hpp.pos
              · exact Nat.mul_div_cancel_left y.2 hpp.pos
        rcases ih m' hm'_lt hm'_pos with hzero | ⟨d, m0, hd, hm0, hm'eq, hd3, hm03, hrho'⟩
        · left; omega
        · right
          refine ⟨p * d, m0, mul_pos hpp.pos hd, hm0, ?_, ?_, hm03, hrho_eq.trans hrho'⟩
          · rw [← hm'_eq, hm'eq]; ring
          · intro q hq
            rw [Nat.mem_primeFactors] at hq
            rcases hq.1.dvd_mul.mp hq.2.1 with hqp | hqd
            · have := (Nat.prime_dvd_prime_iff_eq hq.1 hpp).mp hqp
              rwa [this]
            · exact hd3 q (Nat.mem_primeFactors.mpr ⟨hq.1, hqd, by omega⟩)
      · left
        unfold rho
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro x _ hsum
        have hboth := dvd_both_of_sq_add_sq_mod4_eq3 hpp hp3 (hsum.symm ▸ hpm)
        obtain ⟨a, ha⟩ := hboth.1
        obtain ⟨b, hb⟩ := hboth.2
        apply hp2
        exact ⟨a ^ 2 + b ^ 2, by rw [← hsum, ha, hb]; ring⟩

private def omega1 (p : ℕ) : ℝ :=
  if p % 4 = 1 then 2 else 1

private noncomputable def g2 (q : ℕ) : ℝ :=
  ∏ p ∈ q.primeFactors, (omega1 p / ((p : ℝ) - omega1 p))

private def goodSqfree (X : ℕ) : Finset ℕ :=
  (Finset.Icc 1 X).filter fun q => Squarefree q ∧ ∀ p ∈ q.primeFactors, p % 4 ≠ 3

private lemma sum_inv_sq_le_two (X : ℕ) :
    ∑ d ∈ Finset.Icc 1 X, (1 : ℝ) / (d : ℝ) ^ 2 ≤ 2 := by
  suffices h : ∀ k : ℕ, 1 ≤ k → ∑ d ∈ Finset.Icc 1 k, (1 : ℝ) / (d : ℝ) ^ 2 ≤ 2 - 1 / (k : ℝ) by
    rcases eq_or_ne X 0 with rfl | hX
    · simp
    · have hk : 1 ≤ X := by omega
      have := h X hk
      have hpos : (0 : ℝ) ≤ 1 / (X : ℝ) := by positivity
      linarith
  intro k hk
  induction k with
  | zero => omega
  | succ k ih =>
    rcases eq_or_ne k 0 with rfl | hk0
    · norm_num
    · have hk1 : 1 ≤ k := by omega
      have hIcc : Finset.Icc 1 (k + 1) = insert (k + 1) (Finset.Icc 1 k) := by
        ext x; simp only [mem_Icc, mem_insert]; omega
      rw [hIcc, Finset.sum_insert (by simp)]
      have hih := ih hk1
      have hk_pos : (0 : ℝ) < k := by exact_mod_cast hk1
      have hstep : (1 : ℝ) / ((k + 1 : ℕ) : ℝ) ^ 2 ≤ 1 / (k : ℝ) - 1 / ((k + 1 : ℕ) : ℝ) := by
        push_cast
        have h1 : (0 : ℝ) < k + 1 := by linarith
        have hdiff : 1 / (k : ℝ) - 1 / ((k : ℝ) + 1) = 1 / ((k : ℝ) * ((k : ℝ) + 1)) := by
          field_simp [hk_pos.ne', h1.ne']
          ring
        rw [hdiff]
        exact one_div_le_one_div_of_le (by positivity) (by nlinarith)
      linarith

private lemma sum_pow_le_geom (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) (X : ℕ) :
    ∑ k ∈ Finset.Icc 1 X, r ^ k ≤ r / (1 - r) := by
  induction X with
  | zero =>
    simp
    exact div_nonneg hr0 (by linarith)
  | succ X ih =>
    have hsum : (∑ k ∈ Finset.Icc 1 (X + 1), r ^ k) =
        r * (1 - r ^ (X + 1)) / (1 - r) := by
      clear ih
      induction X with
      | zero =>
        simp
        field_simp [show (1 : ℝ) - r ≠ 0 by linarith]
      | succ n ihn =>
        have hIcc : Finset.Icc 1 (n + 1 + 1) = insert (n + 1 + 1) (Finset.Icc 1 (n + 1)) := by
          ext x; simp only [mem_Icc, mem_insert]; omega
        rw [hIcc, Finset.sum_insert (by simp), ihn]
        have hne : (1 : ℝ) - r ≠ 0 := by linarith
        field_simp [hne]
        ring
    rw [hsum]
    have hpow : 0 ≤ r ^ (X + 1) := pow_nonneg hr0 _
    have hden : 0 < 1 - r := by linarith
    rw [div_le_div_iff_of_pos_right hden]
    nlinarith

private lemma nat_add_one_le_two_pow (k : ℕ) (hk : 1 ≤ k) : k + 1 ≤ 2 ^ k := by
  induction k with
  | zero => omega
  | succ n ih =>
    rcases eq_or_ne n 0 with rfl | hn
    · norm_num
    · have := ih (by omega)
      have : 2 ^ (n + 1) = 2 * 2 ^ n := by ring
      omega

private lemma sum_rad_eq_le_g2 (X q : ℕ) (hq : q ∈ goodSqfree X) :
    ∑ m ∈ (Finset.Icc 1 X).filter (fun m => (∏ p ∈ m.primeFactors, p) = q),
      (rhoBound m : ℝ) / (m : ℝ) ≤ g2 q := by
  simp only [goodSqfree, mem_filter, mem_Icc] at hq
  obtain ⟨⟨hq1, _⟩, hq_sq, hq_no3⟩ := hq
  set P := q.primeFactors
  set box := Fintype.piFinset (fun _ : P => Finset.Icc 1 X)
  let phi : ℕ → (P → ℕ) := fun m p => m.factorization p.1
  have hrad_pf : ∀ m ∈ (Finset.Icc 1 X).filter (fun m => (∏ p ∈ m.primeFactors, p) = q),
      m.primeFactors = P := by
    intro m hm
    simp only [mem_filter, mem_Icc] at hm
    have hrad_sq : Squarefree (∏ p ∈ m.primeFactors, p) := hm.2 ▸ hq_sq
    ext p
    simp only [P, Nat.mem_primeFactors, ne_eq]
    constructor
    · rintro ⟨hpp, hpm, _⟩
      refine ⟨hpp, ?_, by omega⟩
      rw [← hm.2]
      exact Finset.dvd_prod_of_mem _ (Nat.mem_primeFactors.mpr ⟨hpp, hpm, by omega⟩)
    · rintro ⟨hpp, hpq, _⟩
      rw [← hm.2] at hpq
      obtain ⟨r, hr_mem, hpr⟩ := hpp.prime.exists_mem_finset_dvd hpq
      have hrr : r.Prime := Nat.prime_of_mem_primeFactors hr_mem
      have heq : p = r := (Nat.prime_dvd_prime_iff_eq hpp hrr).mp hpr
      subst heq
      exact Nat.mem_primeFactors.mp hr_mem
  have hmaps : ∀ m ∈ (Finset.Icc 1 X).filter (fun m => (∏ p ∈ m.primeFactors, p) = q),
      phi m ∈ box := by
    intro m hm
    have hmpf := hrad_pf m hm
    simp only [mem_filter, mem_Icc] at hm
    simp only [box, Fintype.mem_piFinset, mem_Icc, phi]
    intro p
    have hp_mem : p.1 ∈ m.primeFactors := hmpf.symm ▸ p.2
    have hpp : p.1.Prime := Nat.prime_of_mem_primeFactors hp_mem
    have hpos : 0 < m.factorization p.1 :=
      Nat.Prime.factorization_pos_of_dvd hpp (by omega) (Nat.dvd_of_mem_primeFactors hp_mem)
    have hle : m.factorization p.1 ≤ X := by
      have h1 : p.1 ^ m.factorization p.1 ≤ m :=
        Nat.le_of_dvd (by omega) (Nat.ordProj_dvd m p.1)
      have h2 : m.factorization p.1 < 2 ^ m.factorization p.1 := Nat.lt_two_pow_self
      have h3 : 2 ^ m.factorization p.1 ≤ p.1 ^ m.factorization p.1 :=
        Nat.pow_le_pow_left hpp.two_le _
      omega
    exact ⟨hpos, hle⟩
  have hinj : Set.InjOn phi ((Finset.Icc 1 X).filter (fun m => (∏ p ∈ m.primeFactors, p) = q)) := by
    intro m₁ hm₁ m₂ hm₂ heq
    have hm₁' : m₁ ∈ (Finset.Icc 1 X).filter (fun m => (∏ p ∈ m.primeFactors, p) = q) := Finset.mem_coe.mp hm₁
    have hm₂' : m₂ ∈ (Finset.Icc 1 X).filter (fun m => (∏ p ∈ m.primeFactors, p) = q) := Finset.mem_coe.mp hm₂
    have hpf₁ := hrad_pf m₁ hm₁'
    have hpf₂ := hrad_pf m₂ hm₂'
    simp only [mem_filter, mem_Icc] at hm₁' hm₂'
    have h1 := Nat.prod_factorization_pow_eq_self (show m₁ ≠ 0 by omega)
    have h2 := Nat.prod_factorization_pow_eq_self (show m₂ ≠ 0 by omega)
    rw [← h1, ← h2]
    simp only [Finsupp.prod, Nat.support_factorization, hpf₁, hpf₂]
    refine Finset.prod_congr rfl fun p hp => ?_
    have := congrFun heq ⟨p, hp⟩
    simp only [phi] at this
    rw [this]
  let term : (P → ℕ) → ℝ := fun e =>
    ∏ p : P, (if p.1 % 4 = 1 then ((e p : ℝ) + 1) else 1) / (p.1 : ℝ) ^ (e p)
  have hterm_eq : ∀ m ∈ (Finset.Icc 1 X).filter (fun m => (∏ p ∈ m.primeFactors, p) = q),
      (rhoBound m : ℝ) / (m : ℝ) = term (phi m) := by
    intro m hm
    have hpf := hrad_pf m hm
    simp only [mem_filter, mem_Icc] at hm
    have hm_prod : (m : ℝ) = ∏ p : P, (p.1 : ℝ) ^ (m.factorization p.1) := by
      have h1 := Nat.prod_factorization_pow_eq_self (show m ≠ 0 by omega)
      conv_lhs => rw [← h1]
      simp only [Finsupp.prod, Nat.support_factorization, hpf]
      rw [Nat.cast_prod, ← Finset.prod_attach (s := P)]
      exact Finset.prod_congr rfl fun p _ => Nat.cast_pow p.1 _
    have hrb_prod : (rhoBound m : ℝ) =
        ∏ p : P, (if p.1 % 4 = 1 then ((m.factorization p.1 : ℝ) + 1) else 1) := by
      unfold rhoBound
      rw [hpf, Nat.cast_prod, Finset.prod_filter, ← Finset.prod_attach (s := P)]
      refine Finset.prod_congr rfl fun p _ => by split_ifs <;> simp
    rw [hrb_prod, hm_prod, ← Finset.prod_div_distrib]
  have hsum_le_box :
      ∑ m ∈ (Finset.Icc 1 X).filter (fun m => (∏ p ∈ m.primeFactors, p) = q),
        (rhoBound m : ℝ) / (m : ℝ) ≤ ∑ e ∈ box, term e := by
    calc ∑ m ∈ (Finset.Icc 1 X).filter (fun m => (∏ p ∈ m.primeFactors, p) = q),
            (rhoBound m : ℝ) / (m : ℝ)
        = ∑ m ∈ (Finset.Icc 1 X).filter (fun m => (∏ p ∈ m.primeFactors, p) = q),
            term (phi m) := Finset.sum_congr rfl hterm_eq
      _ = ∑ e ∈ ((Finset.Icc 1 X).filter (fun m => (∏ p ∈ m.primeFactors, p) = q)).image phi,
            term e := (Finset.sum_image hinj).symm
      _ ≤ ∑ e ∈ box, term e := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun e _ _ => ?_)
          · intro e he
            obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp he
            exact hmaps m hm
          · exact Finset.prod_nonneg fun p _ => by split_ifs <;> positivity
  have hbox_eq : ∑ e ∈ box, term e =
      ∏ p : P, ∑ k ∈ Finset.Icc 1 X,
        (if p.1 % 4 = 1 then ((k : ℝ) + 1) else 1) / (p.1 : ℝ) ^ k :=
    Finset.sum_prod_piFinset (Finset.Icc 1 X) fun (p : P) (k : ℕ) =>
      (if p.1 % 4 = 1 then ((k : ℝ) + 1) else 1) / (p.1 : ℝ) ^ k
  have hfactor : ∀ p : P,
      (∑ k ∈ Finset.Icc 1 X, (if p.1 % 4 = 1 then ((k : ℝ) + 1) else 1) / (p.1 : ℝ) ^ k) ≤
      omega1 p.1 / ((p.1 : ℝ) - omega1 p.1) := by
    intro p
    have hpp : p.1.Prime := Nat.prime_of_mem_primeFactors p.2
    have hne3 : p.1 % 4 ≠ 3 := hq_no3 p.1 p.2
    by_cases hp1 : p.1 % 4 = 1
    · have hp5 : (5 : ℝ) ≤ p.1 := by
        exact_mod_cast (by have := hpp.two_le; omega : 5 ≤ p.1)
      have hr0 : (0 : ℝ) ≤ 2 / (p.1 : ℝ) := by positivity
      have hr1 : (2 : ℝ) / (p.1 : ℝ) < 1 := by
        rw [div_lt_one (by linarith)]; linarith
      have hterm_le : ∀ k ∈ Finset.Icc 1 X,
          ((k : ℝ) + 1) / (p.1 : ℝ) ^ k ≤ ((2 : ℝ) / (p.1 : ℝ)) ^ k := by
        intro k hk
        simp only [mem_Icc] at hk
        rw [div_pow]
        gcongr
        exact_mod_cast nat_add_one_le_two_pow k hk.1
      have hgeom := sum_pow_le_geom ((2 : ℝ) / (p.1 : ℝ)) hr0 hr1 X
      have hrhs : (2 / (p.1 : ℝ)) / (1 - 2 / (p.1 : ℝ)) = omega1 p.1 / ((p.1 : ℝ) - omega1 p.1) := by
        simp only [omega1, hp1, ite_true]
        have hp0 : (p.1 : ℝ) ≠ 0 := by linarith
        have hpm2 : (p.1 : ℝ) - 2 ≠ 0 := by linarith
        field_simp [hp0, hpm2]
      calc ∑ k ∈ Finset.Icc 1 X, (if p.1 % 4 = 1 then ((k : ℝ) + 1) else 1) / (p.1 : ℝ) ^ k
          = ∑ k ∈ Finset.Icc 1 X, ((k : ℝ) + 1) / (p.1 : ℝ) ^ k := by simp [hp1]
        _ ≤ ∑ k ∈ Finset.Icc 1 X, ((2 : ℝ) / (p.1 : ℝ)) ^ k := Finset.sum_le_sum hterm_le
        _ ≤ (2 / (p.1 : ℝ)) / (1 - 2 / (p.1 : ℝ)) := hgeom
        _ = omega1 p.1 / ((p.1 : ℝ) - omega1 p.1) := hrhs
    · have hp2 : p.1 = 2 := by
        rcases hpp.eq_two_or_odd with h2 | hodd
        · exact h2
        · omega
      have hnot1 : p.1 % 4 ≠ 1 := hp1
      have hr0 : (0 : ℝ) ≤ 1 / (p.1 : ℝ) := by positivity
      have hr1 : (1 : ℝ) / (p.1 : ℝ) < 1 := by
        rw [hp2]; norm_num
      have hgeom := sum_pow_le_geom ((1 : ℝ) / (p.1 : ℝ)) hr0 hr1 X
      have hrhs : (1 / (p.1 : ℝ)) / (1 - 1 / (p.1 : ℝ)) = omega1 p.1 / ((p.1 : ℝ) - omega1 p.1) := by
        simp only [omega1, hnot1, ite_false, hp2, Nat.cast_ofNat]
        norm_num
      calc ∑ k ∈ Finset.Icc 1 X, (if p.1 % 4 = 1 then ((k : ℝ) + 1) else 1) / (p.1 : ℝ) ^ k
          = ∑ k ∈ Finset.Icc 1 X, ((1 : ℝ) / (p.1 : ℝ)) ^ k := by
            refine Finset.sum_congr rfl fun k _ => ?_
            simp [hnot1, div_pow]
        _ ≤ (1 / (p.1 : ℝ)) / (1 - 1 / (p.1 : ℝ)) := hgeom
        _ = omega1 p.1 / ((p.1 : ℝ) - omega1 p.1) := hrhs
  have hprod_le : ∏ p : P,
      (∑ k ∈ Finset.Icc 1 X, (if p.1 % 4 = 1 then ((k : ℝ) + 1) else 1) / (p.1 : ℝ) ^ k) ≤ g2 q := by
    unfold g2
    rw [← Finset.prod_attach (s := P)]
    refine Finset.prod_le_prod (fun p _ => ?_) (fun p _ => hfactor p)
    exact Finset.sum_nonneg fun k _ => by split_ifs <;> positivity
  exact hsum_le_box.trans (hbox_eq.le.trans hprod_le)

private lemma sum_rho_div_ge_log_div_20 (X : ℕ) (hX : 100 ≤ X) :
    Real.log X / 20 ≤ ∑ m ∈ Finset.Icc 1 X, (rho m : ℝ) / (m : ℝ) := by
  -- Express ∑_{m=1}^X rho(m)/m as a sum over lattice points (a, b) with 1 ≤ a, a^2 + b^2 ≤ X
  set L := (Finset.Icc 1 X ×ˢ Finset.range (X + 1)).filter fun x => x.1 ^ 2 + x.2 ^ 2 ≤ X
  have hlattice : ∑ m ∈ Finset.Icc 1 X, (rho m : ℝ) / (m : ℝ) =
      ∑ x ∈ L, (1 : ℝ) / ((x.1 ^ 2 + x.2 ^ 2 : ℕ) : ℝ) := by
    have hfib : L = (Finset.Icc 1 X).biUnion fun m =>
        (Finset.Icc 1 m ×ˢ Finset.range (m + 1)).filter fun x => x.1 ^ 2 + x.2 ^ 2 = m := by
      ext x
      simp only [L, mem_filter, mem_product, mem_Icc, mem_range, mem_biUnion]
      constructor
      · rintro ⟨⟨⟨hx1, _⟩, _⟩, hle⟩
        refine ⟨x.1 ^ 2 + x.2 ^ 2, ⟨by nlinarith, hle⟩, ⟨⟨⟨hx1, ?_⟩, ?_⟩, rfl⟩⟩
        · nlinarith
        · nlinarith
      · rintro ⟨m, ⟨hm1, hmX⟩, ⟨⟨⟨hx1, _⟩, _⟩, heq⟩⟩
        refine ⟨⟨⟨hx1, ?_⟩, ?_⟩, by omega⟩
        · nlinarith
        · nlinarith
    have hdisj : Set.PairwiseDisjoint (Finset.Icc 1 X : Set ℕ) fun m =>
        (Finset.Icc 1 m ×ˢ Finset.range (m + 1)).filter fun x => x.1 ^ 2 + x.2 ^ 2 = m := by
      intro m₁ _ m₂ _ hne
      simp only [Function.onFun, Finset.disjoint_left]
      intro x hx₁ hx₂
      simp only [mem_filter] at hx₁ hx₂
      exact hne (hx₁.2.symm.trans hx₂.2)
    rw [hfib, Finset.sum_biUnion hdisj]
    refine Finset.sum_congr rfl fun m _ => ?_
    have hcongr : ∑ x ∈ (Finset.Icc 1 m ×ˢ Finset.range (m + 1)).filter (fun x => x.1 ^ 2 + x.2 ^ 2 = m),
        (1 : ℝ) / ((x.1 ^ 2 + x.2 ^ 2 : ℕ) : ℝ) =
        ∑ _x ∈ (Finset.Icc 1 m ×ˢ Finset.range (m + 1)).filter (fun x => x.1 ^ 2 + x.2 ^ 2 = m),
          (1 : ℝ) / (m : ℝ) := by
      refine Finset.sum_congr rfl fun x hx => ?_
      simp only [mem_filter] at hx
      rw [hx.2]
    rw [hcongr, Finset.sum_const, nsmul_eq_mul, rho]
    ring
  rw [hlattice]
  set K := Nat.log 4 (X / 5)
  have h5_le : 5 * 4 ^ K ≤ X := by
    have hdiv_ne : X / 5 ≠ 0 := by omega
    have hpow : 4 ^ K ≤ X / 5 := Nat.pow_log_le_self 4 hdiv_ne
    omega
  have hX_lt : X < 5 * 4 ^ (K + 1) := by
    have hlt : X / 5 < 4 ^ (K + 1) := Nat.lt_pow_succ_log_self (by norm_num : 1 < 4) (X / 5)
    omega
  let shell : ℕ → Finset (ℕ × ℕ) := fun k => Finset.Ico (2 ^ k) (2 ^ (k + 1)) ×ˢ Finset.range (2 ^ k)
  have hsub : (Finset.range (K + 1)).biUnion shell ⊆ L := by
    intro x hx
    simp only [mem_biUnion, mem_range, shell, mem_product, mem_Ico] at hx
    obtain ⟨k, hk, ⟨ha1, ha2⟩, hb⟩ := hx
    have h4k : 4 ^ k ≤ 4 ^ K := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h2k_sq : (2 ^ k) ^ 2 = 4 ^ k := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
    have h2k1_sq : (2 ^ (k + 1)) ^ 2 = 4 * 4 ^ k := by
      rw [pow_succ 2 k, mul_pow, h2k_sq]; ring
    have hsq_le : x.1 ^ 2 + x.2 ^ 2 ≤ 5 * 4 ^ k := by
      have h1 : x.1 ^ 2 ≤ (2 ^ (k + 1)) ^ 2 := Nat.pow_le_pow_left ha2.le 2
      have h2 : x.2 ^ 2 ≤ (2 ^ k) ^ 2 := Nat.pow_le_pow_left hb.le 2
      omega
    have hleX : x.1 ^ 2 + x.2 ^ 2 ≤ X := by nlinarith
    have ha_pos : 1 ≤ x.1 := le_trans (Nat.one_le_pow k 2 (by norm_num)) ha1
    simp only [L, mem_filter, mem_product, mem_Icc, mem_range]
    exact ⟨⟨⟨ha_pos, by nlinarith⟩, by nlinarith⟩, hleX⟩
  have hdisj : Set.PairwiseDisjoint (Finset.range (K + 1) : Set ℕ) shell := by
    intro k₁ _ k₂ _ hne
    simp only [Function.onFun, Finset.disjoint_left]
    intro x hx₁ hx₂
    simp only [shell, mem_product, mem_Ico, mem_range] at hx₁ hx₂
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have : 2 ^ (k₁ + 1) ≤ 2 ^ k₂ := Nat.pow_le_pow_right (by norm_num) hlt
      omega
    · have : 2 ^ (k₂ + 1) ≤ 2 ^ k₁ := Nat.pow_le_pow_right (by norm_num) hgt
      omega
  have hshell_lb : ∀ k ∈ Finset.range (K + 1),
      (1 : ℝ) / 5 ≤ ∑ x ∈ shell k, (1 : ℝ) / ((x.1 ^ 2 + x.2 ^ 2 : ℕ) : ℝ) := by
    intro k _
    have hcard : (shell k).card = 4 ^ k := by
      simp only [shell, Finset.card_product, Nat.card_Ico, Finset.card_range]
      have h1 : 2 ^ (k + 1) - 2 ^ k = 2 ^ k := by
        rw [pow_succ]; omega
      rw [h1, ← sq, ← pow_mul, mul_comm, pow_mul]; norm_num
    have hterm : ∀ x ∈ shell k, (1 : ℝ) / (5 * (4 : ℝ) ^ k) ≤ (1 : ℝ) / ((x.1 ^ 2 + x.2 ^ 2 : ℕ) : ℝ) := by
      intro x hx
      simp only [shell, mem_product, mem_Ico, mem_range] at hx
      have h2k_sq : (2 ^ k) ^ 2 = 4 ^ k := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
      have h2k1_sq : (2 ^ (k + 1)) ^ 2 = 4 * 4 ^ k := by
        rw [pow_succ 2 k, mul_pow, h2k_sq]; ring
      have hsq_le : x.1 ^ 2 + x.2 ^ 2 ≤ 5 * 4 ^ k := by
        have h1 : x.1 ^ 2 ≤ (2 ^ (k + 1)) ^ 2 := Nat.pow_le_pow_left hx.1.2.le 2
        have h2 : x.2 ^ 2 ≤ (2 ^ k) ^ 2 := Nat.pow_le_pow_left hx.2.le 2
        omega
      have ha_pos : 0 < x.1 := lt_of_lt_of_le (pow_pos (by norm_num) k) hx.1.1
      have hpos : (0 : ℝ) < ((x.1 ^ 2 + x.2 ^ 2 : ℕ) : ℝ) := by positivity
      gcongr
      exact_mod_cast hsq_le
    calc (1 : ℝ) / 5
        = ((4 ^ k : ℕ) : ℝ) * ((1 : ℝ) / (5 * (4 : ℝ) ^ k)) := by
          push_cast; field_simp
      _ = ((shell k).card : ℝ) * ((1 : ℝ) / (5 * (4 : ℝ) ^ k)) := by rw [hcard]
      _ = ∑ _x ∈ shell k, (1 : ℝ) / (5 * (4 : ℝ) ^ k) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ x ∈ shell k, (1 : ℝ) / ((x.1 ^ 2 + x.2 ^ 2 : ℕ) : ℝ) := Finset.sum_le_sum hterm
  have hsum_lb : ((K + 1 : ℕ) : ℝ) / 5 ≤ ∑ x ∈ L, (1 : ℝ) / ((x.1 ^ 2 + x.2 ^ 2 : ℕ) : ℝ) := calc
    ((K + 1 : ℕ) : ℝ) / 5
        = ∑ _k ∈ Finset.range (K + 1), (1 : ℝ) / 5 := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
    _ ≤ ∑ k ∈ Finset.range (K + 1), ∑ x ∈ shell k, (1 : ℝ) / ((x.1 ^ 2 + x.2 ^ 2 : ℕ) : ℝ) :=
          Finset.sum_le_sum hshell_lb
    _ = ∑ x ∈ (Finset.range (K + 1)).biUnion shell, (1 : ℝ) / ((x.1 ^ 2 + x.2 ^ 2 : ℕ) : ℝ) :=
          (Finset.sum_biUnion hdisj).symm
    _ ≤ ∑ x ∈ L, (1 : ℝ) / ((x.1 ^ 2 + x.2 ^ 2 : ℕ) : ℝ) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
  have hlog_le : Real.log X ≤ 4 * ((K + 1 : ℕ) : ℝ) := by
    have hX_pos : (0 : ℝ) < X := by exact_mod_cast (by omega : 0 < X)
    have hX_lt_real : (X : ℝ) < (5 : ℝ) * (4 : ℝ) ^ (K + 1) := by exact_mod_cast hX_lt
    have hlog5 : Real.log 5 ≤ 2 := by
      have : (5 : ℝ) ≤ Real.exp 2 := by
        have h1 : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
        have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
        nlinarith
      exact (Real.log_le_iff_le_exp (by norm_num)).mpr this
    have hlog4 : Real.log 4 ≤ 2 := by
      exact (Real.log_le_log (by norm_num) (by norm_num : (4 : ℝ) ≤ 5)).trans hlog5
    have h1 : Real.log X ≤ Real.log ((5 : ℝ) * (4 : ℝ) ^ (K + 1)) :=
      Real.log_le_log hX_pos hX_lt_real.le
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow] at h1
    have hK1 : (1 : ℝ) ≤ ((K + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ K + 1)
    nlinarith
  linarith

private lemma sum_g2_ge_log_div_40 (X : ℕ) (hX : 100 ≤ X) :
    Real.log X / 40 ≤ ∑ q ∈ goodSqfree X, g2 q := by
  set goodM := (Finset.Icc 1 X).filter fun m => ∀ p ∈ m.primeFactors, p % 4 ≠ 3
  -- Step 1: ∑_{m=1}^X rho(m)/m ≤ 2 * ∑_{m ∈ goodM} rho(m)/m
  have hstep1 : ∑ m ∈ Finset.Icc 1 X, (rho m : ℝ) / (m : ℝ) ≤
      2 * ∑ m ∈ goodM, (rho m : ℝ) / (m : ℝ) := by
    set posM := (Finset.Icc 1 X).filter fun m => 0 < rho m
    have hpos_eq : ∑ m ∈ Finset.Icc 1 X, (rho m : ℝ) / (m : ℝ) =
        ∑ m ∈ posM, (rho m : ℝ) / (m : ℝ) := by
      symm
      refine Finset.sum_subset (Finset.filter_subset _ _) fun m hm hnot => ?_
      simp only [posM, mem_filter] at hnot
      have h0 : rho m = 0 := by
        by_contra hne
        exact hnot ⟨hm, Nat.pos_of_ne_zero hne⟩
      simp [h0]
    rw [hpos_eq]
    have hdec : ∀ m ∈ posM, ∃ d m0 : ℕ, 0 < d ∧ 0 < m0 ∧ m = d ^ 2 * m0 ∧
        (∀ p ∈ d.primeFactors, p % 4 = 3) ∧
        (∀ p ∈ m0.primeFactors, p % 4 ≠ 3) ∧ rho m = rho m0 := by
      intro m hm
      simp only [posM, mem_filter, mem_Icc] at hm
      rcases rho_decomp m (by omega) with h0 | h
      · omega
      · exact h
    let psi : ℕ → ℕ × ℕ := fun m =>
      if hm : m ∈ posM then
        (Classical.choose (hdec m hm), Classical.choose (Classical.choose_spec (hdec m hm)))
      else (0, 0)
    have hmaps : ∀ m ∈ posM, psi m ∈ Finset.Icc 1 X ×ˢ goodM := by
      intro m hm
      simp only [psi, dif_pos hm]
      set d := Classical.choose (hdec m hm)
      set m0 := Classical.choose (Classical.choose_spec (hdec m hm))
      have hspec := Classical.choose_spec (Classical.choose_spec (hdec m hm))
      have hm_le : m ≤ X := (Finset.mem_Icc.mp (Finset.mem_filter.mp hm).1).2
      have hd_le_m : d ≤ m := by
        have h1 : d ≤ d ^ 2 := by nlinarith [hspec.1]
        have h2 : d ^ 2 ≤ d ^ 2 * m0 := Nat.le_mul_of_pos_right _ hspec.2.1
        rw [hspec.2.2.1]
        exact h1.trans h2
      have hm0_le_m : m0 ≤ m := by
        have h1 : 1 ≤ d ^ 2 := Nat.one_le_pow 2 d hspec.1
        have h2 : m0 ≤ d ^ 2 * m0 := Nat.le_mul_of_pos_left _ h1
        rw [hspec.2.2.1]
        exact h2
      simp only [goodM, mem_product, mem_filter, mem_Icc]
      exact ⟨⟨hspec.1, hd_le_m.trans hm_le⟩, ⟨⟨hspec.2.1, hm0_le_m.trans hm_le⟩, hspec.2.2.2.2.1⟩⟩
    have hinj : Set.InjOn psi posM := by
      intro m₁ hm₁ m₂ hm₂ heq
      have hm₁' : m₁ ∈ posM := Finset.mem_coe.mp hm₁
      have hm₂' : m₂ ∈ posM := Finset.mem_coe.mp hm₂
      simp only [psi, dif_pos hm₁', dif_pos hm₂'] at heq
      set d₁ := Classical.choose (hdec m₁ hm₁')
      set m0₁ := Classical.choose (Classical.choose_spec (hdec m₁ hm₁'))
      have h1 := Classical.choose_spec (Classical.choose_spec (hdec m₁ hm₁'))
      set d₂ := Classical.choose (hdec m₂ hm₂')
      set m0₂ := Classical.choose (Classical.choose_spec (hdec m₂ hm₂'))
      have h2 := Classical.choose_spec (Classical.choose_spec (hdec m₂ hm₂'))
      have hd : d₁ = d₂ := congrArg Prod.fst heq
      have hm0 : m0₁ = m0₂ := congrArg Prod.snd heq
      calc m₁ = d₁ ^ 2 * m0₁ := h1.2.2.1
        _ = d₂ ^ 2 * m0₂ := by rw [hd, hm0]
        _ = m₂ := h2.2.2.1.symm
    let termP : ℕ × ℕ → ℝ := fun x => ((1 : ℝ) / (x.1 : ℝ) ^ 2) * ((rho x.2 : ℝ) / (x.2 : ℝ))
    have hterm_eq : ∀ m ∈ posM, (rho m : ℝ) / (m : ℝ) = termP (psi m) := by
      intro m hm
      simp only [psi, dif_pos hm, termP]
      set d := Classical.choose (hdec m hm)
      set m0 := Classical.choose (Classical.choose_spec (hdec m hm))
      have hspec := Classical.choose_spec (Classical.choose_spec (hdec m hm))
      have hm_eq : m = d ^ 2 * m0 := hspec.2.2.1
      have hrho_eq : rho m = rho m0 := hspec.2.2.2.2.2
      calc (rho m : ℝ) / (m : ℝ)
          = (rho m0 : ℝ) / ((d ^ 2 * m0 : ℕ) : ℝ) := by rw [hrho_eq, hm_eq]
        _ = ((1 : ℝ) / (d : ℝ) ^ 2) * ((rho m0 : ℝ) / (m0 : ℝ)) := by push_cast; ring
    have hprod_sum : ∑ x ∈ Finset.Icc 1 X ×ˢ goodM, termP x =
        (∑ d ∈ Finset.Icc 1 X, (1 : ℝ) / (d : ℝ) ^ 2) *
        (∑ m0 ∈ goodM, (rho m0 : ℝ) / (m0 : ℝ)) := by
      rw [Finset.sum_product, Finset.sum_mul]
      refine Finset.sum_congr rfl fun d _ => ?_
      rw [Finset.mul_sum]
    calc ∑ m ∈ posM, (rho m : ℝ) / (m : ℝ)
        = ∑ m ∈ posM, termP (psi m) := Finset.sum_congr rfl hterm_eq
      _ = ∑ x ∈ posM.image psi, termP x := (Finset.sum_image hinj).symm
      _ ≤ ∑ x ∈ Finset.Icc 1 X ×ˢ goodM, termP x := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => by simp only [termP]; positivity)
          intro x hx
          obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hx
          exact hmaps m hm
      _ = (∑ d ∈ Finset.Icc 1 X, (1 : ℝ) / (d : ℝ) ^ 2) *
          (∑ m0 ∈ goodM, (rho m0 : ℝ) / (m0 : ℝ)) := hprod_sum
      _ ≤ 2 * ∑ m0 ∈ goodM, (rho m0 : ℝ) / (m0 : ℝ) :=
          mul_le_mul_of_nonneg_right (sum_inv_sq_le_two X)
            (Finset.sum_nonneg fun _ _ => by positivity)
  -- Step 2: ∑_{m ∈ goodM} rho(m)/m ≤ ∑_{q ∈ goodSqfree X} g2 q
  have hstep2 : ∑ m ∈ goodM, (rho m : ℝ) / (m : ℝ) ≤ ∑ q ∈ goodSqfree X, g2 q := by
    have hrad_mem : ∀ m ∈ goodM, (∏ p ∈ m.primeFactors, p) ∈ goodSqfree X := by
      intro m hm
      simp only [goodM, mem_filter, mem_Icc] at hm
      have hrad_dvd : (∏ p ∈ m.primeFactors, p) ∣ m := Nat.prod_primeFactors_dvd m
      have hrad_pos : 0 < ∏ p ∈ m.primeFactors, p :=
        Finset.prod_pos fun p hp => (Nat.prime_of_mem_primeFactors hp).pos
      have hrad_sq : Squarefree (∏ p ∈ m.primeFactors, p) := by
        rw [Nat.squarefree_iff_prime_squarefree]
        intro p hpp hp2
        have hp_in : p ∈ m.primeFactors := by
          have hp_dvd : p ∣ ∏ r ∈ m.primeFactors, r := dvd_trans (dvd_mul_right p p) hp2
          obtain ⟨r, hr, hpr⟩ := hpp.prime.exists_mem_finset_dvd hp_dvd
          have := (Nat.prime_dvd_prime_iff_eq hpp (Nat.prime_of_mem_primeFactors hr)).mp hpr
          rwa [this]
        rw [← Finset.mul_prod_erase _ _ hp_in] at hp2
        have hp_dvd_rest : p ∣ ∏ r ∈ m.primeFactors.erase p, r :=
          (mul_dvd_mul_iff_left hpp.ne_zero).mp hp2
        obtain ⟨r, hr, hpr⟩ := hpp.prime.exists_mem_finset_dvd hp_dvd_rest
        have hr_mem := Finset.mem_erase.mp hr
        exact hr_mem.1 ((Nat.prime_dvd_prime_iff_eq hpp (Nat.prime_of_mem_primeFactors hr_mem.2)).mp hpr).symm
      simp only [goodSqfree, mem_filter, mem_Icc]
      refine ⟨⟨hrad_pos, (Nat.le_of_dvd (by omega) hrad_dvd).trans hm.1.2⟩, hrad_sq, ?_⟩
      intro p hp
      rw [Nat.mem_primeFactors] at hp
      exact hm.2 p (Nat.mem_primeFactors.mpr ⟨hp.1, dvd_trans hp.2.1 hrad_dvd, by omega⟩)
    have hfib : ∑ m ∈ goodM, (rho m : ℝ) / (m : ℝ) =
        ∑ q ∈ goodSqfree X, ∑ m ∈ goodM.filter (fun m => (∏ p ∈ m.primeFactors, p) = q),
          (rho m : ℝ) / (m : ℝ) := by
      rw [Finset.sum_fiberwise_of_maps_to hrad_mem]
    rw [hfib]
    refine Finset.sum_le_sum fun q hq => ?_
    calc ∑ m ∈ goodM.filter (fun m => (∏ p ∈ m.primeFactors, p) = q), (rho m : ℝ) / (m : ℝ)
        ≤ ∑ m ∈ goodM.filter (fun m => (∏ p ∈ m.primeFactors, p) = q), (rhoBound m : ℝ) / (m : ℝ) := by
          refine Finset.sum_le_sum fun m hm => ?_
          simp only [goodM, mem_filter, mem_Icc] at hm
          gcongr
          exact_mod_cast rho_le_rhoBound m (by omega) hm.1.2
      _ ≤ ∑ m ∈ (Finset.Icc 1 X).filter (fun m => (∏ p ∈ m.primeFactors, p) = q),
            (rhoBound m : ℝ) / (m : ℝ) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => by positivity)
          intro m hm
          simp only [goodM, mem_filter] at hm ⊢
          exact ⟨hm.1.1, hm.2⟩
      _ ≤ g2 q := sum_rad_eq_le_g2 X q hq
  have hlog := sum_rho_div_ge_log_div_20 X hX
  linarith

/- ### Part 3: Selberg Sieve, CRT remainder bound, and final disproof -/

private lemma sum_divisors_moebius_real (k : ℕ) (hk : 0 < k) :
    ∑ d ∈ k.divisors, ((μ d : ℤ) : ℝ) = if k = 1 then 1 else 0 := by
  have h1 : ((μ * (ArithmeticFunction.zeta : ArithmeticFunction ℤ)) k : ℝ) =
      ((1 : ArithmeticFunction ℤ) k : ℝ) := by
    rw [ArithmeticFunction.moebius_mul_coe_zeta]
  rw [ArithmeticFunction.mul_apply] at h1
  have h2 : (∑ x ∈ k.divisorsAntidiagonal, μ x.1 * (ArithmeticFunction.zeta : ArithmeticFunction ℤ) x.2) =
      ∑ d ∈ k.divisors, μ d := by
    rw [Nat.sum_divisorsAntidiagonal (fun d e => μ d * (ArithmeticFunction.zeta : ArithmeticFunction ℤ) e)]
    refine Finset.sum_congr rfl fun d hd => ?_
    have hkd : k / d ≠ 0 := by
      have hd_dvd : d ∣ k := Nat.dvd_of_mem_divisors hd
      have hd_le : d ≤ k := Nat.le_of_dvd hk hd_dvd
      have hd_pos : 0 < d := Nat.pos_of_mem_divisors hd
      exact (Nat.div_pos hd_le hd_pos).ne'
    simp [ArithmeticFunction.zeta_apply, hkd]
  rw [h2] at h1
  simpa [ArithmeticFunction.one_apply] using h1

private lemma selberg_sieve_upper_bound (s : BoundingSieve) (z : ℕ) (hz : 1 ≤ z)
    (Crem : ℝ) (hCrem : 0 ≤ Crem)
    (hrem : ∀ d, d ∣ s.prodPrimes → |s.rem d| ≤ Crem * (d : ℝ)) :
    s.siftedSum ≤
      s.totalMass / (∑ l ∈ s.prodPrimes.divisors.filter (· ≤ z), s.selbergTerms l) +
        Crem * (z : ℝ) ^ 4 := by
  set P := s.prodPrimes
  have hP0 : P ≠ 0 := s.prodPrimes_ne_zero
  have hPsq : Squarefree P := s.prodPrimes_squarefree
  set D := P.divisors
  set Dz := D.filter (· ≤ z)
  set L : ℝ := ∑ l ∈ Dz, s.selbergTerms l
  have h1_mem_Dz : 1 ∈ Dz := by
    simp [Dz, D, Nat.mem_divisors, hP0, hz]
  have hL_pos : 0 < L := by
    have h1_pos : 0 < s.selbergTerms 1 := s.selbergTerms_pos (one_dvd P)
    have hle : s.selbergTerms 1 ≤ L :=
      Finset.single_le_sum (fun l hl => by
        simp only [Dz, D, mem_filter, Nat.mem_divisors] at hl
        exact (s.selbergTerms_pos hl.1.1).le) h1_mem_Dz
    linarith
  let w : ℕ → ℝ := fun d =>
    if d ∣ P ∧ d ≤ z then
      ((μ d : ℤ) : ℝ) / (s.nu d * L) *
        ∑ l ∈ Dz.filter (fun l => d ∣ l), s.selbergTerms l
    else 0
  have hw1 : w 1 = 1 := by
    have hcond : 1 ∣ P ∧ 1 ≤ z := ⟨one_dvd P, hz⟩
    simp only [w, if_pos hcond, ArithmeticFunction.moebius_apply_one, Int.cast_one,
      s.nu_mult.map_one, one_mul]
    have hfilt : Dz.filter (fun l => 1 ∣ l) = Dz := by
      ext l; simp
    rw [hfilt]
    change (1 : ℝ) / L * L = 1
    exact div_mul_cancel₀ 1 hL_pos.ne'
  have hupper := BoundingSieve.upperMoebius_lambdaSquared w hw1
  have hbase := s.siftedSum_le_mainSum_errSum_of_upperMoebius (BoundingSieve.lambdaSquared w) hupper
  -- Step 1: Compute mainSum = L⁻¹
  have hmain : s.mainSum (BoundingSieve.lambdaSquared w) = L⁻¹ := by
    rw [s.mainSum_lambdaSquared_eq_sum_mul_sum_sq w]
    have hinner : ∀ l ∈ D,
        (∑ d ∈ D, if l ∣ d then s.nu d * w d else 0) =
        if l ≤ z then ((μ l : ℤ) : ℝ) * s.selbergTerms l / L else 0 := by
      intro l hl
      have hlP : l ∣ P := (Nat.mem_divisors.mp hl).1
      have hl_pos : 0 < l := Nat.pos_of_mem_divisors hl
      have hl_sq : Squarefree l := hPsq.squarefree_of_dvd hlP
      have hstep1 : (∑ d ∈ D, if l ∣ d then s.nu d * w d else 0) =
          ∑ d ∈ Dz.filter (fun d => l ∣ d),
            ((μ d : ℤ) : ℝ) / L * ∑ m ∈ Dz.filter (fun m => d ∣ m), s.selbergTerms m := by
        rw [← Finset.sum_filter]
        have hsub : Dz.filter (fun d => l ∣ d) ⊆ D.filter (fun d => l ∣ d) := by
          intro d hd
          simp only [Dz, mem_filter] at hd ⊢
          exact ⟨hd.1.1, hd.2⟩
        rw [← Finset.sum_subset hsub]
        · refine Finset.sum_congr rfl fun d hd => ?_
          simp only [Dz, D, mem_filter, Nat.mem_divisors] at hd
          have hcond : d ∣ P ∧ d ≤ z := ⟨hd.1.1.1, hd.1.2⟩
          simp only [w, if_pos hcond]
          have hnu : s.nu d ≠ 0 := s.nu_ne_zero hd.1.1.1
          field_simp [hnu, hL_pos.ne']
        · intro d hd hnot
          simp only [Dz, D, mem_filter, Nat.mem_divisors] at hd hnot
          have hnotle : ¬ d ≤ z := fun hle => hnot ⟨⟨hd.1, hle⟩, hd.2⟩
          have hcond : ¬ (d ∣ P ∧ d ≤ z) := fun hc => hnotle hc.2
          simp [w, if_neg hcond]
      rw [hstep1]
      have hswap : (∑ d ∈ Dz.filter (fun d => l ∣ d),
            ((μ d : ℤ) : ℝ) / L * ∑ m ∈ Dz.filter (fun m => d ∣ m), s.selbergTerms m) =
          ∑ m ∈ Dz.filter (fun m => l ∣ m),
            (s.selbergTerms m / L) *
              ∑ d ∈ D.filter (fun d => l ∣ d ∧ d ∣ m), ((μ d : ℤ) : ℝ) := by
        simp_rw [Finset.mul_sum]
        have hlhs : (∑ d ∈ Dz.filter (fun d => l ∣ d), ∑ m ∈ Dz.filter (fun m => d ∣ m),
              ((μ d : ℤ) : ℝ) / L * s.selbergTerms m) =
            ∑ d ∈ Dz, ∑ m ∈ Dz,
              if l ∣ d ∧ d ∣ m then ((μ d : ℤ) : ℝ) / L * s.selbergTerms m else 0 := by
          simp_rw [Finset.sum_filter]
          refine Finset.sum_congr rfl fun d _ => ?_
          split_ifs with hld
          · refine Finset.sum_congr rfl fun m _ => by simp [hld]
          · simp [hld]
        rw [hlhs, Finset.sum_comm]
        simp_rw [Finset.sum_filter]
        refine Finset.sum_congr rfl fun m hm => ?_
        have hmP : m ∣ P := (Nat.mem_divisors.mp (Finset.mem_filter.mp hm).1).1
        have hm_le : m ≤ z := (Finset.mem_filter.mp hm).2
        have hm_pos : 0 < m := Nat.pos_of_mem_divisors (Finset.mem_filter.mp hm).1
        split_ifs with hlm
        · have heq_sub : ∑ d ∈ Dz, (if l ∣ d ∧ d ∣ m then ((μ d : ℤ) : ℝ) / L * s.selbergTerms m else 0) =
              ∑ d ∈ D, (if l ∣ d ∧ d ∣ m then s.selbergTerms m / L * ((μ d : ℤ) : ℝ) else 0) := by
            symm
            rw [← Finset.sum_subset (Finset.filter_subset (· ≤ z) D)]
            · refine Finset.sum_congr rfl fun d _ => by split_ifs <;> ring
            · intro d hd hnot
              simp only [Dz, mem_filter] at hnot
              split_ifs with hdm
              · exfalso
                exact hnot ⟨hd, (Nat.le_of_dvd hm_pos hdm.2).trans hm_le⟩
              · rfl
          exact heq_sub
        · refine Finset.sum_eq_zero fun d _ => ?_
          split_ifs with hdm
          · exact (hlm (dvd_trans hdm.1 hdm.2)).elim
          · rfl
      rw [hswap]
      have hmob_eval : ∀ m ∈ Dz.filter (fun m => l ∣ m),
          ∑ d ∈ D.filter (fun d => l ∣ d ∧ d ∣ m), ((μ d : ℤ) : ℝ) =
          if m = l then ((μ l : ℤ) : ℝ) else 0 := by
        intro m hm
        simp only [Dz, D, mem_filter, Nat.mem_divisors] at hm
        have hmP : m ∣ P := hm.1.1.1
        have hm_pos : 0 < m := Nat.pos_of_ne_zero (ne_zero_of_dvd_ne_zero hP0 hmP)
        have hlm : l ∣ m := hm.2
        have hm_sq : Squarefree m := hPsq.squarefree_of_dvd hmP
        set k := m / l
        have hlk : l * k = m := Nat.mul_div_cancel' hlm
        have hk_pos : 0 < k := Nat.div_pos (Nat.le_of_dvd hm_pos hlm) hl_pos
        have hcop : l.Coprime k := (Nat.squarefree_mul_iff.mp (hlk.symm ▸ hm_sq)).1
        have hbij : ∑ d ∈ D.filter (fun d => l ∣ d ∧ d ∣ m), ((μ d : ℤ) : ℝ) =
            ∑ t ∈ k.divisors, ((μ (l * t) : ℤ) : ℝ) := by
          refine Finset.sum_bij (fun d _ => d / l) ?_ ?_ ?_ ?_
          · intro d hd
            simp only [D, mem_filter, Nat.mem_divisors] at hd ⊢
            refine ⟨?_, hk_pos.ne'⟩
            have h1 : l * (d / l) ∣ l * k := by rw [Nat.mul_div_cancel' hd.2.1, hlk]; exact hd.2.2
            exact (mul_dvd_mul_iff_left hl_pos.ne').mp h1
          · intro d₁ hd₁ d₂ hd₂ heq
            simp only [mem_filter] at hd₁ hd₂
            rw [← Nat.mul_div_cancel' hd₁.2.1, ← Nat.mul_div_cancel' hd₂.2.1, heq]
          · intro t ht
            rw [Nat.mem_divisors] at ht
            refine ⟨l * t, ?_, Nat.mul_div_cancel_left t hl_pos⟩
            simp only [D, mem_filter, Nat.mem_divisors]
            have hlt_dvd_m : l * t ∣ m := by rw [← hlk]; exact mul_dvd_mul_left l ht.1
            exact ⟨⟨dvd_trans hlt_dvd_m hmP, hP0⟩, dvd_mul_right l t, hlt_dvd_m⟩
          · intro d hd
            simp only [mem_filter] at hd
            rw [Nat.mul_div_cancel' hd.2.1]
        rw [hbij]
        have hmul_mob : ∑ t ∈ k.divisors, ((μ (l * t) : ℤ) : ℝ) =
            ((μ l : ℤ) : ℝ) * ∑ t ∈ k.divisors, ((μ t : ℤ) : ℝ) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun t ht => ?_
          have ht_cop : l.Coprime t := hcop.coprime_dvd_right (Nat.dvd_of_mem_divisors ht)
          rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime ht_cop, Int.cast_mul]
        rw [hmul_mob, sum_divisors_moebius_real k hk_pos]
        by_cases hml : m = l
        · have hk1 : k = 1 := by
            have : l * k = l * 1 := by rw [hlk, hml, mul_one]
            exact mul_left_cancel₀ hl_pos.ne' this
          simp [hml, hk1]
        · have hk1 : k ≠ 1 := fun h => hml (by rw [← hlk, h, mul_one])
          simp [hml, hk1]
      rw [Finset.sum_congr rfl fun m hm => by rw [hmob_eval m hm]]
      by_cases hlz : l ≤ z
      · have hl_in : l ∈ Dz.filter (fun m => l ∣ m) := by
          simp [Dz, D, hl, hlz]
        rw [if_pos hlz, Finset.sum_eq_single l]
        · simp; ring
        · intro m _ hml; simp [hml]
        · intro hnot; exact (hnot hl_in).elim
      · rw [if_neg hlz]
        refine Finset.sum_eq_zero fun m hm => ?_
        simp only [Dz, mem_filter] at hm
        have hne : m ≠ l := fun h => hlz (h ▸ hm.1.2)
        simp [hne]
    rw [Finset.sum_congr rfl fun l hl => by rw [hinner l hl]]
    have hsimp : ∑ l ∈ D, (s.selbergTerms l)⁻¹ *
          (if l ≤ z then ((μ l : ℤ) : ℝ) * s.selbergTerms l / L else 0) ^ 2 =
        ∑ l ∈ Dz, s.selbergTerms l / L ^ 2 := by
      simp only [Dz, Finset.sum_filter]
      refine Finset.sum_congr rfl fun l hl => ?_
      split_ifs with hlz
      · have hlP : l ∣ P := (Nat.mem_divisors.mp hl).1
        have hgl_pos : 0 < s.selbergTerms l := s.selbergTerms_pos hlP
        have hmu2 : (((μ l : ℤ) : ℝ)) ^ 2 = 1 := by
          have := ArithmeticFunction.moebius_sq_eq_one_of_squarefree (hPsq.squarefree_of_dvd hlP)
          exact_mod_cast this
        have hsq : (((μ l : ℤ) : ℝ) * s.selbergTerms l / L) ^ 2 =
            (((μ l : ℤ) : ℝ)) ^ 2 * s.selbergTerms l ^ 2 / L ^ 2 := by ring
        rw [hsq, hmu2, one_mul]
        field_simp [hgl_pos.ne', hL_pos.ne']
      · simp
    rw [hsimp, ← Finset.sum_div]
    change L / L ^ 2 = L⁻¹
    field_simp [hL_pos.ne']
  -- Step 2: Prove |w d| ≤ 1
  have hw_abs : ∀ d, |w d| ≤ 1 := by
    intro d
    by_cases hcond : d ∣ P ∧ d ≤ z
    · simp only [w, if_pos hcond]
      have hdP : d ∣ P := hcond.1
      have hdz : d ≤ z := hcond.2
      have hd_pos : 0 < d := Nat.pos_of_ne_zero (ne_zero_of_dvd_ne_zero hP0 hdP)
      have hnu_pos : 0 < s.nu d := s.nu_pos_of_dvd_prodPrimes hdP
      have hsum_nn : 0 ≤ ∑ l ∈ Dz.filter (fun l => d ∣ l), s.selbergTerms l :=
        Finset.sum_nonneg fun l hl => by
          simp only [Dz, D, mem_filter, Nat.mem_divisors] at hl
          exact (s.selbergTerms_pos hl.1.1.1).le
      have hmu_abs : |((μ d : ℤ) : ℝ)| ≤ 1 := by
        have := ArithmeticFunction.abs_moebius_le_one (n := d)
        exact_mod_cast this
      rw [abs_mul, abs_div, abs_of_pos (mul_pos hnu_pos hL_pos), abs_of_nonneg hsum_nn]
      -- Bound ∑_{l ≤ z, d ∣ l, l ∣ P} g(l) ≤ (s.nu d) * L
      set Q := P / d
      have hdQ : d * Q = P := Nat.mul_div_cancel' hdP
      have hQ0 : Q ≠ 0 := fun h => hP0 (by rw [← hdQ, h, mul_zero])
      have hcop : d.Coprime Q := (Nat.squarefree_mul_iff.mp (hdQ.symm ▸ hPsq)).1
      have hsum_eq : ∑ l ∈ Dz.filter (fun l => d ∣ l), s.selbergTerms l =
          s.selbergTerms d * ∑ m ∈ Q.divisors.filter (· ≤ z / d), s.selbergTerms m := by
        rw [Finset.mul_sum]
        refine Finset.sum_bij (fun l _ => l / d) ?_ ?_ ?_ ?_
        · intro l hl
          simp only [Dz, D, mem_filter, Nat.mem_divisors] at hl ⊢
          refine ⟨⟨?_, hQ0⟩, ?_⟩
          · have : d * (l / d) ∣ d * Q := by rw [Nat.mul_div_cancel' hl.2, hdQ]; exact hl.1.1.1
            exact (mul_dvd_mul_iff_left hd_pos.ne').mp this
          · exact Nat.div_le_div_right hl.1.2
        · intro l₁ hl₁ l₂ hl₂ heq
          simp only [mem_filter] at hl₁ hl₂
          rw [← Nat.mul_div_cancel' hl₁.2, ← Nat.mul_div_cancel' hl₂.2, heq]
        · intro m hm
          simp only [mem_filter, Nat.mem_divisors] at hm
          refine ⟨d * m, ?_, Nat.mul_div_cancel_left m hd_pos⟩
          simp only [Dz, D, mem_filter, Nat.mem_divisors]
          have hdmP : d * m ∣ P := by rw [← hdQ]; exact mul_dvd_mul_left d hm.1.1
          have hdmz : d * m ≤ z := (Nat.mul_le_mul_left d hm.2).trans (Nat.mul_div_le z d)
          exact ⟨⟨⟨hdmP, hP0⟩, hdmz⟩, dvd_mul_right d m⟩
        · intro l hl
          simp only [Dz, D, mem_filter, Nat.mem_divisors] at hl
          have hmQ : l / d ∣ Q := by
            have : d * (l / d) ∣ d * Q := by rw [Nat.mul_div_cancel' hl.2, hdQ]; exact hl.1.1.1
            exact (mul_dvd_mul_iff_left hd_pos.ne').mp this
          have hcop' : d.Coprime (l / d) := hcop.coprime_dvd_right hmQ
          conv_lhs => rw [← Nat.mul_div_cancel' hl.2]
          exact s.selbergTerms_isMultiplicative.map_mul_of_coprime hcop'
      have hprod_le_L : (s.selbergTerms d * (s.nu d)⁻¹) *
          (∑ m ∈ Q.divisors.filter (· ≤ z / d), s.selbergTerms m) ≤ L := by
        have hdiv_id : s.selbergTerms d * (s.nu d)⁻¹ = ∑ k ∈ d.divisors, s.selbergTerms k := by
          rw [← s.sum_divisors_selbergTerms_eq_selbergTerms_mul_nu_inv hdP]
          rw [← Finset.sum_filter, Nat.divisors_filter_dvd_of_dvd hP0 hdP]
        rw [hdiv_id, Finset.sum_mul]
        simp_rw [Finset.mul_sum]
        rw [← Finset.sum_product']
        set Sprod := d.divisors ×ˢ Q.divisors.filter (· ≤ z / d)
        have hinj : Set.InjOn (fun x : ℕ × ℕ => x.1 * x.2) Sprod := by
          intro x₁ hx₁ x₂ hx₂ heq
          dsimp only at heq
          have hx₁' := Finset.mem_coe.mp hx₁
          have hx₂' := Finset.mem_coe.mp hx₂
          simp only [Sprod, mem_product, mem_filter, Nat.mem_divisors] at hx₁' hx₂'
          have hcop12 : x₁.1.Coprime x₂.2 := (hcop.coprime_dvd_left hx₁'.1.1).coprime_dvd_right hx₂'.2.1.1
          have hcop21 : x₂.1.Coprime x₁.2 := (hcop.coprime_dvd_left hx₂'.1.1).coprime_dvd_right hx₁'.2.1.1
          have hd1 : x₁.1 ∣ x₂.1 := hcop12.dvd_of_dvd_mul_right (heq ▸ dvd_mul_right x₁.1 x₁.2)
          have hd2 : x₂.1 ∣ x₁.1 := hcop21.dvd_of_dvd_mul_right (heq.symm ▸ dvd_mul_right x₂.1 x₂.2)
          have hx1eq : x₁.1 = x₂.1 := Nat.dvd_antisymm hd1 hd2
          have hx1pos : 0 < x₁.1 := Nat.pos_of_ne_zero (ne_zero_of_dvd_ne_zero hd_pos.ne' hx₁'.1.1)
          have hx2eq : x₁.2 = x₂.2 := mul_left_cancel₀ hx1pos.ne' (by rw [← hx1eq] at heq; exact heq)
          exact Prod.ext hx1eq hx2eq
        have hterm : ∀ x ∈ Sprod, s.selbergTerms x.1 * s.selbergTerms x.2 =
            s.selbergTerms (x.1 * x.2) := by
          intro x hx
          simp only [Sprod, mem_product, mem_filter, Nat.mem_divisors] at hx
          have hcx : x.1.Coprime x.2 := (hcop.coprime_dvd_left hx.1.1).coprime_dvd_right hx.2.1.1
          exact (s.selbergTerms_isMultiplicative.map_mul_of_coprime hcx).symm
        have hmaps : Sprod.image (fun x : ℕ × ℕ => x.1 * x.2) ⊆ Dz := by
          intro n hn
          obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hn
          simp only [Sprod, mem_product, mem_filter, Nat.mem_divisors] at hx
          simp only [Dz, D, mem_filter, Nat.mem_divisors]
          have hmulP : x.1 * x.2 ∣ P := by rw [← hdQ]; exact mul_dvd_mul hx.1.1 hx.2.1.1
          have hx1_le : x.1 ≤ d := Nat.le_of_dvd hd_pos hx.1.1
          have hmulz : x.1 * x.2 ≤ z := (Nat.mul_le_mul hx1_le hx.2.2).trans (Nat.mul_div_le z d)
          exact ⟨⟨hmulP, hP0⟩, hmulz⟩
        calc ∑ x ∈ Sprod, s.selbergTerms x.1 * s.selbergTerms x.2
            = ∑ x ∈ Sprod, s.selbergTerms (x.1 * x.2) := Finset.sum_congr rfl hterm
          _ = ∑ n ∈ Sprod.image (fun x : ℕ × ℕ => x.1 * x.2), s.selbergTerms n :=
                (Finset.sum_image hinj).symm
          _ ≤ ∑ n ∈ Dz, s.selbergTerms n :=
                Finset.sum_le_sum_of_subset_of_nonneg hmaps fun n hn _ => by
                  simp only [Dz, D, mem_filter, Nat.mem_divisors] at hn
                  exact (s.selbergTerms_pos hn.1.1).le
      have hfinal : (∑ l ∈ Dz.filter (fun l => d ∣ l), s.selbergTerms l) / (s.nu d * L) ≤ 1 := by
        rw [hsum_eq, div_le_one (mul_pos hnu_pos hL_pos)]
        have hrew : s.selbergTerms d * ∑ m ∈ Q.divisors.filter (· ≤ z / d), s.selbergTerms m =
            s.nu d * ((s.selbergTerms d * (s.nu d)⁻¹) *
              ∑ m ∈ Q.divisors.filter (· ≤ z / d), s.selbergTerms m) := by
          field_simp [hnu_pos.ne']
        rw [hrew]
        exact mul_le_mul_of_nonneg_left hprod_le_L hnu_pos.le
      calc |((μ d : ℤ) : ℝ)| / (s.nu d * L) *
              ∑ l ∈ Dz.filter (fun l => d ∣ l), s.selbergTerms l
          ≤ 1 / (s.nu d * L) * ∑ l ∈ Dz.filter (fun l => d ∣ l), s.selbergTerms l := by
            gcongr
        _ = (∑ l ∈ Dz.filter (fun l => d ∣ l), s.selbergTerms l) / (s.nu d * L) := by ring
        _ ≤ 1 := hfinal
    · simp [w, if_neg hcond]
  -- Step 3: Bound errSum ≤ Crem * z^4
  have herr : s.errSum (BoundingSieve.lambdaSquared w) ≤ Crem * (z : ℝ) ^ 4 := by
    unfold BoundingSieve.errSum
    have hterm_le : ∀ d ∈ D,
        |BoundingSieve.lambdaSquared w d| * |s.rem d| ≤
        ∑ d1 ∈ Dz, ∑ d2 ∈ Dz, if d = Nat.lcm d1 d2 then Crem * (z : ℝ) ^ 2 else 0 := by
      intro d hd
      have hdP : d ∣ P := (Nat.mem_divisors.mp hd).1
      have hlam_abs : |BoundingSieve.lambdaSquared w d| ≤
          ∑ d1 ∈ d.divisors, ∑ d2 ∈ d.divisors,
            if d = Nat.lcm d1 d2 then |w d1| * |w d2| else 0 := by
        unfold BoundingSieve.lambdaSquared
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun d1 _ => ?_)
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun d2 _ => ?_)
        split_ifs
        · rw [abs_mul]
        · simp
      have hsub1 : ∀ d1 ∈ d.divisors, ∀ d2 ∈ d.divisors,
          (if d = Nat.lcm d1 d2 then |w d1| * |w d2| * |s.rem d| else 0) ≤
          (if d1 ≤ z ∧ d2 ≤ z ∧ d = Nat.lcm d1 d2 then Crem * (z : ℝ) ^ 2 else 0) := by
        intro d1 hd1 d2 hd2
        by_cases hle : d1 ≤ z ∧ d2 ≤ z
        · split_ifs with h1 h2
          · have hrem_d : |s.rem d| ≤ Crem * (d : ℝ) := hrem d hdP
            have hd_le_z2 : (d : ℝ) ≤ (z : ℝ) ^ 2 := by
              have hlcm_le : Nat.lcm d1 d2 ≤ d1 * d2 :=
                Nat.lcm_le_mul (Nat.pos_of_mem_divisors hd1) (Nat.pos_of_mem_divisors hd2)
              have hprod_le : d1 * d2 ≤ z * z := Nat.mul_le_mul hle.1 hle.2
              have : d ≤ z ^ 2 := by rw [sq]; exact (h1 ▸ hlcm_le).trans hprod_le
              exact_mod_cast this
            have hrem_z2 : |s.rem d| ≤ Crem * (z : ℝ) ^ 2 :=
              hrem_d.trans (mul_le_mul_of_nonneg_left hd_le_z2 hCrem)
            calc |w d1| * |w d2| * |s.rem d|
                ≤ 1 * 1 * (Crem * (z : ℝ) ^ 2) := by
                  gcongr
                  · exact hw_abs d1
                  · exact hw_abs d2
              _ = Crem * (z : ℝ) ^ 2 := by ring
          · exact (h2 ⟨hle.1, hle.2, h1⟩).elim
          · positivity
          · exact le_rfl
        · have hcond_false : ¬ (d1 ≤ z ∧ d2 ≤ z ∧ d = Nat.lcm d1 d2) := fun h => hle ⟨h.1, h.2.1⟩
          rw [if_neg hcond_false]
          split_ifs
          · have hzero : w d1 = 0 ∨ w d2 = 0 := by
              by_cases h1z : d1 ≤ z
              · right
                have h2z : ¬ d2 ≤ z := fun h => hle ⟨h1z, h⟩
                simp [w, if_neg (fun hc : d2 ∣ P ∧ d2 ≤ z => h2z hc.2)]
              · left
                simp [w, if_neg (fun hc : d1 ∣ P ∧ d1 ≤ z => h1z hc.2)]
            rcases hzero with h0 | h0 <;> simp [h0]
          · exact le_rfl
      calc |BoundingSieve.lambdaSquared w d| * |s.rem d|
          ≤ (∑ d1 ∈ d.divisors, ∑ d2 ∈ d.divisors,
              if d = Nat.lcm d1 d2 then |w d1| * |w d2| else 0) * |s.rem d| :=
            mul_le_mul_of_nonneg_right hlam_abs (abs_nonneg _)
        _ = ∑ d1 ∈ d.divisors, ∑ d2 ∈ d.divisors,
              if d = Nat.lcm d1 d2 then |w d1| * |w d2| * |s.rem d| else 0 := by
            simp_rw [Finset.sum_mul, ite_mul, zero_mul]
        _ ≤ ∑ d1 ∈ d.divisors, ∑ d2 ∈ d.divisors,
              if d1 ≤ z ∧ d2 ≤ z ∧ d = Nat.lcm d1 d2 then Crem * (z : ℝ) ^ 2 else 0 :=
            Finset.sum_le_sum fun d1 hd1 => Finset.sum_le_sum fun d2 hd2 => hsub1 d1 hd1 d2 hd2
        _ ≤ ∑ d1 ∈ D, ∑ d2 ∈ D,
              if d1 ≤ z ∧ d2 ≤ z ∧ d = Nat.lcm d1 d2 then Crem * (z : ℝ) ^ 2 else 0 := by
            have hd_sub : d.divisors ⊆ D := Nat.divisors_subset_of_dvd hP0 hdP
            refine Finset.sum_le_sum_of_subset_of_nonneg hd_sub (fun _ _ _ => Finset.sum_nonneg fun _ _ => by split_ifs <;> positivity) |>.trans ?_
            exact Finset.sum_le_sum fun d1 _ =>
              Finset.sum_le_sum_of_subset_of_nonneg hd_sub fun _ _ _ => by split_ifs <;> positivity
        _ = ∑ d1 ∈ Dz, ∑ d2 ∈ Dz, if d = Nat.lcm d1 d2 then Crem * (z : ℝ) ^ 2 else 0 := by
            simp only [Dz, Finset.sum_filter]
            refine Finset.sum_congr rfl fun d1 _ => ?_
            split_ifs with h1
            · refine Finset.sum_congr rfl fun d2 _ => by split_ifs <;> simp_all
            · simp [h1]
    have hDz_card : Dz.card ≤ z := by
      have hsub : Dz ⊆ Finset.Icc 1 z := by
        intro x hx
        simp only [Dz, D, mem_filter, Nat.mem_divisors, mem_Icc] at hx ⊢
        exact ⟨Nat.pos_of_ne_zero (ne_zero_of_dvd_ne_zero hP0 hx.1.1), hx.2⟩
      exact (Finset.card_le_card hsub).trans (by simp)
    calc ∑ d ∈ D, |BoundingSieve.lambdaSquared w d| * |s.rem d|
        ≤ ∑ d ∈ D, ∑ d1 ∈ Dz, ∑ d2 ∈ Dz, if d = Nat.lcm d1 d2 then Crem * (z : ℝ) ^ 2 else 0 :=
          Finset.sum_le_sum hterm_le
      _ = ∑ d1 ∈ Dz, ∑ d2 ∈ Dz, ∑ d ∈ D, if d = Nat.lcm d1 d2 then Crem * (z : ℝ) ^ 2 else 0 := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun d1 _ => Finset.sum_comm
      _ ≤ ∑ d1 ∈ Dz, ∑ d2 ∈ Dz, Crem * (z : ℝ) ^ 2 := by
          refine Finset.sum_le_sum fun d1 _ => Finset.sum_le_sum fun d2 _ => ?_
          rw [Finset.sum_ite_eq']
          split_ifs
          · exact le_rfl
          · positivity
      _ = (Dz.card : ℝ) * (Dz.card : ℝ) * (Crem * (z : ℝ) ^ 2) := by
          simp [Finset.sum_const, nsmul_eq_mul]; ring
      _ ≤ (z : ℝ) * (z : ℝ) * (Crem * (z : ℝ) ^ 2) := by
          have hcardR : (Dz.card : ℝ) ≤ (z : ℝ) := by exact_mod_cast hDz_card
          gcongr
      _ = Crem * (z : ℝ) ^ 4 := by ring
  rw [hmain] at hbase
  rw [div_eq_mul_inv]
  linarith

/- CRT root counting for s^2 + n^2 ≡ 0 (mod d) -/

private def sqSols (n d : ℕ) [NeZero d] : Finset (ZMod d) :=
  Finset.univ.filter fun r : ZMod d => r ^ 2 + (n : ZMod d) ^ 2 = 0

private lemma sqSols_card_congr {n a b : ℕ} [NeZero a] [NeZero b] (h : a = b) :
    (sqSols n a).card = (sqSols n b).card := by
  subst h; rfl

private lemma sqSols_card_mul (n a b : ℕ) [NeZero a] [NeZero b] (hab : a.Coprime b) :
    have : NeZero (a * b) := ⟨mul_ne_zero (NeZero.ne a) (NeZero.ne b)⟩
    (sqSols n (a * b)).card = (sqSols n a).card * (sqSols n b).card := by
  have : NeZero (a * b) := ⟨mul_ne_zero (NeZero.ne a) (NeZero.ne b)⟩
  let e := ZMod.chineseRemainder hab
  rw [← Finset.card_product]
  refine Finset.card_bij (fun r _ => e r) ?_ ?_ ?_
  · intro r hr
    simp only [sqSols, mem_filter, mem_univ, true_and, mem_product] at hr ⊢
    have hmap : e (r ^ 2 + (n : ZMod (a * b)) ^ 2) = 0 := by rw [hr, _root_.map_zero]
    rw [map_add, map_pow, map_pow, map_natCast] at hmap
    have h1 := congrArg Prod.fst hmap
    have h2 := congrArg Prod.snd hmap
    simpa using And.intro h1 h2
  · intro r₁ _ r₂ _ heq
    exact e.injective heq
  · intro x hx
    simp only [sqSols, mem_product, mem_filter, mem_univ, true_and] at hx
    refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
    simp only [sqSols, mem_filter, mem_univ, true_and]
    apply e.injective
    rw [map_add, map_pow, map_pow, map_natCast, _root_.map_zero, e.apply_symm_apply]
    ext
    · simpa using hx.1
    · simpa using hx.2

private lemma sqSols_card_two {n : ℕ} (hodd : n % 2 = 1) : (sqSols n 2).card = 1 := by
  have hn : (n : ZMod 2) = 1 := by
    rw [← Nat.mod_add_div n 2, hodd]
    push_cast
    have h2 : (2 : ZMod 2) = 0 := by decide
    rw [h2, zero_mul, add_zero]
  have heq : sqSols n 2 = {1} := by
    ext r
    simp only [sqSols, mem_filter, mem_univ, true_and, mem_singleton, hn]
    have hcases : r = 0 ∨ r = 1 := by
      fin_cases r
      · left; rfl
      · right; rfl
    rcases hcases with rfl | rfl
    · decide
    · decide
  rw [heq, Finset.card_singleton]

private lemma sqSols_card_prime_dvd {n p : ℕ} (hp : p.Prime) (hpn : p ∣ n) :
    haveI : NeZero p := ⟨hp.ne_zero⟩
    (sqSols n p).card = 1 := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : Fact p.Prime := ⟨hp⟩
  have hn0 : (n : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff n p).mpr hpn
  have heq : sqSols n p = {0} := by
    ext r
    simp only [sqSols, mem_filter, mem_univ, true_and, mem_singleton, hn0, zero_pow two_ne_zero,
      add_zero]
    exact ⟨eq_zero_of_pow_eq_zero, fun h => by simp [h]⟩
  rw [heq, Finset.card_singleton]

private lemma sqSols_card_prime_mod4_eq1 {n p : ℕ} (hp : p.Prime) (hp1 : p % 4 = 1)
    (hndvd : ¬ p ∣ n) :
    haveI : NeZero p := ⟨hp.ne_zero⟩
    (sqSols n p).card = 2 := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : Fact p.Prime := ⟨hp⟩
  have hn0 : (n : ZMod p) ≠ 0 := fun h => hndvd ((ZMod.natCast_eq_zero_iff n p).mp h)
  have hsq : IsSquare (-1 : ZMod p) := ZMod.exists_sq_eq_neg_one_iff.mpr (by omega)
  obtain ⟨j, hj⟩ := hsq
  have hj2 : j ^ 2 = -1 := by rw [sq, ← hj]
  have hj0 : j ≠ 0 := by
    intro h0
    rw [h0, zero_pow two_ne_zero] at hj2
    have : (1 : ZMod p) = 0 := by
      have := congrArg Neg.neg hj2
      simpa using this.symm
    exact one_ne_zero this
  have h2ne0 : (2 : ZMod p) ≠ 0 := by
    intro h2
    have hdvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp h2
    have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
    have := hp.two_le
    omega
  have hdistinct : j * (n : ZMod p) ≠ -(j * (n : ZMod p)) := by
    intro heq
    have hsum : (2 : ZMod p) * (j * (n : ZMod p)) = 0 := by
      calc (2 : ZMod p) * (j * (n : ZMod p))
          = j * (n : ZMod p) + j * (n : ZMod p) := by ring
        _ = -(j * (n : ZMod p)) + j * (n : ZMod p) := by nth_rw 1 [heq]
        _ = 0 := neg_add_cancel _
    rcases mul_eq_zero.mp hsum with h2 | hjn
    · exact h2ne0 h2
    · rcases mul_eq_zero.mp hjn with h | h
      · exact hj0 h
      · exact hn0 h
  have heq : sqSols n p = {j * (n : ZMod p), -(j * (n : ZMod p))} := by
    ext r
    simp only [sqSols, mem_filter, mem_univ, true_and, mem_insert, mem_singleton]
    have hfac : r ^ 2 + (n : ZMod p) ^ 2 = (r - j * (n : ZMod p)) * (r + j * (n : ZMod p)) := by
      symm
      calc (r - j * (n : ZMod p)) * (r + j * (n : ZMod p))
          = r ^ 2 - j ^ 2 * (n : ZMod p) ^ 2 := by ring
        _ = r ^ 2 - (-1) * (n : ZMod p) ^ 2 := by rw [hj2]
        _ = r ^ 2 + (n : ZMod p) ^ 2 := by ring
    rw [hfac, mul_eq_zero, sub_eq_zero, add_eq_zero_iff_eq_neg]
  rw [heq, Finset.card_pair hdistinct]

private lemma sqSols_card_eq_prod_omega1 {n d : ℕ} [hd_nz : NeZero d] (hodd : n % 2 = 1)
    (hd_sq : Squarefree d)
    (hd_pf : ∀ p ∈ d.primeFactors, (p = 2) ∨ (p % 4 = 1 ∧ ¬ p ∣ n) ∨ (p % 4 = 3 ∧ p ∣ n)) :
    ((sqSols n d).card : ℝ) = ∏ p ∈ d.primeFactors, omega1 p := by
  revert hd_nz hd_sq hd_pf
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro hd_nz hd_sq hd_pf
    by_cases hd1 : d = 1
    · subst hd1
      have h1 : (sqSols n 1).card = 1 := by
        have : sqSols n 1 = {0} := by
          ext r
          simp only [sqSols, mem_filter, mem_univ, true_and, mem_singleton]
          exact ⟨fun _ => Subsingleton.elim r 0, fun _ => Subsingleton.elim _ 0⟩
        rw [this, Finset.card_singleton]
      simp [h1]
    · have hd_gt1 : 1 < d := by have := hd_sq.ne_zero; omega
      obtain ⟨p, hp_mem⟩ := Nat.nonempty_primeFactors.mpr hd_gt1
      have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp_mem
      have hpd : p ∣ d := Nat.dvd_of_mem_primeFactors hp_mem
      set d' := d / p
      have hpd' : p * d' = d := Nat.mul_div_cancel' hpd
      have hd'_sq : Squarefree d' := hd_sq.squarefree_of_dvd ⟨p, by rw [← hpd', mul_comm]⟩
      have hcop : p.Coprime d' := (Nat.squarefree_mul_iff.mp (hpd'.symm ▸ hd_sq)).1
      have hd'_lt : d' < d := by
        have h1 : 0 < d' := Nat.pos_of_ne_zero hd'_sq.ne_zero
        have h2 := hpp.two_le
        nlinarith
      have hd'_pf : ∀ q ∈ d'.primeFactors, (q = 2) ∨ (q % 4 = 1 ∧ ¬ q ∣ n) ∨ (q % 4 = 3 ∧ q ∣ n) := by
        intro q hq
        apply hd_pf q
        rw [Nat.mem_primeFactors] at hq ⊢
        exact ⟨hq.1, dvd_trans hq.2.1 ⟨p, by rw [← hpd', mul_comm]⟩, hd_sq.ne_zero⟩
      have : NeZero p := ⟨hpp.ne_zero⟩
      have : NeZero d' := ⟨hd'_sq.ne_zero⟩
      have : NeZero (p * d') := ⟨mul_ne_zero hpp.ne_zero hd'_sq.ne_zero⟩
      have hmul : (sqSols n d).card = (sqSols n p).card * (sqSols n d').card := by
        rw [← sqSols_card_congr hpd']
        exact sqSols_card_mul n p d' hcop
      have hp_card : ((sqSols n p).card : ℝ) = omega1 p := by
        rcases hd_pf p hp_mem with rfl | ⟨hp1, hndvd⟩ | ⟨hp3, hdvd⟩
        · rw [sqSols_card_two hodd]; simp [omega1]
        · rw [sqSols_card_prime_mod4_eq1 hpp hp1 hndvd]; simp [omega1, hp1]
        · rw [sqSols_card_prime_dvd hpp hdvd]
          have hne1 : p % 4 ≠ 1 := by omega
          simp [omega1, hne1]
      have hpf_eq : d.primeFactors = insert p d'.primeFactors := by
        rw [← hpd', Nat.primeFactors_mul hpp.ne_zero hd'_sq.ne_zero, hpp.primeFactors]
        simp
      have hp_not_mem : p ∉ d'.primeFactors := by
        intro hmem
        have := Nat.dvd_of_mem_primeFactors hmem
        exact hpp.not_isUnit (Nat.isUnit_iff.mpr (Nat.dvd_one.mp (hcop.symm ▸ Nat.dvd_gcd this dvd_rfl)))
      have hih := ih d' hd'_lt hd'_sq hd'_pf
      rw [hmul, Nat.cast_mul, hp_card, hih, hpf_eq, Finset.prod_insert hp_not_mem]

private lemma count_Ico_rem_bound (n d : ℕ) [NeZero d] (hn : 1 ≤ n) :
    let ω : ℕ := (sqSols n d).card
    |(((Finset.Ico 1 n).filter (fun s => d ∣ n ^ 2 + s ^ 2)).card : ℝ) -
      (ω : ℝ) / (d : ℝ) * (n : ℝ)| ≤ 2 * (d : ℝ) := by
  intro ω
  have hd_pos : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  have hω_le_d : ω ≤ d := by
    calc ω = (sqSols n d).card := rfl
      _ ≤ (Finset.univ : Finset (ZMod d)).card := Finset.card_le_card (Finset.filter_subset _ _)
      _ = d := by rw [Finset.card_univ, ZMod.card]
  -- Count over Finset.range n by splitting into q full blocks of length d plus tail
  set q := n / d
  set r := n % d
  have hdiv : q * d + r = n := by rw [mul_comm]; exact Nat.div_add_mod n d
  have hr_lt : r < d := Nat.mod_lt n hd_pos
  have hblock : ∀ j : ℕ,
      ((Finset.Ico (j * d) ((j + 1) * d)).filter (fun s => d ∣ n ^ 2 + s ^ 2)).card = ω := by
    intro j
    refine Finset.card_bij (fun s _ => (s : ZMod d)) ?_ ?_ ?_
    · intro s hs
      simp only [mem_filter, mem_Ico, sqSols, mem_univ, true_and] at hs ⊢
      have h0 := (ZMod.natCast_eq_zero_iff (n ^ 2 + s ^ 2) d).mpr hs.2
      simp only [Nat.cast_add, Nat.cast_pow] at h0
      rwa [add_comm]
    · intro s₁ hs₁ s₂ hs₂ heq
      simp only [mem_filter, mem_Ico] at hs₁ hs₂
      have hmod : s₁ % d = s₂ % d := by
        have := congrArg ZMod.val heq
        simpa [ZMod.val_natCast] using this
      have hs1_eq : s₁ = j * d + (s₁ - j * d) := by omega
      have hs2_eq : s₂ = j * d + (s₂ - j * d) := by omega
      have h1lt : s₁ - j * d < d := by nlinarith
      have h2lt : s₂ - j * d < d := by nlinarith
      have hm1 : s₁ % d = s₁ - j * d := by
        conv_lhs => rw [hs1_eq]
        rw [Nat.mul_add_mod', Nat.mod_eq_of_lt h1lt]
      have hm2 : s₂ % d = s₂ - j * d := by
        conv_lhs => rw [hs2_eq]
        rw [Nat.mul_add_mod', Nat.mod_eq_of_lt h2lt]
      omega
    · intro x hx
      simp only [sqSols, mem_filter, mem_univ, true_and] at hx
      refine ⟨j * d + x.val, ?_, ?_⟩
      · simp only [mem_filter, mem_Ico]
        have hxlt : x.val < d := x.val_lt
        refine ⟨⟨by omega, by nlinarith⟩, ?_⟩
        rw [← ZMod.natCast_eq_zero_iff]
        have hcast : ((j * d + x.val : ℕ) : ZMod d) = x := by
          simp [ZMod.natCast_zmod_val]
        simp only [Nat.cast_add, Nat.cast_pow, hcast]
        rwa [add_comm]
      · simp [ZMod.natCast_zmod_val]
  have htail : ((Finset.Ico (q * d) n).filter (fun s => d ∣ n ^ 2 + s ^ 2)).card ≤ ω := by
    refine Finset.card_le_card_of_injOn (fun s => (s : ZMod d)) ?_ ?_
    · intro s hs
      have hs' := Finset.mem_coe.mp hs
      rw [Finset.mem_coe]
      simp only [mem_filter, mem_Ico, sqSols, mem_univ, true_and] at hs' ⊢
      have h0 := (ZMod.natCast_eq_zero_iff (n ^ 2 + s ^ 2) d).mpr hs'.2
      simp only [Nat.cast_add, Nat.cast_pow] at h0
      rwa [add_comm]
    · intro s₁ hs₁ s₂ hs₂ heq
      have hs₁' := Finset.mem_coe.mp hs₁
      have hs₂' := Finset.mem_coe.mp hs₂
      simp only [mem_filter, mem_Ico] at hs₁' hs₂'
      have hmod : s₁ % d = s₂ % d := by
        have := congrArg ZMod.val heq
        simpa [ZMod.val_natCast] using this
      have h1lt : s₁ - q * d < d := by omega
      have h2lt : s₂ - q * d < d := by omega
      have hm1 : s₁ % d = s₁ - q * d := by
        have hs1_eq : s₁ = q * d + (s₁ - q * d) := by omega
        conv_lhs => rw [hs1_eq]
        rw [Nat.mul_add_mod', Nat.mod_eq_of_lt h1lt]
      have hm2 : s₂ % d = s₂ - q * d := by
        have hs2_eq : s₂ = q * d + (s₂ - q * d) := by omega
        conv_lhs => rw [hs2_eq]
        rw [Nat.mul_add_mod', Nat.mod_eq_of_lt h2lt]
      omega
  have hpart : (Finset.range n).filter (fun s => d ∣ n ^ 2 + s ^ 2) =
      ((Finset.range q).biUnion (fun j => (Finset.Ico (j * d) ((j + 1) * d)).filter (fun s => d ∣ n ^ 2 + s ^ 2))) ∪
      (Finset.Ico (q * d) n).filter (fun s => d ∣ n ^ 2 + s ^ 2) := by
    ext s
    simp only [mem_union, mem_biUnion, mem_range, mem_filter, mem_Ico]
    constructor
    · rintro ⟨hsn, hdvd⟩
      by_cases hsq : s < q * d
      · left
        refine ⟨s / d, ?_, ⟨?_, ?_⟩, hdvd⟩
        · exact (Nat.div_lt_iff_lt_mul hd_pos).mpr hsq
        · rw [mul_comm]; exact Nat.mul_div_le s d
        · have : s < d * (s / d) + d := by
            have hmod := Nat.mod_lt s hd_pos
            have hdm := Nat.div_add_mod s d
            omega
          nlinarith
      · right
        exact ⟨⟨by omega, hsn⟩, hdvd⟩
    · rintro (⟨j, hj, ⟨_, hs2⟩, hdvd⟩ | ⟨⟨_, hsn⟩, hdvd⟩)
      · have hle : (j + 1) * d ≤ q * d := Nat.mul_le_mul_right d hj
        exact ⟨by omega, hdvd⟩
      · exact ⟨hsn, hdvd⟩
  have hdisj_blocks : Set.PairwiseDisjoint (Finset.range q : Set ℕ)
      (fun j => (Finset.Ico (j * d) ((j + 1) * d)).filter (fun s => d ∣ n ^ 2 + s ^ 2)) := by
    intro j₁ _ j₂ _ hne
    simp only [Function.onFun, Finset.disjoint_left, mem_filter, mem_Ico]
    intro s hs₁ hs₂
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have : (j₁ + 1) * d ≤ j₂ * d := Nat.mul_le_mul_right d hlt
      omega
    · have : (j₂ + 1) * d ≤ j₁ * d := Nat.mul_le_mul_right d hgt
      omega
  have hdisj_tail : Disjoint
      ((Finset.range q).biUnion (fun j => (Finset.Ico (j * d) ((j + 1) * d)).filter (fun s => d ∣ n ^ 2 + s ^ 2)))
      ((Finset.Ico (q * d) n).filter (fun s => d ∣ n ^ 2 + s ^ 2)) := by
    rw [Finset.disjoint_left]
    intro s hs1 hs2
    simp only [mem_biUnion, mem_range, mem_filter, mem_Ico] at hs1 hs2
    obtain ⟨j, hj, ⟨_, hsj⟩, _⟩ := hs1
    have : (j + 1) * d ≤ q * d := Nat.mul_le_mul_right d hj
    omega
  have hrange_card :
      ((Finset.range n).filter (fun s => d ∣ n ^ 2 + s ^ 2)).card =
      q * ω + ((Finset.Ico (q * d) n).filter (fun s => d ∣ n ^ 2 + s ^ 2)).card := by
    rw [hpart, Finset.card_union_of_disjoint hdisj_tail, Finset.card_biUnion hdisj_blocks]
    congr 1
    simp [hblock, Finset.sum_const, smul_eq_mul]
  -- Compare Ico 1 n with range n (differ by at most 1 at s = 0)
  have hIco_sub : (Finset.Ico 1 n).filter (fun s => d ∣ n ^ 2 + s ^ 2) ⊆
      (Finset.range n).filter (fun s => d ∣ n ^ 2 + s ^ 2) := by
    intro s hs
    simp only [mem_filter, mem_Ico, mem_range] at hs ⊢
    exact ⟨hs.1.2, hs.2⟩
  have hrange_sub : (Finset.range n).filter (fun s => d ∣ n ^ 2 + s ^ 2) ⊆
      insert 0 ((Finset.Ico 1 n).filter (fun s => d ∣ n ^ 2 + s ^ 2)) := by
    intro s hs
    simp only [mem_filter, mem_range, mem_insert, mem_Ico] at hs ⊢
    by_cases hs0 : s = 0
    · left; exact hs0
    · right; exact ⟨⟨by omega, hs.1⟩, hs.2⟩
  set C := ((Finset.Ico 1 n).filter (fun s => d ∣ n ^ 2 + s ^ 2)).card
  have hC_le : C ≤ q * ω + ω := by
    have h1 : C ≤ ((Finset.range n).filter (fun s => d ∣ n ^ 2 + s ^ 2)).card :=
      Finset.card_le_card hIco_sub
    omega
  have hC_ge : q * ω ≤ C + 1 := by
    have h1 : ((Finset.range n).filter (fun s => d ∣ n ^ 2 + s ^ 2)).card ≤ C + 1 :=
      (Finset.card_le_card hrange_sub).trans (Finset.card_insert_le _ _)
    omega
  have hmain_eq : (ω : ℝ) / (d : ℝ) * (n : ℝ) = (q : ℝ) * (ω : ℝ) + (r : ℝ) / (d : ℝ) * (ω : ℝ) := by
    have hn_cast : (n : ℝ) = (q : ℝ) * (d : ℝ) + (r : ℝ) := by exact_mod_cast hdiv.symm
    have hd_ne : (d : ℝ) ≠ 0 := by exact_mod_cast hd_pos.ne'
    rw [hn_cast]
    field_simp [hd_ne]
  have hrem_nn : 0 ≤ (r : ℝ) / (d : ℝ) * (ω : ℝ) := by positivity
  have hrem_le : (r : ℝ) / (d : ℝ) * (ω : ℝ) ≤ (ω : ℝ) := by
    have hr_le : (r : ℝ) / (d : ℝ) ≤ 1 := by
      rw [div_le_one (by exact_mod_cast hd_pos)]
      exact_mod_cast hr_lt.le
    calc (r : ℝ) / (d : ℝ) * (ω : ℝ) ≤ 1 * (ω : ℝ) := by gcongr
      _ = (ω : ℝ) := one_mul _
  have hC_leR : (C : ℝ) ≤ (q : ℝ) * (ω : ℝ) + (ω : ℝ) := by exact_mod_cast hC_le
  have hC_geR : (q : ℝ) * (ω : ℝ) ≤ (C : ℝ) + 1 := by exact_mod_cast hC_ge
  have hω_leR : (ω : ℝ) ≤ (d : ℝ) := by exact_mod_cast hω_le_d
  have hd_ge1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd_pos
  rw [hmain_eq, abs_le]
  constructor <;> linarith

/- Putting everything together for a chosen finite set S of primes ≡ 3 (mod 4) -/

theorem finite_inert_sieve_counterexample (S : Finset ℕ)
    (hS_primes : ∀ p ∈ S, p.Prime ∧ p % 4 = 3)
    (hM3_ge : 200000 ≤ ∏ p ∈ S, p)
    (hS_prod_gt : (10000 : ℝ) < ∏ p ∈ S, ((p : ℝ) / ((p : ℝ) - 1))) :
    5 * OeisA69004.a ((∏ p ∈ S, p)^10) < Nat.primeCounting ((∏ p ∈ S, p)^10) := by
  set M3 : ℕ := ∏ p ∈ S, p
  have hM3_pos : 0 < M3 := by omega
  have hM3_ge100 : 100 ≤ M3 := by omega
  have hM3_odd : M3 % 2 = 1 := by
    have hprod_odd : Odd M3 := by
      refine Finset.prod_induction _ Odd (fun _ _ ha hb => ha.mul hb) odd_one fun p hp => ?_
      have hp3 := (hS_primes p hp).2
      exact Nat.odd_iff.mpr (by omega)
    exact Nat.odd_iff.mp hprod_odd
  set n : ℕ := M3 ^ 10
  set z : ℕ := M3 ^ 2
  have hn_gt1 : 1 < n := by
    have : 2 ≤ M3 := by omega
    calc 1 < 2 ^ 10 := by norm_num
      _ ≤ M3 ^ 10 := Nat.pow_le_pow_left this 10
  have hn_odd : n % 2 = 1 := by
    have : Odd n := Odd.pow (Nat.odd_iff.mpr hM3_odd)
    exact Nat.odd_iff.mp this
  have hz_ge1 : 1 ≤ z := Nat.one_le_pow 2 M3 hM3_pos
  have hM3_le_z : M3 ≤ z := by
    change M3 ≤ M3 ^ 2
    nlinarith
  have hM3_pf : ∀ p ∈ M3.primeFactors, p ∈ S := by
    intro p hp
    rw [Nat.mem_primeFactors] at hp
    obtain ⟨q, hqS, hpq⟩ := hp.1.prime.exists_mem_finset_dvd hp.2.1
    have heq := (Nat.prime_dvd_prime_iff_eq hp.1 (hS_primes q hqS).1).mp hpq
    rwa [heq]
  have hn_pf : ∀ p, p.Prime → (p ∣ n ↔ p ∈ S) := by
    intro p hpp
    constructor
    · intro hpn
      have hpM3 : p ∣ M3 := hpp.dvd_of_dvd_pow hpn
      exact hM3_pf p (Nat.mem_primeFactors.mpr ⟨hpp, hpM3, hM3_pos.ne'⟩)
    · intro hpS
      exact dvd_trans (Finset.dvd_prod_of_mem _ hpS) (dvd_pow_self M3 (by norm_num))
  -- Build the BoundingSieve
  set Pset : Finset ℕ := (Finset.Icc 2 z).filter fun p => p.Prime ∧ (p ∈ S ∨ p % 4 ≠ 3)
  set P : ℕ := ∏ p ∈ Pset, p
  have hP_pos : 0 < P := Finset.prod_pos fun p hp => (Finset.mem_filter.mp hp).2.1.pos
  have hP_sq : Squarefree P := by
    rw [Nat.squarefree_iff_prime_squarefree]
    intro p hpp hp2
    have hp_in : p ∈ Pset := by
      have hpd : p ∣ P := dvd_trans (dvd_mul_right p p) hp2
      obtain ⟨r, hr, hpr⟩ := hpp.prime.exists_mem_finset_dvd hpd
      have hrr : r.Prime := (Finset.mem_filter.mp hr).2.1
      have heq := (Nat.prime_dvd_prime_iff_eq hpp hrr).mp hpr
      rwa [heq]
    have hp2' : p * p ∣ ∏ r ∈ Pset, r := hp2
    rw [← Finset.mul_prod_erase _ _ hp_in] at hp2'
    have hprest : p ∣ ∏ r ∈ Pset.erase p, r := (mul_dvd_mul_iff_left hpp.ne_zero).mp hp2'
    obtain ⟨r, hr, hpr⟩ := hpp.prime.exists_mem_finset_dvd hprest
    have hrm := Finset.mem_erase.mp hr
    exact hrm.1 ((Nat.prime_dvd_prime_iff_eq hpp (Finset.mem_filter.mp hrm.2).2.1).mp hpr).symm
  have hP_pf : ∀ p, p.Prime → (p ∣ P ↔ p ∈ Pset) := by
    intro p hpp
    constructor
    · intro hpd
      obtain ⟨r, hr, hpr⟩ := hpp.prime.exists_mem_finset_dvd hpd
      have heq := (Nat.prime_dvd_prime_iff_eq hpp (Finset.mem_filter.mp hr).2.1).mp hpr
      rwa [heq]
    · intro hpP
      exact Finset.dvd_prod_of_mem _ hpP
  let nuFn : ArithmeticFunction ℝ := ArithmeticFunction.prodPrimeFactors fun p => omega1 p / (p : ℝ)
  have hnu_mult : nuFn.IsMultiplicative := ArithmeticFunction.IsMultiplicative.prodPrimeFactors _
  have hnu_prime : ∀ p : ℕ, p.Prime → nuFn p = omega1 p / (p : ℝ) := by
    intro p hpp
    simp only [nuFn, ArithmeticFunction.prodPrimeFactors_apply hpp.ne_zero, hpp.primeFactors,
      Finset.prod_singleton]
  let sv : BoundingSieve := {
    support := (Finset.Ico 1 n).image (fun x => n ^ 2 + x ^ 2)
    prodPrimes := P
    prodPrimes_squarefree := hP_sq
    weights := fun _ => 1
    weights_nonneg := fun _ => zero_le_one
    totalMass := (n : ℝ)
    nu := nuFn
    nu_mult := hnu_mult
    nu_pos_of_prime := fun p hpp _ => by
      rw [hnu_prime p hpp]
      have hp_pos : (0 : ℝ) < p := by exact_mod_cast hpp.pos
      unfold omega1; split_ifs <;> positivity
    nu_lt_one_of_prime := fun p hpp _ => by
      rw [hnu_prime p hpp]
      have hp_pos : (0 : ℝ) < p := by exact_mod_cast hpp.pos
      unfold omega1
      split_ifs with hp1
      · have hp5 : (5 : ℝ) ≤ p := by exact_mod_cast (by have := hpp.two_le; omega : 5 ≤ p)
        rw [div_lt_one hp_pos]; linarith
      · have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hpp.two_le
        rw [div_lt_one hp_pos]; linarith
  }
  -- Injectivity of x ↦ n^2 + x^2 on ℕ
  have hinj_sq : Set.InjOn (fun x : ℕ => n ^ 2 + x ^ 2) (Finset.Ico 1 n) := by
    intro x₁ _ x₂ _ heq
    dsimp only at heq
    have hsq : x₁ ^ 2 = x₂ ^ 2 := by omega
    nlinarith
  -- Step A: OeisA69004.a n ≤ sv.siftedSum
  have ha_le_sifted : (OeisA69004.a n : ℝ) ≤ sv.siftedSum := by
    unfold OeisA69004.a BoundingSieve.siftedSum
    simp only [sv]
    rw [Finset.sum_image hinj_sq, Nat.cast_sum]
    refine Finset.sum_le_sum fun x hx => ?_
    simp only [mem_Ico] at hx
    split_ifs with hpr hcop
    · simp
    · exfalso
      apply hcop
      rw [Nat.coprime_comm, hpr.coprime_iff_not_dvd]
      intro hdiv
      have hle_z : ∀ q ∈ Pset, q ≤ z := fun q hq => (Finset.mem_Icc.mp (Finset.mem_filter.mp hq).1).2
      have hlt_q : ∀ q ∈ Pset, q < n ^ 2 + x ^ 2 := fun q hq => by
        have hqz : q ≤ z := hle_z q hq
        have hz_lt_n : z < n := by
          have : M3 ^ 2 < M3 ^ 10 := Nat.pow_lt_pow_right (by omega) (by norm_num)
          exact this
        have hn_le : n ≤ n ^ 2 := by nlinarith
        omega
      have hq_mem : n ^ 2 + x ^ 2 ∈ Pset := (hP_pf (n ^ 2 + x ^ 2) hpr).mp hdiv
      exact (hlt_q _ hq_mem).ne rfl
    · norm_num
    · norm_num
  -- Step B: |sv.rem d| ≤ 2 * d for all d ∣ P
  have hrem_bound : ∀ d, d ∣ sv.prodPrimes → |sv.rem d| ≤ 2 * (d : ℝ) := by
    intro d hdP
    have hd_sq : Squarefree d := hP_sq.squarefree_of_dvd hdP
    haveI : NeZero d := ⟨hd_sq.ne_zero⟩
    have hd_pf : ∀ p ∈ d.primeFactors, (p = 2) ∨ (p % 4 = 1 ∧ ¬ p ∣ n) ∨ (p % 4 = 3 ∧ p ∣ n) := by
      intro p hp
      have hpp := Nat.prime_of_mem_primeFactors hp
      have hpP : p ∈ Pset := (hP_pf p hpp).mp (dvd_trans (Nat.dvd_of_mem_primeFactors hp) hdP)
      have hcond := (Finset.mem_filter.mp hpP).2.2
      by_cases hp2 : p = 2
      · left; exact hp2
      · rcases hpp.eq_two_or_odd with rfl | hodd
        · exact (hp2 rfl).elim
        · by_cases hp1 : p % 4 = 1
          · right; left
            refine ⟨hp1, fun hpn => ?_⟩
            have hpS : p ∈ S := (hn_pf p hpp).mp hpn
            have := (hS_primes p hpS).2
            omega
          · right; right
            have hp3 : p % 4 = 3 := by omega
            have hpS : p ∈ S := hcond.resolve_right (fun h => h hp3)
            exact ⟨hp3, (hn_pf p hpp).mpr hpS⟩
    have hnu_eq : sv.nu d = ((sqSols n d).card : ℝ) / (d : ℝ) := by
      change nuFn d = ((sqSols n d).card : ℝ) / (d : ℝ)
      rw [sqSols_card_eq_prod_omega1 hn_odd hd_sq hd_pf]
      simp only [nuFn, ArithmeticFunction.prodPrimeFactors_apply hd_sq.ne_zero]
      rw [Finset.prod_div_distrib, ← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hd_sq]
    have hmult_eq : sv.multSum d =
        (((Finset.Ico 1 n).filter (fun s => d ∣ n ^ 2 + s ^ 2)).card : ℝ) := by
      simp only [BoundingSieve.multSum, sv]
      rw [Finset.sum_image hinj_sq, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
    simp only [BoundingSieve.rem, sv]
    change |sv.multSum d - sv.nu d * (n : ℝ)| ≤ 2 * (d : ℝ)
    rw [hmult_eq, hnu_eq]
    exact count_Ico_rem_bound n d (by omega)
  -- Step C: Apply selberg_sieve_upper_bound
  have hsieve := selberg_sieve_upper_bound sv z hz_ge1 2 (by norm_num) hrem_bound
  -- Step D: Lower bound L = ∑ l ∈ P.divisors.filter (· ≤ z), sv.selbergTerms l
  set L := ∑ l ∈ P.divisors.filter (· ≤ z), sv.selbergTerms l
  have hselb_eq : ∀ l : ℕ, l ∣ P →
      sv.selbergTerms l = ∏ p ∈ l.primeFactors, (omega1 p / ((p : ℝ) - omega1 p)) := by
    intro l hlP
    have hl_sq : Squarefree l := hP_sq.squarefree_of_dvd hlP
    rw [sv.selbergTerms_apply]
    change nuFn l * ∏ p ∈ l.primeFactors, (1 - nuFn p)⁻¹ = _
    simp only [nuFn, ArithmeticFunction.prodPrimeFactors_apply hl_sq.ne_zero]
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun p hp => ?_
    have hpp := Nat.prime_of_mem_primeFactors hp
    rw [ArithmeticFunction.prodPrimeFactors_apply hpp.ne_zero, hpp.primeFactors, Finset.prod_singleton]
    have hp_pos : (0 : ℝ) < p := by exact_mod_cast hpp.pos
    have hp_gt : omega1 p < (p : ℝ) := by
      unfold omega1
      split_ifs with hp1
      · exact_mod_cast (by have := hpp.two_le; omega : 2 < p)
      · exact_mod_cast hpp.one_lt
    have hsub : (p : ℝ) - omega1 p ≠ 0 := by linarith
    field_simp [hp_pos.ne', hsub]
  have hL_lb : (∏ p ∈ S, ((p : ℝ) / ((p : ℝ) - 1))) * (∑ q ∈ goodSqfree M3, g2 q) ≤ L := by
    -- Inject M3.divisors × goodSqfree M3 into P.divisors.filter (· ≤ z) via (q1, q2) ↦ q1 * q2
    have hM3_dvd_P : M3 ∣ P := by
      have hS_sub : S ⊆ Pset := by
        intro p hp
        have hpp := (hS_primes p hp).1
        have hp_le_M3 : p ≤ M3 := Nat.le_of_dvd hM3_pos (Finset.dvd_prod_of_mem _ hp)
        simp only [Pset, mem_filter, mem_Icc]
        exact ⟨⟨hpp.two_le, hp_le_M3.trans hM3_le_z⟩, hpp, Or.inl hp⟩
      exact Finset.prod_dvd_prod_of_subset S Pset id hS_sub
    have hM3_sq : Squarefree M3 := hP_sq.squarefree_of_dvd hM3_dvd_P
    have hM3_sum : ∑ q1 ∈ M3.divisors, ∏ p ∈ q1.primeFactors, ((1 : ℝ) / ((p : ℝ) - 1)) =
        ∏ p ∈ S, ((p : ℝ) / ((p : ℝ) - 1)) := by
      have hM3_pf_eq : M3.primeFactors = S := by
        ext p
        constructor
        · exact hM3_pf p
        · intro hp
          exact Nat.mem_primeFactors.mpr ⟨(hS_primes p hp).1, Finset.dvd_prod_of_mem _ hp, hM3_pos.ne'⟩
      have hbij : ∑ q1 ∈ M3.divisors, ∏ p ∈ q1.primeFactors, ((1 : ℝ) / ((p : ℝ) - 1)) =
          ∑ T ∈ S.powerset, ∏ p ∈ T, ((1 : ℝ) / ((p : ℝ) - 1)) := by
        refine Finset.sum_bij (fun q1 _ => q1.primeFactors) ?_ ?_ ?_ ?_
        · intro q1 hq1
          rw [Finset.mem_powerset, ← hM3_pf_eq]
          intro p hp
          rw [Nat.mem_primeFactors] at hp ⊢
          exact ⟨hp.1, dvd_trans hp.2.1 (Nat.dvd_of_mem_divisors hq1), hM3_pos.ne'⟩
        · intro a ha b hb heq
          have ha_sq := hM3_sq.squarefree_of_dvd (Nat.dvd_of_mem_divisors ha)
          have hb_sq := hM3_sq.squarefree_of_dvd (Nat.dvd_of_mem_divisors hb)
          rw [← Nat.prod_primeFactors_of_squarefree ha_sq, ← Nat.prod_primeFactors_of_squarefree hb_sq, heq]
        · intro T hT
          rw [Finset.mem_powerset] at hT
          refine ⟨∏ p ∈ T, p, ?_, ?_⟩
          · rw [Nat.mem_divisors]
            exact ⟨Finset.prod_dvd_prod_of_subset T S id hT, hM3_pos.ne'⟩
          · ext p
            rw [Nat.mem_primeFactors]
            constructor
            · rintro ⟨hpp, hpT, _⟩
              obtain ⟨r, hr, hpr⟩ := hpp.prime.exists_mem_finset_dvd hpT
              have heq := (Nat.prime_dvd_prime_iff_eq hpp (hS_primes r (hT hr)).1).mp hpr
              rwa [heq]
            · intro hpT
              have hTpos : 0 < ∏ r ∈ T, r := Finset.prod_pos fun r hr => (hS_primes r (hT hr)).1.pos
              exact ⟨(hS_primes p (hT hpT)).1, Finset.dvd_prod_of_mem _ hpT, hTpos.ne'⟩
        · intro _ _; rfl
      rw [hbij, ← Finset.prod_one_add]
      refine Finset.prod_congr rfl fun p hp => ?_
      have hp3 : (3 : ℝ) ≤ p := by exact_mod_cast (by have := (hS_primes p hp).1.two_le; have := (hS_primes p hp).2; omega : 3 ≤ p)
      field_simp [show (p : ℝ) - 1 ≠ 0 by linarith]
      ring
    rw [← hM3_sum, Finset.sum_mul]
    simp_rw [Finset.mul_sum]
    rw [← Finset.sum_product']
    set Dom := M3.divisors ×ˢ goodSqfree M3
    have hcop_dom : ∀ x ∈ Dom, x.1.Coprime x.2 := by
      intro x hx
      simp only [Dom, mem_product, Nat.mem_divisors, goodSqfree, mem_filter] at hx
      rw [Nat.coprime_iff_gcd_eq_one]
      by_contra hne
      obtain ⟨p, hpp, hpg⟩ := Nat.exists_prime_and_dvd hne
      have hp1 : p ∣ x.1 := dvd_trans hpg (Nat.gcd_dvd_left _ _)
      have hp2 : p ∣ x.2 := dvd_trans hpg (Nat.gcd_dvd_right _ _)
      have hpS : p ∈ S := hM3_pf p (Nat.mem_primeFactors.mpr ⟨hpp, dvd_trans hp1 hx.1.1, hM3_pos.ne'⟩)
      have hp3 : p % 4 = 3 := (hS_primes p hpS).2
      have hne3 : p % 4 ≠ 3 := hx.2.2.2 p (Nat.mem_primeFactors.mpr ⟨hpp, hp2, hx.2.2.1.ne_zero⟩)
      exact hne3 hp3
    have hinj_dom : Set.InjOn (fun x : ℕ × ℕ => x.1 * x.2) Dom := by
      intro x₁ hx₁ x₂ hx₂ heq
      dsimp only at heq
      have hx₁' := Finset.mem_coe.mp hx₁
      have hx₂' := Finset.mem_coe.mp hx₂
      have h12 : x₁.1.Coprime x₂.2 := by
        simp only [Dom, mem_product, Nat.mem_divisors, goodSqfree, mem_filter] at hx₁' hx₂'
        exact hcop_dom (x₁.1, x₂.2) (Finset.mem_product.mpr ⟨Nat.mem_divisors.mpr hx₁'.1, Finset.mem_filter.mpr hx₂'.2⟩)
      have h21 : x₂.1.Coprime x₁.2 := by
        simp only [Dom, mem_product, Nat.mem_divisors, goodSqfree, mem_filter] at hx₁' hx₂'
        exact hcop_dom (x₂.1, x₁.2) (Finset.mem_product.mpr ⟨Nat.mem_divisors.mpr hx₂'.1, Finset.mem_filter.mpr hx₁'.2⟩)
      have hd1 : x₁.1 ∣ x₂.1 := h12.dvd_of_dvd_mul_right (heq ▸ dvd_mul_right x₁.1 x₁.2)
      have hd2 : x₂.1 ∣ x₁.1 := h21.dvd_of_dvd_mul_right (heq.symm ▸ dvd_mul_right x₂.1 x₂.2)
      have hx1eq : x₁.1 = x₂.1 := Nat.dvd_antisymm hd1 hd2
      have hx1pos : 0 < x₁.1 := Nat.pos_of_mem_divisors (Finset.mem_product.mp hx₁').1
      have hx2eq : x₁.2 = x₂.2 := mul_left_cancel₀ hx1pos.ne' (by rw [← hx1eq] at heq; exact heq)
      exact Prod.ext hx1eq hx2eq
    have hmaps_dom : Dom.image (fun x : ℕ × ℕ => x.1 * x.2) ⊆ P.divisors.filter (· ≤ z) := by
      intro l hl
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hl
      have hcx := hcop_dom x hx
      simp only [Dom, mem_product, Nat.mem_divisors, goodSqfree, mem_filter, mem_Icc] at hx
      simp only [mem_filter, Nat.mem_divisors]
      have hx1P : x.1 ∣ P := dvd_trans hx.1.1 hM3_dvd_P
      have hx2P : x.2 ∣ P := by
        rw [← Nat.prod_primeFactors_of_squarefree hx.2.2.1]
        have hsub : x.2.primeFactors ⊆ Pset := by
          intro p hp
          have hpp := Nat.prime_of_mem_primeFactors hp
          have hp_le_x2 : p ≤ x.2 := Nat.le_of_dvd (by omega) (Nat.dvd_of_mem_primeFactors hp)
          simp only [Pset, mem_filter, mem_Icc]
          exact ⟨⟨hpp.two_le, hp_le_x2.trans (hx.2.1.2.trans hM3_le_z)⟩, hpp, Or.inr (hx.2.2.2 p hp)⟩
        exact Finset.prod_dvd_prod_of_subset _ _ id hsub
      have hmulP : x.1 * x.2 ∣ P := hcx.mul_dvd_of_dvd_of_dvd hx1P hx2P
      have hx1_le : x.1 ≤ M3 := Nat.le_of_dvd hM3_pos hx.1.1
      have hmul_le : x.1 * x.2 ≤ z := by
        have : x.1 * x.2 ≤ M3 * M3 := Nat.mul_le_mul hx1_le hx.2.1.2
        simpa [z, sq] using this
      exact ⟨⟨hmulP, hP_pos.ne'⟩, hmul_le⟩
    have hterm_dom : ∀ x ∈ Dom,
        (∏ p ∈ x.1.primeFactors, ((1 : ℝ) / ((p : ℝ) - 1))) * g2 x.2 =
        sv.selbergTerms (x.1 * x.2) := by
      intro x hx
      have hcx := hcop_dom x hx
      have hmemP := hmaps_dom (Finset.mem_image_of_mem _ hx)
      have hmulP : x.1 * x.2 ∣ P := (Nat.mem_divisors.mp (Finset.mem_filter.mp hmemP).1).1
      rw [hselb_eq _ hmulP]
      simp only [Dom, mem_product, Nat.mem_divisors, goodSqfree, mem_filter] at hx
      have hx1_ne : x.1 ≠ 0 := ne_zero_of_dvd_ne_zero hM3_pos.ne' hx.1.1
      have hx2_ne : x.2 ≠ 0 := hx.2.2.1.ne_zero
      rw [Nat.primeFactors_mul hx1_ne hx2_ne]
      have hdisj : Disjoint x.1.primeFactors x.2.primeFactors := by
        rw [Finset.disjoint_left]
        intro p hp1 hp2
        have hp_dvd_1 : p ∣ x.1 := Nat.dvd_of_mem_primeFactors hp1
        have hp_dvd_2 : p ∣ x.2 := Nat.dvd_of_mem_primeFactors hp2
        have hp_dvd_gcd : p ∣ Nat.gcd x.1 x.2 := Nat.dvd_gcd hp_dvd_1 hp_dvd_2
        rw [hcx.gcd_eq_one] at hp_dvd_gcd
        exact (Nat.prime_of_mem_primeFactors hp1).ne_one (Nat.dvd_one.mp hp_dvd_gcd)
      rw [Finset.prod_union hdisj]
      congr 1
      refine Finset.prod_congr rfl fun p hp => ?_
      have hpS : p ∈ S := hM3_pf p (Nat.mem_primeFactors.mpr
        ⟨Nat.prime_of_mem_primeFactors hp, dvd_trans (Nat.dvd_of_mem_primeFactors hp) hx.1.1, hM3_pos.ne'⟩)
      have hp3 : p % 4 = 3 := (hS_primes p hpS).2
      have hne1 : p % 4 ≠ 1 := by omega
      simp [omega1, hne1]
    calc ∑ x ∈ Dom, (∏ p ∈ x.1.primeFactors, ((1 : ℝ) / ((p : ℝ) - 1))) * g2 x.2
        = ∑ x ∈ Dom, sv.selbergTerms (x.1 * x.2) := Finset.sum_congr rfl hterm_dom
      _ = ∑ l ∈ Dom.image (fun x : ℕ × ℕ => x.1 * x.2), sv.selbergTerms l :=
            (Finset.sum_image hinj_dom).symm
      _ ≤ L := Finset.sum_le_sum_of_subset_of_nonneg hmaps_dom fun l hl _ => by
            simp only [mem_filter, Nat.mem_divisors] at hl
            exact (sv.selbergTerms_pos hl.1.1).le
  -- Step E: Combine numerical bounds to get 5 * a n < Nat.primeCounting n
  have hlogM3_pos : 0 < Real.log M3 := Real.log_pos (by exact_mod_cast (by omega : 1 < M3))
  have hlogn_eq : Real.log n = 10 * Real.log M3 := by
    simp only [n, Nat.cast_pow, Real.log_pow]
    ring
  have hlogn_pos : 0 < Real.log n := by linarith
  have hS1_lb : Real.log M3 / 40 ≤ ∑ q ∈ goodSqfree M3, g2 q :=
    sum_g2_ge_log_div_40 M3 hM3_ge100
  have hL_final : 25 * Real.log n ≤ L := by
    have hprod_lb : (10000 : ℝ) * (Real.log M3 / 40) ≤ L := by
      have h1 : (10000 : ℝ) * (Real.log M3 / 40) ≤
          (∏ p ∈ S, ((p : ℝ) / ((p : ℝ) - 1))) * (∑ q ∈ goodSqfree M3, g2 q) := by
        have hpos1 : 0 ≤ Real.log M3 / 40 := by linarith
        exact mul_le_mul hS_prod_gt.le hS1_lb hpos1 (by linarith)
      exact h1.trans hL_lb
    linarith [hlogn_eq]
  have hL_pos : 0 < L := by linarith
  have hmain_bnd : (n : ℝ) / L ≤ (n : ℝ) / (25 * Real.log n) := by
    gcongr
  have herr_bnd : 2 * (z : ℝ) ^ 4 ≤ (n : ℝ) / (100 * Real.log n) := by
    have hz4_eq : (z : ℝ) ^ 4 * (M3 : ℝ) ^ 2 = (n : ℝ) := by
      simp only [z, n, Nat.cast_pow]; ring
    have hM3_real : (200000 : ℝ) ≤ (M3 : ℝ) := by exact_mod_cast hM3_ge
    have hlog_le_M3 : Real.log M3 ≤ (M3 : ℝ) := by
      have := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < M3)
      linarith
    have hkey : 200 * Real.log n ≤ (M3 : ℝ) ^ 2 := by
      rw [hlogn_eq]
      nlinarith
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < 100 * Real.log n)]
    calc 2 * (z : ℝ) ^ 4 * (100 * Real.log n)
        = (z : ℝ) ^ 4 * (200 * Real.log n) := by ring
      _ ≤ (z : ℝ) ^ 4 * (M3 : ℝ) ^ 2 := by gcongr
      _ = (n : ℝ) := hz4_eq
  have ha_bnd : 5 * (OeisA69004.a n : ℝ) ≤ (1 / 4 : ℝ) * ((n : ℝ) / Real.log n) := by
    have h1 : (OeisA69004.a n : ℝ) ≤ (n : ℝ) / L + 2 * (z : ℝ) ^ 4 :=
      ha_le_sifted.trans hsieve
    have h2 : (n : ℝ) / (25 * Real.log n) + (n : ℝ) / (100 * Real.log n) =
        (1 / 20 : ℝ) * ((n : ℝ) / Real.log n) := by
      field_simp [hlogn_pos.ne']
      ring
    linarith
  -- Chebyshev lower bound on Nat.primeCounting n
  have hpi_lb : (1 / 2 : ℝ) * ((n : ℝ) / Real.log n) ≤ (Nat.primeCounting n : ℝ) := by
    have hcheb := Chebyshev.pi_ge n
    have hlog2 : (0.69 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
    have hn_ge : (1000 : ℝ) ≤ (n : ℝ) := by
      have : 1000 ≤ M3 := by omega
      have h1 : M3 ≤ M3 ^ 10 := Nat.le_self_pow (by norm_num) M3
      exact_mod_cast this.trans h1
    have hlog_n1 : Real.log ((n : ℝ) + 1) ≤ (n : ℝ) / 10 := by
      have h1 : Real.log (((n : ℝ) + 1) / 20) ≤ ((n : ℝ) + 1) / 20 - 1 :=
        Real.log_le_sub_one_of_pos (by linarith)
      have h2 : Real.log ((n : ℝ) + 1) = Real.log (((n : ℝ) + 1) / 20) + Real.log 20 := by
        rw [← Real.log_mul (by linarith) (by norm_num)]
        congr 1; ring
      have hlog20 : Real.log 20 ≤ 20 := by
        linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 20)]
      linarith
    have hnum : (1 / 2 : ℝ) * (n : ℝ) ≤ (n : ℝ) * Real.log 2 - Real.log ((n : ℝ) + 1) := by
      nlinarith
    have hdiv : (1 / 2 : ℝ) * ((n : ℝ) / Real.log n) ≤
        ((n : ℝ) * Real.log 2 - Real.log ((n : ℝ) + 1)) / Real.log n := by
      rw [← mul_div_assoc]
      exact div_le_div_of_nonneg_right hnum hlogn_pos.le
    exact hdiv.trans hcheb
  have hn_posR : (0 : ℝ) < (n : ℝ) / Real.log n := by positivity
  have hstrictR : (5 * OeisA69004.a n : ℝ) < (Nat.primeCounting n : ℝ) := by
    push_cast
    linarith
  change 5 * OeisA69004.a n < Nat.primeCounting n
  exact_mod_cast hstrictR

end OeisA69004Disproof


/-! A finite bound for the alternating harmonic sum of the character modulo four. -/

namespace A069004ExplicitRow

open Finset

/-- The odd terms alternate. At every new positive term past the first, the
preceding negative term has at least as much weight. -/
theorem chiFour_weighted_sum_le (w : ℕ → ℝ) (hw : ∀ m, 0 ≤ w m)
    (hanti : AntitoneOn w (Set.Ici 1)) (n : ℕ) :
    (∑ m ∈ range (n + 1), (ZMod.χ₄ m : ℝ) * w m) ≤ w 1 := by
  let S (r : ℕ) := ∑ m ∈ range (r + 1), (ZMod.χ₄ m : ℝ) * w m
  change S n ≤ w 1
  have step (r : ℕ) : S (r + 1) = S r + (ZMod.χ₄ (r+1 : ℕ) : ℝ) * w (r+1) :=
    sum_range_succ _ _
  induction n using Nat.strong_induction_on with
  | h n ih =>
    match n with
    | 0 => simpa [S, ZMod.χ₄_nat_eq_if_mod_four] using hw 1
    | 1 => norm_num [S, sum_range_succ, ZMod.χ₄_nat_eq_if_mod_four]
    | 2 => norm_num [S, sum_range_succ, ZMod.χ₄_nat_eq_if_mod_four]
    | k + 3 =>
      by_cases hp : (k+3) % 4 = 1
      · have hc₁ : ZMod.χ₄ (k+1 : ℕ) = -1 := ZMod.χ₄_nat_three_mod_four (by omega)
        have hc₂ : ZMod.χ₄ (k+2 : ℕ) = 0 := by
          rw [ZMod.χ₄_nat_eq_if_mod_four, if_pos (by omega)]
        have hc₃ := ZMod.χ₄_nat_one_mod_four hp
        have hk := ih k (by omega)
        have hwk := hanti (show 1 ≤ k+1 by omega) (show 1 ≤ k+3 by omega)
          (show k+1 ≤ k+3 by omega)
        rw [step (k+2), step (k+1), step k, hc₁, hc₂, hc₃]
        push_cast
        linarith
      · have hc : (ZMod.χ₄ (k+3 : ℕ) : ℝ) ≤ 0 := by
          rw [ZMod.χ₄_nat_eq_if_mod_four, if_neg hp]
          split <;> norm_num
        rw [step (k+2)]
        exact (add_le_of_nonpos_right (mul_nonpos_of_nonpos_of_nonneg hc (hw _))).trans (ih (k+2) (by omega))

/-- The finite sum includes the zero term at zero and extends through n. -/
theorem chiFour_harmonic_range_le_one (n : ℕ) :
    (∑ m ∈ range (n+1), (ZMod.χ₄ m : ℝ) / m) ≤ 1 := by
  have hanti : AntitoneOn (fun m : ℕ => (m : ℝ)⁻¹) (Set.Ici 1) := by
    intro a ha b _ hab
    exact inv_anti₀ (by exact_mod_cast (show 0 < a by exact ha)) (by exact_mod_cast hab)
  simpa [div_eq_mul_inv] using chiFour_weighted_sum_le (fun m : ℕ => (m : ℝ)⁻¹)
    (by intro m; positivity) hanti n

/-- Partial sums over the positive integers, including the empty sum for n=0. -/
theorem chiFour_harmonic_le_one (n : ℕ) :
    (∑ m ∈ Icc 1 n, (ZMod.χ₄ m : ℝ) / m) ≤ 1 := by
  have hsets : Icc 1 n = Ico 1 (n+1) := by ext k; simp
  rw [hsets, sum_Ico_eq_sub _ (by omega : 1 ≤ n+1)]
  simpa using chiFour_harmonic_range_le_one n

end A069004ExplicitRow

/-! Finite divisor convolution for the character modulo four. -/

namespace A069004Cutoff

open Finset ArithmeticFunction

def character : ArithmeticFunction ℤ where
  toFun n := ZMod.χ₄ n
  map_zero' := rfl

def oddIndicator : ArithmeticFunction ℤ where
  toFun n := (ZMod.χ₄ n) ^ 2
  map_zero' := by decide

def primeWeight (p : ℕ) : ℤ := if p % 4 = 3 then 2 else 0

def inertWeight : ArithmeticFunction ℤ := prodPrimeFactors primeWeight

theorem char_mult : character.IsMultiplicative := by
  constructor
  · rfl
  · intro a b _
    change ZMod.χ₄ ((a*b : ℕ) : ZMod 4) = _
    simp only [Nat.cast_mul, map_mul]
    rfl

theorem odd_mult : oddIndicator.IsMultiplicative := by
  constructor
  · rfl
  · intro a b _
    change (ZMod.χ₄ ((a*b : ℕ) : ZMod 4))^2 = (ZMod.χ₄ a)^2 * (ZMod.χ₄ b)^2
    rw [Nat.cast_mul, map_mul, mul_pow]

private theorem weight_prime_pow {p k : ℕ} (hp : p.Prime) (hk : k ≠ 0) :
    inertWeight (p^k) = primeWeight p := by
  rw [inertWeight, prodPrimeFactors_apply (pow_ne_zero _ hp.ne_zero),
    Nat.primeFactors_prime_pow hk hp, Finset.prod_singleton]

private theorem scalar_sum (x : ℤ) (k : ℕ) :
    (∑ j ∈ range k, x^j * (1-x)) + x^k = 1 := by
  induction k with
  | zero => simp
  | succ k ih => rw [sum_range_succ, pow_succ]; linarith

private theorem char_prime_pow (p j : ℕ) : character (p^j) = (ZMod.χ₄ p)^j := by
  change ZMod.χ₄ ((p^j : ℕ) : ZMod 4) = _
  rw [Nat.cast_pow, map_pow]

theorem inert_convolution : character * inertWeight = oddIndicator := by
  apply (IsMultiplicative.eq_iff_eq_on_prime_powers _ (char_mult.mul (IsMultiplicative.prodPrimeFactors _))
    _ odd_mult).mpr
  intro p k hp
  change (character * inertWeight) (p^k) = oddIndicator (p^k)
  rw [ArithmeticFunction.mul_apply, Nat.sum_divisorsAntidiagonal (fun a b => character a * inertWeight b),
    Nat.sum_divisors_prime_pow hp, Finset.sum_range_succ]
  have hlast : character (p ^ k) * inertWeight (p ^ k / p ^ k) = (ZMod.χ₄ p) ^ k := by
    rw [Nat.div_self (pow_pos hp.pos _), (show inertWeight 1 = 1 from (IsMultiplicative.prodPrimeFactors primeWeight).1),
        mul_one, char_prime_pow]
  have hterm : ∀ j ∈ range k, character (p ^ j) * inertWeight (p ^ k / p ^ j) =
      (ZMod.χ₄ p)^j * primeWeight p := by
    intro j hj
    have hj' := Finset.mem_range.mp hj
    rw [Nat.pow_div hj'.le hp.pos, weight_prime_pow hp (by omega), char_prime_pow]
  rw [hlast, Finset.sum_congr rfl hterm]
  change _ = (ZMod.χ₄ ((p^k : ℕ) : ZMod 4)) ^ 2
  rw [Nat.cast_pow, map_pow]
  by_cases h2 : p = 2
  · subst p
    have h : ZMod.χ₄ (2 : ZMod 4) = 0 := rfl
    cases k <;> simp [primeWeight, h]
  · have hodd := hp.eq_two_or_odd.resolve_left h2
    have hc : p % 4 = 1 ∨ p % 4 = 3 := by omega
    rcases hc with h1 | h3
    · have hχ := ZMod.χ₄_nat_one_mod_four h1
      have hne : p % 4 ≠ 3 := by omega
      simp [hχ, primeWeight, hne]
    · have hχ := ZMod.χ₄_nat_three_mod_four h3
      have hscalar := scalar_sum (-1) k
      norm_num at hscalar
      simp only [hχ, primeWeight, h3, if_true]
      rw [hscalar, ← pow_mul, Nat.mul_comm, pow_mul]
      norm_num


end A069004Cutoff

/-! Finite lower bounds for the odd harmonic sum used in the explicit A069004 row. -/
namespace A069004Cutoff

open Finset

/-- Sum of the first m reciprocals of positive odd integers. -/
def oddHarmonic (m : ℕ) : ℚ :=
  ∑ j ∈ range m, 1 / (2 * (j : ℚ) + 1)

/-- Doubling the number of odd denominators adds at least one quarter. -/
theorem oddHarmonic_double (m : ℕ) (hm : 0 < m) :
    oddHarmonic m + 1 / 4 ≤ oddHarmonic (2 * m) := by
  rw [two_mul, oddHarmonic, oddHarmonic, Finset.sum_range_add]
  apply add_le_add_right
  have hm' : 0 < (m : ℚ) := by exact_mod_cast hm
  calc
    (1 : ℚ) / 4 = ∑ _j ∈ range m, 1 / (4 * (m : ℚ)) := by
      simp [Finset.sum_const, nsmul_eq_mul]
      field_simp
    _ ≤ ∑ j ∈ range m, 1 / (2 * ((m + j : ℕ) : ℚ) + 1) := by
      refine Finset.sum_le_sum fun j hj => ?_
      have hj' : (j : ℚ) + 1 ≤ m := by exact_mod_cast (Nat.succ_le_of_lt (Finset.mem_range.mp hj))
      apply one_div_le_one_div_of_le (by positivity)
      push_cast
      linarith

/-- The odd positive integers below 2^(k+1) are 2j+1, 0 ≤ j < 2^k. -/
theorem oddHarmonic_two_pow (k : ℕ) :
    1 + (k : ℚ) / 4 ≤ oddHarmonic (2 ^ k) := by
  induction k with
  | zero => norm_num [oddHarmonic]
  | succ k ih =>
      have h := oddHarmonic_double (2 ^ k) (by positivity)
      rw [pow_succ, mul_comm]
      push_cast
      linarith

theorem explicit_odd_harmonic :
    (10000 : ℚ) ^ 2 < oddHarmonic (2 ^ 400000000) := by
  calc
    (10000 : ℚ) ^ 2 < 1 + (400000000 : ℚ) / 4 := by norm_num
    _ ≤ _ := oddHarmonic_two_pow 400000000


end A069004Cutoff

namespace A069004Cutoff

open Finset

/-- The positive-index harmonic sum of the odd indicator is the usual odd harmonic sum. -/
theorem odd_indicator_harmonic (m : ℕ) :
    ∑ n ∈ Icc 1 (2*m), (oddIndicator n : ℚ) / (n : ℚ) = oddHarmonic m := by
  induction m with
  | zero => simp [oddHarmonic]
  | succ m ih =>
    have h1 : oddIndicator (2*m+1) = 1 := by
      change ZMod.χ₄ ((2*m+1 : ℕ) : ZMod 4)^2 = _
      rw [ZMod.χ₄_nat_eq_if_mod_four]
      have h : (2*m+1)%2 ≠ 0 := by omega
      by_cases ht : (2*m+1)%4 = 1 <;> simp [h, ht]
    have h2 : oddIndicator (2*m+1+1) = 0 := by
      change ZMod.χ₄ ((2*m+1+1 : ℕ) : ZMod 4)^2 = _
      rw [ZMod.χ₄_nat_eq_if_mod_four]
      have h : (2*m+1+1)%2 = 0 := by omega
      simp [h]
    rw [show 2*(m+1) = 2*m+1+1 by omega, Finset.sum_Icc_succ_top (a := 1) (b := 2*m+1) (by omega),
        Finset.sum_Icc_succ_top (a := 1) (b := 2*m) (by omega), ih, h1, h2, oddHarmonic, oddHarmonic, sum_range_succ]
    push_cast <;> ring

/-- Same finite identity after transport to the reals. -/
theorem odd_indicator_harmonic_real (m : ℕ) :
    ∑ n ∈ Icc 1 (2*m), (oddIndicator n : ℝ) / (n : ℝ) = (oddHarmonic m : ℝ) := by
  exact_mod_cast odd_indicator_harmonic m

end A069004Cutoff

namespace A069004Cutoff
open Finset

/-- Regroup a finite divisor sum by the divisor and its complementary factor. -/
theorem finite_divisor_regroup {M : Type*} [AddCommMonoid M]
    (Y : ℕ) (f : ℕ → ℕ → M) :
    ∑ n ∈ Icc 1 Y, ∑ d ∈ n.divisors, f d (n / d) =
      ∑ d ∈ Icc 1 Y, ∑ m ∈ Icc 1 (Y / d), f d m := by
  classical
  have hdiv (n : ℕ) (hn : n ∈ Icc 1 Y) :
      n.divisors = (Icc 1 Y).filter (· ∣ n) := by
    have h := mem_Icc.mp hn
    ext d
    simp only [Nat.mem_divisors, mem_filter, mem_Icc]
    constructor
    · rintro ⟨hd, hn'⟩
      exact ⟨⟨Nat.pos_of_dvd_of_pos hd h.1, (Nat.le_of_dvd h.1 hd).trans h.2⟩, hd⟩
    · rintro ⟨_, hd⟩
      exact ⟨hd, Nat.ne_of_gt h.1⟩
  calc
    _ = ∑ n ∈ Icc 1 Y, ∑ d ∈ Icc 1 Y, if d ∣ n then f d (n / d) else 0 := by
      apply sum_congr rfl
      intro n hn
      rw [hdiv n hn, sum_filter]
    _ = ∑ d ∈ Icc 1 Y, ∑ n ∈ (Icc 1 Y).filter (d ∣ ·), f d (n / d) := by
      rw [sum_comm]
      simp only [sum_filter]
    _ = _ := by
      apply sum_congr rfl
      intro d hd
      have hd' := (mem_Icc.mp hd).1
      symm
      apply sum_bij' (fun m _ ↦ m*d) (fun n _ ↦ n/d)
      · intro m hm
        have hm' := mem_Icc.mp hm
        exact mem_filter.mpr ⟨mem_Icc.mpr ⟨Nat.mul_pos hm'.1 hd',
          (Nat.le_div_iff_mul_le hd').mp hm'.2⟩, dvd_mul_left _ _⟩
      · intro n hn
        obtain ⟨hn, hn'⟩ := mem_filter.mp hn
        obtain ⟨h1, h2⟩ := mem_Icc.mp hn
        exact mem_Icc.mpr ⟨(Nat.le_div_iff_mul_le hd').mpr (by simpa using Nat.le_of_dvd h1 hn'),
          Nat.div_le_div_right h2⟩
      · intro m _
        exact Nat.mul_div_cancel m hd'
      · intro n hn
        exact Nat.div_mul_cancel (mem_filter.mp hn).2
      · intro m _
        rw [Nat.mul_div_cancel m hd']

/-- Harmonic weights turn the finite divisor convolution into partial character sums. -/
theorem weighted_divisor_regroup {K : Type*} [Field K] [CharZero K]
    (Y : ℕ) (b χ : ℕ → K) :
    ∑ n ∈ Icc 1 Y, (∑ d ∈ n.divisors, b d * χ (n / d)) / (n : K) =
      ∑ d ∈ Icc 1 Y, (b d / (d : K)) * ∑ m ∈ Icc 1 (Y / d), χ m / (m : K) := by
  simp_rw [Finset.sum_div, Finset.mul_sum]
  rw [← finite_divisor_regroup Y (fun d m ↦ b d / (d : K) * (χ m / (m : K)))]
  apply sum_congr rfl
  intro n hn
  apply sum_congr rfl
  intro d hd
  have hz : ((n / d : ℕ) : K) * (d : K) = (n : K) := by
    exact_mod_cast Nat.div_mul_cancel (Nat.mem_divisors.mp hd).1
  rw [div_mul_div_comm, mul_comm (d : K), hz]

/-- A uniform upper bound for partial character sums bounds the full convolution. -/
theorem weighted_divisor_le {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (Y : ℕ) (b χ : ℕ → K) (C : K) (hb : ∀ d ∈ Icc 1 Y, 0 ≤ b d)
    (hχ : ∀ Z ≤ Y, ∑ m ∈ Icc 1 Z, χ m / (m : K) ≤ C) :
    ∑ n ∈ Icc 1 Y, (∑ d ∈ n.divisors, b d * χ (n / d)) / (n : K) ≤
      (∑ d ∈ Icc 1 Y, b d / (d : K)) * C := by
  rw [weighted_divisor_regroup, Finset.sum_mul]
  apply sum_le_sum
  intro d hd
  exact mul_le_mul_of_nonneg_left (hχ _ (Nat.div_le_self _ _))
    (div_nonneg (hb d hd) (Nat.cast_nonneg d))

end A069004Cutoff

/-! Bound the odd reciprocal sum by the positive inert weights. -/

namespace A069004Cutoff

open Finset ArithmeticFunction

theorem weight_nonnegative (n : ℕ) : 0 ≤ inertWeight n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · rw [inertWeight, prodPrimeFactors_apply hn]
    refine Finset.prod_nonneg fun _ _ => ?_
    unfold primeWeight
    split <;> norm_num

theorem odd_real_divisor (n : ℕ) :
    (oddIndicator n : ℝ) = ∑ d ∈ n.divisors, (inertWeight d : ℝ) * (character (n/d) : ℝ) := by
  have h : oddIndicator n = ∑ d ∈ n.divisors, inertWeight d * character (n/d) := by
    rw [← inert_convolution, mul_comm character inertWeight, ArithmeticFunction.mul_apply,
      Nat.sum_divisorsAntidiagonal (fun d m => inertWeight d * character m)]
  exact_mod_cast h

theorem odd_harmonic_le_inert (Y : ℕ) :
    ∑ n ∈ Icc 1 Y, (oddIndicator n : ℝ)/n ≤
      ∑ d ∈ Icc 1 Y, (inertWeight d : ℝ)/d := by
  have h := weighted_divisor_le Y (fun d => (inertWeight d : ℝ)) (fun m => (character m : ℝ))
    1 (fun d _ => by exact_mod_cast weight_nonnegative d)
    (fun Z _ => A069004ExplicitRow.chiFour_harmonic_le_one Z)
  simpa only [← odd_real_divisor, mul_one] using h


end A069004Cutoff

namespace A069004Cutoff
open Finset ArithmeticFunction

private def weightLocal (p : ℕ) : ℤ := if p % 4 = 3 then 2 else 0
private def weightGlobal := prodPrimeFactors weightLocal
private noncomputable def weightedRecip (n : ℕ) : ℝ := (weightGlobal n : ℝ) / n

private theorem reciprocal_one : weightedRecip 1 = 1 := by
  have h : weightGlobal 1 = 1 := (IsMultiplicative.prodPrimeFactors weightLocal).1
  simp [weightedRecip, h]

private theorem reciprocal_mul {m n : ℕ} (h : m.Coprime n) :
    weightedRecip (m*n) = weightedRecip m * weightedRecip n := by
  have hm : weightGlobal (m*n) = weightGlobal m * weightGlobal n :=
    (IsMultiplicative.prodPrimeFactors weightLocal).2 h
  simp [weightedRecip, hm, div_mul_div_comm]

private theorem reciprocal_nonneg (m : ℕ) : 0 ≤ weightedRecip m := by
  have h : 0 ≤ weightGlobal m := by
    by_cases hm : m = 0
    · simp [hm]
    · rw [weightGlobal, prodPrimeFactors_apply hm]
      exact prod_nonneg fun i _ => by unfold weightLocal; split <;> norm_num
  exact div_nonneg (by exact_mod_cast h) (Nat.cast_nonneg _)

private theorem reciprocal_prime_succ {p : ℕ} (hp : p.Prime) (j : ℕ) :
    weightedRecip (p^(j+1)) = (weightLocal p : ℝ) * (p : ℝ)⁻¹ * (p : ℝ)⁻¹ ^ j := by
  rw [weightedRecip, weightGlobal, prodPrimeFactors_apply (pow_ne_zero _ hp.ne_zero),
    Nat.primeFactors_prime_pow (by omega) hp, Finset.prod_singleton]
  rw [Nat.cast_pow, div_eq_mul_inv, ← inv_pow, pow_succ]
  ring

private theorem prime_series {p : ℕ} (hp : p.Prime) :
    HasSum (fun j : ℕ => weightedRecip (p^j))
      (1 + (weightLocal p : ℝ)/((p : ℝ)-1)) := by
  have hp1 : 1 < (p : ℝ) := by exact_mod_cast hp.one_lt
  have hpos : 0 < (p : ℝ) := by positivity
  have hx : (p : ℝ)⁻¹ < 1 := (inv_lt_one₀ hpos).mpr hp1
  have hg := (hasSum_geometric_of_lt_one (inv_nonneg.mpr hpos.le) hx).mul_left
    ((weightLocal p : ℝ)*(p : ℝ)⁻¹)
  rw [← hasSum_nat_add_iff' 1]
  simp only [Finset.sum_range_one, pow_zero, reciprocal_one, add_sub_cancel_left]
  simp_rw [reciprocal_prime_succ hp]
  have alg : (weightLocal p : ℝ) / ((p:ℝ)-1) =
      ((weightLocal p : ℝ)*(p:ℝ)⁻¹) * (1 - (p:ℝ)⁻¹)⁻¹ := by
    have hp0 : (p:ℝ) ≠ 0 := ne_of_gt hpos
    have hp' : (p:ℝ)-1 ≠ 0 := sub_ne_zero.mpr hp1.ne'
    have hx' : 1 - (p:ℝ)⁻¹ ≠ 0 := sub_ne_zero.mpr hx.ne'
    field_simp [hp0, hp', hx'] <;> ring
  rw [alg]
  exact hg

theorem finite_inert_harmonic_euler (Y : ℕ) :
    (∑ n ∈ Icc 1 Y, (((prodPrimeFactors (fun p : ℕ =>
       if p % 4 = 3 then (2 : ℤ) else 0)) n : ℤ) : ℝ)/n) ≤
    ∏ p ∈ (range (Y+1)).filter (fun p => p.Prime ∧ p % 4 = 3),
      (((p : ℝ)+1)/((p : ℝ)-1)) := by
  let s := range (Y+1)
  have hs : ∀ n ∈ Icc 1 Y, n ∈ Nat.factoredNumbers s := by
    intro n hn
    obtain ⟨hn1, hnY⟩ := mem_Icc.mp hn
    apply Nat.mem_factoredNumbers_iff_forall_le.mpr
    refine ⟨by omega, ?_⟩
    intro p hpn _ _
    exact mem_range.mpr (by omega)
  have H := (EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_tsum
    reciprocal_one (fun h => reciprocal_mul h) (fun {p} hp => ?_) s).2
  case refine_1 =>
    simpa only [Real.norm_eq_abs, abs_of_nonneg (reciprocal_nonneg _)] using (prime_series hp).summable
  have hsum := sum_le_hasSum ((Icc 1 Y).subtype (· ∈ Nat.factoredNumbers s))
    (fun n _ => reciprocal_nonneg n.val) H
  rw [sum_subtype_of_mem weightedRecip hs] at hsum
  change (∑ n ∈ Icc 1 Y, weightedRecip n) ≤ _
  refine hsum.trans_eq ?_
  rw [← Finset.filter_filter]
  rw [Finset.prod_filter (fun p : ℕ => p % 4 = 3)]
  apply Finset.prod_congr rfl
  intro p hp
  have hpp := (Finset.mem_filter.mp hp).2
  rw [(prime_series hpp).tsum_eq]
  by_cases hi : p%4=3
  · have hp1 : 1 < (p : ℝ) := by exact_mod_cast hpp.one_lt
    simp [weightLocal, hi]
    field_simp [sub_ne_zero.mpr hp1.ne'] <;> ring
  · simp [weightLocal, hi]

end A069004Cutoff

/-! Product comparisons for the inert primes in an explicit cutoff. -/

namespace A069004Cutoff

open Finset

def inertPrimesTo (Y : ℕ) : Finset ℕ :=
  (range (Y+1)).filter fun p => p.Prime ∧ p % 4 = 3

theorem inertPrimesTo_spec {p Y : ℕ} (h : p ∈ inertPrimesTo Y) :
    p.Prime ∧ p % 4 = 3 := (mem_filter.mp h).2

theorem inertPrimesTo_three {p Y : ℕ} (h : p ∈ inertPrimesTo Y) : 3 ≤ p := by
  have hp := (inertPrimesTo_spec h).2
  omega

theorem inert_comparison (Y : ℕ) :
    ∏ p ∈ inertPrimesTo Y, (((p : ℝ)+1)/((p : ℝ)-1)) ≤
      (∏ p ∈ inertPrimesTo Y, (p : ℝ)/((p : ℝ)-1)) ^ 2 := by
  rw [← Finset.prod_pow]
  apply Finset.prod_le_prod
  · intro p hp
    have h3 : (3 : ℝ) ≤ p := by exact_mod_cast inertPrimesTo_three hp
    exact div_nonneg (by linarith) (by linarith)
  · intro p hp
    have h3 : (3 : ℝ) ≤ p := by exact_mod_cast inertPrimesTo_three hp
    rw [div_pow]
    apply (div_le_div_iff₀ (by linarith) (sq_pos_of_pos (show (0 : ℝ) < (p : ℝ)-1 by linarith))).mpr
    nlinarith

theorem sieve_product_bound {Y : ℕ}
    (h : (10000 : ℝ)^2 < (∏ p ∈ inertPrimesTo Y, (p : ℝ)/((p : ℝ)-1))^2) :
    (200000 ≤ ∏ p ∈ inertPrimesTo Y, p) ∧
      (10000 : ℝ) < ∏ p ∈ inertPrimesTo Y, (p : ℝ)/((p : ℝ)-1) := by
  have hP : 0 ≤ ∏ p ∈ inertPrimesTo Y, (p : ℝ)/((p : ℝ)-1) := by
    refine prod_nonneg fun p hp => ?_
    have h3 : (3 : ℝ) ≤ p := by exact_mod_cast inertPrimesTo_three hp
    exact div_nonneg (Nat.cast_nonneg p) (by linarith)
  have hM : (∏ p ∈ inertPrimesTo Y, (p : ℝ)/((p : ℝ)-1))^2 ≤
      ((∏ p ∈ inertPrimesTo Y, p : ℕ) : ℝ) := by
    rw [← Finset.prod_pow, Nat.cast_prod]
    refine Finset.prod_le_prod (fun _ _ => sq_nonneg _) fun p hp => ?_
    have h3 : (3 : ℝ) ≤ p := by exact_mod_cast inertPrimesTo_three hp
    rw [div_pow, div_le_iff₀ (sq_pos_of_pos (show (0 : ℝ) < (p : ℝ)-1 by linarith))]
    nlinarith [mul_nonneg (show 0 ≤ (p : ℝ) by positivity)
      (show 0 ≤ ((p : ℝ)-1)^2 - p by nlinarith [sq_nonneg ((p : ℝ)-3)])]
  constructor
  · have hh : (200000 : ℝ) ≤ ((∏ p ∈ inertPrimesTo Y, p : ℕ) : ℝ) := by linarith
    exact_mod_cast hh
  · nlinarith


end A069004Cutoff

/-! An explicit family of A069004 counterexamples. The final sieve implication is
extracted from PastaPastaPasta's upstream proof, commit
bcea01aab3f3a3f6ba41afd1207183477f35bade. -/

namespace A069004Cutoff

open Finset

/-- At k = 400000000 this cutoff is 2 ^ 400000001. -/
def dyadicCutoff (k : ℕ) : ℕ := 2 * 2^k

def witnessAt (Y : ℕ) : ℕ := (∏ p ∈ inertPrimesTo Y, p)^10

theorem dyadicCutoff_eq_pow (k : ℕ) : dyadicCutoff k = 2^(k+1) :=
  (pow_succ' (2 : ℕ) k).symm

private theorem odd_sum_cast (m : ℕ) (h : (10000 : ℚ)^2 < oddHarmonic m) :
    (10000 : ℝ)^2 < ∑ n ∈ Icc 1 (2*m), (oddIndicator n : ℝ)/n := by
  rw [odd_indicator_harmonic_real]
  exact_mod_cast h

private theorem dyadic_odd_sum (k : ℕ) (h : (10000 : ℚ)^2 < oddHarmonic (2^k)) :
    (10000 : ℝ)^2 < ∑ n ∈ Icc 1 (dyadicCutoff k), (oddIndicator n : ℝ)/n :=
  odd_sum_cast (2^k) h

theorem cutoff_odd_sum : (10000 : ℝ)^2 <
    ∑ n ∈ Icc 1 (dyadicCutoff 400000000), (oddIndicator n : ℝ)/n :=
  dyadic_odd_sum 400000000 explicit_odd_harmonic

/-- A finite Euler-product lower bound for every cutoff, including small cutoffs. -/
theorem harmonic_product_bound (Y : ℕ) :
    ∑ n ∈ Icc 1 Y, (oddIndicator n : ℝ)/n ≤
      (∏ p ∈ inertPrimesTo Y, (p : ℝ)/((p : ℝ)-1)) ^ 2 := by
  calc
    _ ≤ ∑ n ∈ Icc 1 Y, (inertWeight n : ℝ)/n := odd_harmonic_le_inert Y
    _ ≤ ∏ p ∈ inertPrimesTo Y, (((p : ℝ)+1)/((p : ℝ)-1)) :=
      finite_inert_harmonic_euler Y
    _ ≤ _ := inert_comparison Y

theorem sieve_assumptions (Y : ℕ) (hY : (dyadicCutoff 400000000) ≤ Y) :
    200000 ≤ ∏ p ∈ inertPrimesTo Y, p ∧
      (10000 : ℝ) < ∏ p ∈ inertPrimesTo Y, (p : ℝ)/((p : ℝ)-1) := by
  have hsub : Icc 1 (dyadicCutoff 400000000) ⊆ Icc 1 Y := fun n hn =>
    mem_Icc.mpr ⟨(mem_Icc.mp hn).1, (mem_Icc.mp hn).2.trans hY⟩
  apply sieve_product_bound
  calc
    (10000 : ℝ)^2 < ∑ n ∈ Icc 1 (dyadicCutoff 400000000), (oddIndicator n : ℝ)/n := cutoff_odd_sum
    _ ≤ ∑ n ∈ Icc 1 Y, (oddIndicator n : ℝ)/n := by
      refine sum_le_sum_of_subset_of_nonneg hsub fun n _ _ => ?_
      have h : (0 : ℤ) ≤ oddIndicator n := sq_nonneg _
      exact div_nonneg (by exact_mod_cast h) (Nat.cast_nonneg _)
    _ ≤ _ := harmonic_product_bound Y

theorem explicit_family (Y : ℕ) (hY : (dyadicCutoff 400000000) ≤ Y) :
    1 < witnessAt Y ∧ 5 * OeisA69004.a (witnessAt Y) < Nat.primeCounting (witnessAt Y) := by
  obtain ⟨hM, hP⟩ := sieve_assumptions Y hY
  constructor
  · change 1 < (∏ p ∈ inertPrimesTo Y, p)^10
    exact one_lt_pow₀ (by omega) (by decide)
  · exact OeisA69004Disproof.finite_inert_sieve_counterexample (inertPrimesTo Y)
      (fun p hp => inertPrimesTo_spec hp) hM hP

theorem explicit_row : 1 < witnessAt (dyadicCutoff 400000000) ∧
    5 * OeisA69004.a (witnessAt (dyadicCutoff 400000000)) < Nat.primeCounting (witnessAt (dyadicCutoff 400000000)) :=
  explicit_family (dyadicCutoff 400000000) le_rfl




end A069004Cutoff

theorem OMA.disproof : ¬ (type_of% @OeisA69004.conjecture2.variants.without_upper_bound) := by
  intro h
  exact (Nat.not_le_of_lt A069004Cutoff.explicit_row.2) (h.1 _ A069004Cutoff.explicit_row.1)
