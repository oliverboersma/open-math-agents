import OMAReductions.R_RiemannHypothesis_robin_criterion_R1_H1_R1
import Mathlib
/- Copyright (c) 2026 Jonas Whidden. All rights reserved.
Portions adapted under Apache-2.0 from kimihiro64/Robin1984 at
e3697139babfe0f6cc7a76a08bf41a92aa7a2978, CAProfile, PrimeReferenceSign,
ExponentProxyBound and AbundancyExponentBound. The finite-support benchmark
separates the two remaining prime estimates from the divisor arithmetic. -/

namespace OMA.R_RiemannHypothesis_robin_criterion_R1_H1_R1_H2_R1

open Real
open scoped ArithmeticFunction.sigma

/-- Conditional upper estimate for the finite prime benchmark. The correction
over T is a partial sum of the absolutely convergent Euler product correction. -/
def H1 : Prop := RiemannHypothesis → ∀ H : ℝ, exp 30 < H →
    ∀ T : Finset ℕ, (∀ p ∈ T, Nat.Prime p) →
      (∑ p ∈ T, -(log (1 - 1 / (p : ℝ)) + 1 / (p : ℝ))) +
        (∑ p ∈ Nat.primesLE ⌊H⌋₊, (1 / (p : ℝ) - log p / (H * log H))) +
        H / (H * log H) <
        eulerMascheroniConstant + log (log H) +
          (113/50 : ℝ) * (H^(-(1/2 : ℝ)) * (log H)⁻¹)

/-- Conditional lower estimate for the loss paid by the exponent at every
prime up to half the height, including primes absent from the factorization. -/
def H2 : Prop := RiemannHypothesis → ∀ H : ℝ, exp 30 < H →
    (113/50 : ℝ) * (H^(-(1/2 : ℝ)) * (log H)⁻¹) ≤
      ∑ p ∈ Nat.primesLE ⌊H/2⌋₊, min (log p / (H * log H)) ((p : ℝ)⁻¹ ^ 2)


theorem robin_prime_reference_atom_sign {u v : Real} (hu : 1 < u) (hv : 1 < v) :
    And (u <= v -> 0 <= 1 / u - Real.log u / (v * Real.log v))
      (v <= u -> 1 / u - Real.log u / (v * Real.log v) <= 0) := by
  have huPos : 0 < u := by linarith
  have hvPos : 0 < v := by linarith
  have hLogU := Real.log_pos hu
  have hLogV := Real.log_pos hv
  have hFactor : 0 < u * (v * Real.log v) := by positivity
  have hEq : (1 / u - Real.log u / (v * Real.log v)) *
      (u * (v * Real.log v)) = v * Real.log v - u * Real.log u := by
    field_simp
  constructor
  . intro h
    have hLog := Real.log_le_log huPos h
    have hMul : u * Real.log u <= v * Real.log v := by gcongr
    nlinarith
  . intro h
    have hLog := Real.log_le_log hvPos h
    have hMul : v * Real.log v <= u * Real.log u := by gcongr
    nlinarith

theorem robin_absent_prime_cost {H p : Real} (hH : 2 <= H) (hp : 2 <= p) (hpH : p <= H / 2) :
    (Inv.inv p)^2 <= 1 / p - Real.log p / (H * Real.log H) := by
  have hHPos : 0 < H := by linarith
  have hpPos : 0 < p := by linarith
  have hpOne : 1 < p := by linarith
  have hHOne : 1 < H := by linarith
  have hLogH := Real.log_pos hHOne
  have hLogP := Real.log_pos hpOne
  have hLog : Real.log p <= Real.log H := Real.log_le_log hpPos (by linarith)
  have hSmall : Real.log p / (H * Real.log H) <= 1 / H := by
    have h := div_le_div_of_nonneg_right hLog (mul_nonneg hHPos.le hLogH.le)
    have hEq : Real.log H / (H * Real.log H) = 1 / H := by field_simp
    exact h.trans_eq hEq
  have hInv : 1 / H <= 1 / (2 * p) :=
    one_div_le_one_div_of_le (by positivity) (by linarith)
  have hLast : (Inv.inv p)^2 <= 1 / p - 1 / (2 * p) := by
    have hInvP : 0 < Inv.inv p := inv_pos.mpr hpPos
    have hInvLe : Inv.inv p <= (1 / 2 : Real) := by
      simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0 : Real) < 2) hp
    have hEq : 1 / p - 1 / (2 * p) = (1 / 2 : Real) * Inv.inv p := by ring
    rw [hEq]
    nlinarith
  linarith

/-- The a=0 branch is essential: omitted primes pay from the benchmark. -/
theorem robin_exponent_proxy_plus_cost_le_benchmark
    {H p : Real} (hH : 2 <= H) (hp : 2 <= p) (a : Nat) :
    (if a = 0 then 0 else 1 / (p : ℝ) - (a : ℝ) * log p / (H * log H) - ((p : ℝ)⁻¹)^(a + 1)) +
        (if p <= H / 2 then min (Real.log p / (H * Real.log H)) ((Inv.inv p)^2) else 0) <=
      (if p <= H then 1 / p - Real.log p / (H * Real.log H) else 0) := by
  have hpOne : 1 < p := by linarith
  have hHOne : 1 < H := by linarith
  have hLogP := Real.log_pos hpOne
  have hLogH := Real.log_pos hHOne
  have hCost : 0 <= Real.log p / (H * Real.log H) := by positivity
  have hPow : 0 <= (Inv.inv p)^(a + 1) := by positivity
  have hSigns := robin_prime_reference_atom_sign hpOne hHOne
  by_cases ha : a = 0
  . subst a
    rw [if_pos rfl, zero_add]
    by_cases hpHalf : p <= H / 2
    . have hpFull : p <= H := by linarith
      rw [if_pos hpHalf, if_pos hpFull]
      exact (min_le_right _ _).trans (robin_absent_prime_cost hH hp hpHalf)
    . rw [if_neg hpHalf]
      split_ifs with hpFull
      . exact hSigns.1 hpFull
      . exact le_rfl
  . have haOne : 1 <= a := by omega
    have haReal : (1 : Real) <= a := by exact_mod_cast haOne
    rw [if_neg ha]
    have hMul : (a : Real) * Real.log p / (H * Real.log H) =
        (a : Real) * (Real.log p / (H * Real.log H)) := by ring
    rw [hMul]
    by_cases hpHalf : p <= H / 2
    . have hpFull : p <= H := by linarith
      rw [if_pos hpHalf, if_pos hpFull]
      by_cases haEq : a = 1
      . subst a
        norm_num
        linarith [min_le_right (Real.log p / (H * Real.log H)) (Inv.inv (p^2))]
      . have haTwo : (2 : Real) <= a := by exact_mod_cast (show 2 <= a by omega)
        have hMin := min_le_left (Real.log p / (H * Real.log H)) ((Inv.inv p)^2)
        nlinarith
    . rw [if_neg hpHalf, add_zero]
      by_cases hpFull : p <= H
      . rw [if_pos hpFull]
        nlinarith
      . rw [if_neg hpFull]
        have hNeg := hSigns.2 (le_of_lt (lt_of_not_ge hpFull))
        nlinarith

theorem robin_complete_exponent_proxy_bound
    {H : Real} (hH : 2 <= H) (a : Nat -> Nat) (S : Finset Nat)
    (hPrime : forall p, Membership.mem S p -> Nat.Prime p)
    (hContains : forall p, Membership.mem (Nat.primesLE (Nat.floor H)) p -> Membership.mem S p) :
    Finset.sum S (fun p => (if (a p) = 0 then 0 else 1 / (p : ℝ) - ((a p) : ℝ) * log p / (H * log H) - ((p : ℝ)⁻¹)^((a p) + 1))) +
        Finset.sum (Nat.primesLE (Nat.floor (H / 2)))
          (fun p => min (Real.log p / (H * Real.log H)) ((Inv.inv (p : Real))^2)) <=
      Finset.sum (Nat.primesLE (Nat.floor H))
        (fun p => 1 / (p : Real) - Real.log p / (H * Real.log H)) := by
  classical
  have hHNonneg : 0 <= H := by linarith
  have hHalfNonneg : 0 <= H / 2 := by linarith
  have hSubset : Nat.primesLE (Nat.floor H) <= S := hContains
  have hHalfSubset : Nat.primesLE (Nat.floor (H / 2)) <= S :=
    (Nat.primesLE_mono (Nat.floor_mono (by linarith : H / 2 <= H))).trans hSubset
  have hSum := Finset.sum_le_sum (s := S) (fun p hp =>
    robin_exponent_proxy_plus_cost_le_benchmark (p := (p : Real)) hH
      (by exact_mod_cast (hPrime p hp).two_le) (a p))
  rw [Finset.sum_add_distrib] at hSum
  have hFilter (y : Real) (hy : 0 <= y)
      (hSub : Nat.primesLE (Nat.floor y) <= S) :
      S.filter (fun p : Nat => (p : Real) <= y) = Nat.primesLE (Nat.floor y) := by
    ext p
    simp only [Finset.mem_filter, Nat.mem_primesLE]
    constructor
    . intro hp
      exact And.intro (Nat.le_floor hp.2) (hPrime p hp.1)
    . intro hp
      exact And.intro (hSub (Nat.mem_primesLE.mpr hp)) ((Nat.le_floor_iff hy).mp hp.1)
  rw [<- Finset.sum_filter, <- Finset.sum_filter,
    hFilter (H / 2) hHalfNonneg hHalfSubset, hFilter H hHNonneg hSubset] at hSum
  exact hSum
theorem one_sub_prime_zpow_neg_pos
    {p : Nat} (hp : 1 < (p : Real)) {j : Nat} (hj : 0 < j) :
    0 < 1 - (p : Real) ^ (-(j : Int)) := by
  have hp_nonneg : 0 <= (p : Real) := le_of_lt (lt_trans zero_lt_one hp)
  have hpow_gt_one : 1 < (p : Real) ^ j := by
    exact (one_lt_pow_iff_of_nonneg hp_nonneg hj.ne').mpr hp
  have hinv_lt_one : ((p : Real) ^ j)⁻¹ < 1 :=
    inv_lt_one_of_one_lt₀ hpow_gt_one
  rw [zpow_neg, zpow_natCast]
  exact sub_pos.mpr hinv_lt_one

theorem primeTowerTopCorrection_zero_sub_eq_log_geom_div_pow
    {p k : Nat} (hp : 1 < (p : Real)) :
    (-Real.log (1 - (p : ℝ) ^ (-(0 + 1 : ℤ)))) - (-Real.log (1 - (p : ℝ) ^ (-(k + 1 : ℤ)))) =
      Real.log
        (((Finset.range (k + 1)).sum (fun i => (p : Real) ^ i)) /
          ((p : Real) ^ k)) := by
  have hA : 0 < 1 - (p : Real) ^ (-(k + 1 : Int)) := by
    simpa using
      one_sub_prime_zpow_neg_pos (p := p) hp (j := k + 1)
        (Nat.succ_pos k)
  have hB : 0 < 1 - (p : Real) ^ (-(1 : Int)) := by
    simpa using
      one_sub_prime_zpow_neg_pos (p := p) hp (j := 1)
        (by norm_num : 0 < 1)
  have hlog :
      (-Real.log (1 - (p : ℝ) ^ (-(0 + 1 : ℤ)))) - (-Real.log (1 - (p : ℝ) ^ (-(k + 1 : ℤ)))) =
        Real.log
          (((1 - (p : Real) ^ (-(k + 1 : Int))) /
            (1 - (p : Real) ^ (-(1 : Int))))) := by
    rw [Real.log_div (ne_of_gt hA) (ne_of_gt hB)]
    ring
  rw [hlog]
  apply congrArg Real.log
  have hp_pos : 0 < (p : Real) := lt_trans zero_lt_one hp
  have hp0 : (p : Real) ≠ 0 := ne_of_gt hp_pos
  have hp1 : (p : Real) ≠ 1 := ne_of_gt hp
  have hz : (p : Real) ^ ((k : Int) + 1) = (p : Real) ^ (k + 1) := by
    simpa using zpow_natCast (p : Real) (k + 1)
  rw [geom_sum_eq hp1]
  rw [zpow_neg, zpow_neg, hz]
  norm_num
  field_simp [hp0, hp1]
  ring

theorem factorization_primeTowerTopCorrection_sum_eq_log_abundancy
    {n : Nat} (hn : n ≠ 0) :
    n.factorization.sum
        (fun p k =>
          (-Real.log (1 - (p : ℝ) ^ (-(0 + 1 : ℤ)))) - (-Real.log (1 - (p : ℝ) ^ (-(k + 1 : ℤ))))) =
      Real.log (((σ 1 n : ℝ) / n)) := by
  classical
  let localGain : Nat → Real := fun p =>
    ((Finset.range (n.factorization p + 1)).sum
        (fun i => (p : Real) ^ i)) /
      ((p : Real) ^ n.factorization p)
  have hsum :
      n.factorization.sum
          (fun p k =>
            (-Real.log (1 - (p : ℝ) ^ (-(0 + 1 : ℤ)))) - (-Real.log (1 - (p : ℝ) ^ (-(k + 1 : ℤ))))) =
        ∑ p ∈ n.factorization.support, Real.log (localGain p) := by
    rw [Finsupp.sum]
    apply Finset.sum_congr rfl
    intro p hp
    have hpPrime : Nat.Prime p :=
      Nat.prime_of_mem_primeFactors (by
        simpa [Nat.support_factorization] using hp)
    have hpReal : 1 < (p : Real) := by exact_mod_cast hpPrime.one_lt
    exact primeTowerTopCorrection_zero_sub_eq_log_geom_div_pow (p := p) (k := n.factorization p) hpReal
  have hlocal_ne :
      ∀ p ∈ n.factorization.support, localGain p ≠ 0 := by
    intro p hp
    have hpPrime : Nat.Prime p :=
      Nat.prime_of_mem_primeFactors (by
        simpa [Nat.support_factorization] using hp)
    have hp_pos : 0 < (p : Real) := by exact_mod_cast hpPrime.pos
    have hden : (p : Real) ^ n.factorization p ≠ 0 :=
      pow_ne_zero _ (ne_of_gt hp_pos)
    have hnum_pos :
        0 <
          (Finset.range (n.factorization p + 1)).sum
            (fun i => (p : Real) ^ i) := by
      refine Finset.sum_pos (fun i _hi => pow_pos hp_pos i) ?_
      exact ⟨0, by simp⟩
    dsimp [localGain]
    exact div_ne_zero (ne_of_gt hnum_pos) hden
  have hprod_log :
      (∑ p ∈ n.factorization.support, Real.log (localGain p)) =
        Real.log (∏ p ∈ n.factorization.support, localGain p) :=
    (Real.log_prod hlocal_ne).symm
  rw [hsum, hprod_log]
  apply congrArg Real.log
  have hsigma :
      (σ 1 n : Real) =
        ∏ p ∈ n.factorization.support,
          (Finset.range (n.factorization p + 1)).sum
            (fun i => (p : Real) ^ i) := by
    have h :=
      ArithmeticFunction.sigma_eq_prod_primeFactors_sum_range_factorization_pow_mul
        (k := 1) (n := n) hn
    rw [h]
    simp [Nat.support_factorization]
  have hnprod :
      (n : Real) =
        ∏ p ∈ n.factorization.support,
          (p : Real) ^ n.factorization p := by
    have hNat :
        (∏ p ∈ n.factorization.support, p ^ n.factorization p) = n := by
      simpa [Finsupp.prod] using Nat.prod_factorization_pow_eq_self hn
    exact_mod_cast hNat.symm
  rw [hsigma, hnprod]
  dsimp [localGain]
  rw [Finset.prod_div_distrib]

theorem robin_prime_factor_gain_le {p : Nat} (hp : Nat.Prime p) (a : Nat) :
    (-Real.log (1 - (p : ℝ) ^ (-(0 + 1 : ℤ)))) - (-Real.log (1 - (p : ℝ) ^ (-(a + 1 : ℤ)))) <=
      1 / (p : Real) - (Inv.inv (p : Real))^(a + 1) - (log (1 - 1 / (p : ℝ)) + 1 / (p : ℝ)) := by
  have hpOne : (1 : Real) < p := by exact_mod_cast hp.one_lt
  have hPow : (p : Real)^(-(a + 1 : Int)) = (Inv.inv (p : Real))^(a + 1) := by
    rw [zpow_neg, show (a : Int) + 1 = ((a + 1 : Nat) : Int) by omega,
      zpow_natCast, <- inv_pow]
  have hNext : 0 < 1 - (Inv.inv (p : Real))^(a + 1) := by
    rw [<- hPow]
    exact one_sub_prime_zpow_neg_pos hpOne (by omega : 0 < a + 1)
  have hLog := Real.log_le_sub_one_of_pos hNext
  have hTop : (-Real.log (1 - (p : ℝ) ^ (-(a + 1 : ℤ)))) = -Real.log (1 - (Inv.inv (p : Real))^(a + 1)) := by
    rw [hPow]
  have hZero : (-Real.log (1 - (p : ℝ) ^ (-(0 + 1 : ℤ)))) = -Real.log (1 - 1 / (p : Real)) := by
    norm_num [one_div]
  rw [hZero, hTop]
  linarith

theorem robin_log_abundancy_le_actual_proxy {n : Nat} (hn : Not (n = 0)) (H : Real) :
    Real.log (((σ 1 n : ℝ) / n)) <= (∑ p ∈ n.factorization.support, -(log (1 - 1 / (p : ℝ)) + 1 / (p : ℝ))) +
      Finset.sum n.factorization.support (fun p => (if (n.factorization p) = 0 then 0 else 1 / (p : ℝ) - ((n.factorization p) : ℝ) * log p / (H * log H) - ((p : ℝ)⁻¹)^((n.factorization p) + 1))) +
        Real.log (n : Real) / (H * Real.log H) := by
  classical
  have hPrime (p : Nat) (hp : Membership.mem n.factorization.support p) : Nat.Prime p :=
    Nat.prime_of_mem_primeFactors (by simpa only [Nat.support_factorization] using hp)
  have hGain := Finset.sum_le_sum (s := n.factorization.support)
    (fun p hp => robin_prime_factor_gain_le (hPrime p hp) (n.factorization p))
  have hGainEq := factorization_primeTowerTopCorrection_sum_eq_log_abundancy hn
  rw [Finsupp.sum] at hGainEq
  rw [hGainEq, Finset.sum_sub_distrib] at hGain
  rw [Finset.sum_neg_distrib]
  have hHeight : Finset.sum n.factorization.support
      (fun p => (n.factorization p : Real) * Real.log p / (H * Real.log H)) =
        Real.log (n : Real) / (H * Real.log H) := by
    rw [<- Finset.sum_div, Real.log_nat_eq_sum_factorization, Finsupp.sum]
  have hProxy : Finset.sum n.factorization.support (fun p => (if (n.factorization p) = 0 then 0 else 1 / (p : ℝ) - ((n.factorization p) : ℝ) * log p / (H * log H) - ((p : ℝ)⁻¹)^((n.factorization p) + 1))) =
      Finset.sum n.factorization.support (fun p => 1 / (p : Real) - (Inv.inv (p : Real))^(n.factorization p + 1)) -
        Real.log (n : Real) / (H * Real.log H) := by
    rw [<- hHeight, <- Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro p hp
    have hNe : Not (n.factorization p = 0) := Finsupp.mem_support_iff.mp hp
    rw [if_neg hNe]
    ring
  linarith

theorem main : H1 → H2 → OMA.R_RiemannHypothesis_robin_criterion_R1_H1_R1.H2 := by
  intro upper lower rh n hn h
  let H := log (n : ℝ)
  have hh : 2 ≤ H := by
    have := Real.add_one_le_exp (30 : ℝ)
    dsimp [H]
    linarith
  let S := n.factorization.support ∪ Nat.primesLE ⌊H⌋₊
  have primes (p : ℕ) (hp : p ∈ n.factorization.support) : p.Prime :=
    Nat.prime_of_mem_primeFactors (by simpa only [Nat.support_factorization] using hp)
  have sp (p : ℕ) (hp : p ∈ S) : p.Prime := by
    rcases Finset.mem_union.mp hp with h | h
    · exact primes p h
    · exact Nat.prime_of_mem_primesLE h
  have inc : n.factorization.support ⊆ S := Finset.subset_union_left
  have hproxy := robin_complete_exponent_proxy_bound hh n.factorization S sp
    (fun _ => Finset.mem_union_right _)
  have heq : (∑ p ∈ n.factorization.support, (if (n.factorization p) = 0 then 0 else 1 / (p : ℝ) - ((n.factorization p) : ℝ) * log p / (H * log H) - ((p : ℝ)⁻¹)^((n.factorization p) + 1))) = ∑ p ∈ S, (if (n.factorization p) = 0 then 0 else 1 / (p : ℝ) - ((n.factorization p) : ℝ) * log p / (H * log H) - ((p : ℝ)⁻¹)^((n.factorization p) + 1)) := by
    apply Finset.sum_subset inc
    intro p _ hp
    rw [Finsupp.notMem_support_iff.mp hp, if_pos rfl]
  rw [← heq] at hproxy
  have ha := robin_log_abundancy_le_actual_proxy (n := n) (by omega) H
  have hm := upper rh H h _ primes
  have hc := lower rh H h
  change log ((σ 1 n : ℝ)/n) < eulerMascheroniConstant + log (log H)
  change _ ≤ _ + _ + H / (H * log H) at ha
  linarith only [ha, hproxy, hm, hc]

end OMA.R_RiemannHypothesis_robin_criterion_R1_H1_R1_H2_R1
