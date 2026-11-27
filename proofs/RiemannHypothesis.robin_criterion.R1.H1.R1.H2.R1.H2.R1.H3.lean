import OMAReductions.R_RiemannHypothesis_robin_criterion_R1_H1_R1_H2_R1_H2_R1
import Mathlib

/- Copyright (c) 2026 Jonas Whidden. All rights reserved.
Adapted from PrimeCostLowerBound.lean in kimihiro64/Robin1984 at commit
e3697139babfe0f6cc7a76a08bf41a92aa7a2978 under Apache-2.0. -/
namespace Robin1984

noncomputable section

theorem robin_prime_square_reference_sign {u v : Real} (hu : 1 < u) (hv : 1 < v) :
    And (u <= v -> Real.log u / (v^2 * Real.log v) <= (Inv.inv u)^2)
      (v <= u -> (Inv.inv u)^2 <= Real.log u / (v^2 * Real.log v)) := by
  have huPos : 0 < u := by linarith
  have hvPos : 0 < v := by linarith
  have hLogU := Real.log_pos hu
  have hLogV := Real.log_pos hv
  have hFactor : 0 < u^2 * (v^2 * Real.log v) := by positivity
  have hEq : ((Inv.inv u)^2 - Real.log u / (v^2 * Real.log v)) *
      (u^2 * (v^2 * Real.log v)) = v^2 * Real.log v - u^2 * Real.log u := by
    field_simp
  constructor
  . intro h
    have hLog := Real.log_le_log huPos h
    have hMul : u^2 * Real.log u <= v^2 * Real.log v := by gcongr
    nlinarith
  . intro h
    have hLog := Real.log_le_log hvPos h
    have hMul : v^2 * Real.log v <= u^2 * Real.log u := by gcongr
    nlinarith

theorem robin_minimum_prime_cost_ge_block
    {H s b : Real} (hH : 1 < H) (hs : 1 < s) (hsb : s <= b)
    (hDen : H * Real.log H <= s^2 * Real.log s) :
    Chebyshev.theta s / (s^2 * Real.log s) +
        Finset.sum ((Finset.Ioc (Nat.floor s) (Nat.floor b)).filter Nat.Prime)
          (fun p => (Inv.inv (p : Real))^2) <=
      Finset.sum (Nat.primesLE (Nat.floor b))
        (fun p => min (Real.log p / (H * Real.log H)) ((Inv.inv (p : Real))^2)) := by
  classical
  have hsNonneg : 0 <= s := by linarith
  have hbNonneg : 0 <= b := by linarith
  have hHPos : 0 < H := by linarith
  have hLogH := Real.log_pos hH
  have hSubset : Nat.primesLE (Nat.floor s) <= Nat.primesLE (Nat.floor b) :=
    Nat.primesLE_mono (Nat.floor_mono hsb)
  have hSmall : Chebyshev.theta s / (s^2 * Real.log s) <=
      Finset.sum (Nat.primesLE (Nat.floor s))
        (fun p => min (Real.log p / (H * Real.log H)) ((Inv.inv (p : Real))^2)) := by
    rw [Chebyshev.theta_eq_sum_primesLE, Finset.sum_div]
    apply Finset.sum_le_sum
    intro p hp
    have hpPrime := Nat.prime_of_mem_primesLE hp
    have hpOne : (1 : Real) < p := by exact_mod_cast hpPrime.one_lt
    have hpLe : (p : Real) <= s := (Nat.le_floor_iff hsNonneg).mp (Nat.le_of_mem_primesLE hp)
    have hAlpha : Real.log (p : Real) / (s^2 * Real.log s) <=
        Real.log p / (H * Real.log H) :=
      div_le_div_of_nonneg_left (Real.log_pos hpOne).le (mul_pos hHPos hLogH) hDen
    exact le_min hAlpha ((robin_prime_square_reference_sign hpOne hs).1 hpLe)
  have hLarge :
      Finset.sum ((Finset.Ioc (Nat.floor s) (Nat.floor b)).filter Nat.Prime)
        (fun p => (Inv.inv (p : Real))^2) <=
      Finset.sum ((Finset.Ioc (Nat.floor s) (Nat.floor b)).filter Nat.Prime)
        (fun p => min (Real.log p / (H * Real.log H)) ((Inv.inv (p : Real))^2)) := by
    apply Finset.sum_le_sum
    intro p hp
    have hpPrime := (Finset.mem_filter.mp hp).2
    have hpOne : (1 : Real) < p := by exact_mod_cast hpPrime.one_lt
    have hpGt : Nat.floor s < p := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hp).1).1
    have hpGe : s <= (p : Real) := by
      by_contra h
      have hpLe : p <= Nat.floor s := Nat.le_floor (le_of_lt (lt_of_not_ge h))
      omega
    have hAlpha : Real.log (p : Real) / (s^2 * Real.log s) <=
        Real.log p / (H * Real.log H) :=
      div_le_div_of_nonneg_left (Real.log_pos hpOne).le (mul_pos hHPos hLogH) hDen
    exact le_min (((robin_prime_square_reference_sign hpOne hs).2 hpGe).trans hAlpha) le_rfl
  have hDiff : SDiff.sdiff (Nat.primesLE (Nat.floor b)) (Nat.primesLE (Nat.floor s)) =
      (Finset.Ioc (Nat.floor s) (Nat.floor b)).filter Nat.Prime := by
    ext p
    simp only [Finset.mem_sdiff, Nat.mem_primesLE, Finset.mem_filter, Finset.mem_Ioc]
    constructor
    . intro h
      have hGt : Nat.floor s < p := by
        by_contra hNot
        exact h.2 (And.intro (Nat.le_of_not_gt hNot) h.1.2)
      exact And.intro (And.intro hGt h.1.1) h.1.2
    . intro h
      exact And.intro (And.intro h.1.2 h.2)
        (fun hOther => (Nat.not_lt_of_ge hOther.1) h.1.1)
  have hSum := Finset.sum_sdiff hSubset
    (f := fun p : Nat => min (Real.log p / (H * Real.log H)) ((Inv.inv (p : Real))^2))
  rw [hDiff] at hSum
  linarith

end

end Robin1984

theorem OMA.solution : OMA.R_RiemannHypothesis_robin_criterion_R1_H1_R1_H2_R1_H2_R1.H3 := by
  intro H s b hH hs hsb hden
  exact Robin1984.robin_minimum_prime_cost_ge_block hH hs hsb hden
