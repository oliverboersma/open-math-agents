import OMAStatements.S_oeis_a263245

-- Problem: A263245: Decimal representation of the n-th iteration of the Rule 155 elementary cellular automaton starting with a single ON (black) cell
-- Upstream: formal-conjectures statements/oeis-a263245.lean:0 (declaration OMA.S_oeis_a263245.main)
-- Credit: @marcelopierry (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace OMA.Proof_oeis_a263245

open OMA.S_oeis_a263245
open PowerSeries

private lemma ruleOut_155 (l c r : Bool) :
    ruleOut 155 l c r =
      match l, c, r with
      | false, false, false => true
      | false, false, true  => true
      | false, true,  false => false
      | false, true,  true  => true
      | true,  false, false => true
      | true,  false, true  => false
      | true,  true,  false => false
      | true,  true,  true  => true := by
  cases l <;> cases c <;> cases r <;> decide

private lemma cell_155_step_odd (p i : ℤ) :
    ruleOut 155 (decide (i - 1 ≠ p)) (decide (i ≠ p)) (decide (i + 1 ≠ p)) =
      decide (i ≠ p - 1 ∧ i ≠ p) := by
  by_cases h1 : i = p - 1
  · rw [h1]
    have ha : p - 1 - 1 ≠ p := by omega
    have hb : p - 1 ≠ p := by omega
    have hc : p - 1 + 1 = p := by omega
    simp [ruleOut_155, ha, hb, hc]
  · by_cases h2 : i = p
    · rw [h2]
      have ha : p - 1 ≠ p := by omega
      have hc : p + 1 ≠ p := by omega
      simp [ruleOut_155, ha, hc]
    · by_cases h3 : i = p + 1
      · rw [h3]
        have ha : p + 1 - 1 = p := by omega
        have hb : p + 1 ≠ p := by omega
        have hc : p + 1 + 1 ≠ p := by omega
        have hd : p + 1 ≠ p - 1 := by omega
        simp [ruleOut_155, ha, hb, hc, hd]
      · have ha : i - 1 ≠ p := by omega
        have hc : i + 1 ≠ p := by omega
        simp [ruleOut_155, ha, h2, hc, h1]

private lemma cell_155_step_even (p i : ℤ) :
    ruleOut 155 (decide (i - 1 ≠ p ∧ i - 1 ≠ p + 1))
      (decide (i ≠ p ∧ i ≠ p + 1))
      (decide (i + 1 ≠ p ∧ i + 1 ≠ p + 1)) =
      decide (i ≠ p - 1) := by
  by_cases h1 : i = p - 1
  · rw [h1]
    have ha1 : p - 1 - 1 ≠ p := by omega
    have ha2 : p - 1 - 1 ≠ p + 1 := by omega
    have hb1 : p - 1 ≠ p := by omega
    have hb2 : p - 1 ≠ p + 1 := by omega
    have hc1 : p - 1 + 1 = p := by omega
    simp [ruleOut_155, ha1, ha2, hb1, hb2, hc1]
  · by_cases h2 : i = p
    · rw [h2]
      have ha1 : p - 1 ≠ p := by omega
      have ha2 : p - 1 ≠ p + 1 := by omega
      have hd : p ≠ p - 1 := by omega
      simp [ruleOut_155, ha1, ha2, hd]
    · by_cases h3 : i = p + 1
      · rw [h3]
        have ha1 : p + 1 - 1 = p := by omega
        have hc1 : p + 1 + 1 ≠ p := by omega
        have hc2 : p + 1 + 1 ≠ p + 1 := by omega
        have hd : p + 1 ≠ p - 1 := by omega
        simp [ruleOut_155, ha1, hc1, hc2, hd]
      · by_cases h4 : i = p + 2
        · rw [h4]
          have ha2 : p + 2 - 1 = p + 1 := by omega
          have hb1 : p + 2 ≠ p := by omega
          have hb2 : p + 2 ≠ p + 1 := by omega
          have hc1 : p + 2 + 1 ≠ p := by omega
          have hc2 : p + 2 + 1 ≠ p + 1 := by omega
          have hd : p + 2 ≠ p - 1 := by omega
          simp [ruleOut_155, ha2, hb1, hb2, hc1, hc2, hd]
        · have ha1 : i - 1 ≠ p := by omega
          have ha2 : i - 1 ≠ p + 1 := by omega
          have hc1 : i + 1 ≠ p := by omega
          have hc2 : i + 1 ≠ p + 1 := by omega
          simp [ruleOut_155, ha1, ha2, h2, h3, hc1, hc2, h1]

private lemma cell_155_formula :
    ∀ t : ℕ, 1 ≤ t → ∀ i : ℤ,
      cell 155 t i =
        if Odd t then decide (i ≠ 1 - (t : ℤ))
        else decide (i ≠ 1 - (t : ℤ) ∧ i ≠ 2 - (t : ℤ)) := by
  intro t ht
  induction t with
  | zero => omega
  | succ t ih =>
    cases t with
    | zero =>
      intro i
      change ruleOut 155 (decide (i - 1 = 0)) (decide (i = 0)) (decide (i + 1 = 0)) =
        if Odd (1 : ℕ) then decide (i ≠ 1 - ((1 : ℕ) : ℤ))
        else decide (i ≠ 1 - ((1 : ℕ) : ℤ) ∧ i ≠ 2 - ((1 : ℕ) : ℤ))
      simp only [Nat.cast_one, sub_self, show Odd (1 : ℕ) from ⟨0, rfl⟩, ite_true]
      by_cases h0 : i = 0
      · rw [h0]; simp [ruleOut_155]
      · by_cases hm : i = -1
        · rw [hm]; simp [ruleOut_155]
        · by_cases hp : i = 1
          · rw [hp]; simp [ruleOut_155]
          · have h1 : i - 1 ≠ 0 := by omega
            have h2 : i + 1 ≠ 0 := by omega
            simp [ruleOut_155, h0, h1, h2]
    | succ t =>
      have hprev := ih (by omega)
      intro i
      change ruleOut 155 (cell 155 (t + 1) (i - 1)) (cell 155 (t + 1) i)
          (cell 155 (t + 1) (i + 1)) = _
      rw [hprev, hprev, hprev]
      by_cases hodd : Odd (t + 1)
      · have hnot : ¬ Odd (t + 2) := by
          obtain ⟨k, hk⟩ := hodd
          intro ⟨m, hm⟩
          omega
        simp only [hodd, hnot, ite_true, ite_false]
        rw [cell_155_step_odd (1 - ((t + 1 : ℕ) : ℤ)) i]
        have hp1 : 1 - ((t + 1 : ℕ) : ℤ) - 1 = 1 - ((t + 2 : ℕ) : ℤ) := by push_cast; omega
        have hp2 : 1 - ((t + 1 : ℕ) : ℤ) = 2 - ((t + 2 : ℕ) : ℤ) := by push_cast; omega
        rw [hp1, hp2]
      · have hodd2 : Odd (t + 2) := by
          rcases Nat.even_or_odd (t + 1) with ⟨k, hk⟩ | h
          · exact ⟨k, by omega⟩
          · exact (hodd h).elim
        simp only [hodd, hodd2, ite_true, ite_false]
        have hp2 : 2 - ((t + 1 : ℕ) : ℤ) = (1 - ((t + 1 : ℕ) : ℤ)) + 1 := by omega
        rw [hp2, cell_155_step_even (1 - ((t + 1 : ℕ) : ℤ)) i]
        have hp1 : 1 - ((t + 1 : ℕ) : ℤ) - 1 = 1 - ((t + 2 : ℕ) : ℤ) := by push_cast; omega
        rw [hp1]

private lemma sum_two_pow_rev (m : ℕ) :
    ∑ j ∈ Finset.range (m + 1), (2 : ℤ) ^ (m - j) = 2 ^ (m + 1) - 1 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ]
    have hsplit :
        ∑ j ∈ Finset.range (m + 1), (2 : ℤ) ^ (m + 1 - j) =
          2 * ∑ j ∈ Finset.range (m + 1), (2 : ℤ) ^ (m - j) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j hj => ?_
      have hjm : j ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      rw [show m + 1 - j = (m - j) + 1 by omega, pow_succ']
    rw [hsplit, ih, Nat.sub_self, pow_zero]
    ring

private lemma a_zero : a 0 = 1 := by
  simp [a, cell]

private lemma a_odd (n : ℕ) (hn : Odd n) : a n = 3 * 2 ^ (2 * n - 1) - 1 := by
  have h1 : 1 ≤ n := by obtain ⟨k, rfl⟩ := hn; omega
  have hsum : a n = ∑ j ∈ Finset.range (2 * n + 1),
      ((2 : ℤ) ^ (2 * n - j) - if j = 1 then (2 : ℤ) ^ (2 * n - j) else 0) := by
    unfold a
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [cell_155_formula n h1 ((j : ℤ) - n), if_pos hn]
    by_cases hj : j = 1
    · subst hj
      simp
    · have hne : (j : ℤ) - (n : ℤ) ≠ 1 - (n : ℤ) := by omega
      simp [hj, hne]
  rw [hsum, Finset.sum_sub_distrib, sum_two_pow_rev (2 * n)]
  have hmem : 1 ∈ Finset.range (2 * n + 1) := Finset.mem_range.mpr (by omega)
  rw [Finset.sum_ite_eq' (Finset.range (2 * n + 1)) 1 (fun j => (2 : ℤ) ^ (2 * n - j)),
    if_pos hmem]
  have hpow : (2 : ℤ) ^ (2 * n + 1) = 4 * (2 : ℤ) ^ (2 * n - 1) := by
    rw [show 2 * n + 1 = (2 * n - 1) + 2 by omega, pow_add]
    ring
  linarith

private lemma a_even (n : ℕ) (h0 : 0 < n) (hn : Even n) : a n = 5 * 2 ^ (2 * n - 2) - 1 := by
  have h2 : 2 ≤ n := by obtain ⟨k, rfl⟩ := hn; omega
  have hnot : ¬ Odd n := Nat.not_odd_iff_even.mpr hn
  have hsum : a n = ∑ j ∈ Finset.range (2 * n + 1),
      ((2 : ℤ) ^ (2 * n - j) - (if j = 1 then (2 : ℤ) ^ (2 * n - j) else 0) -
        (if j = 2 then (2 : ℤ) ^ (2 * n - j) else 0)) := by
    unfold a
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [cell_155_formula n (by omega) ((j : ℤ) - n), if_neg hnot]
    by_cases hj1 : j = 1
    · subst hj1
      simp
    · by_cases hj2 : j = 2
      · subst hj2
        simp
      · have hne1 : (j : ℤ) - (n : ℤ) ≠ 1 - (n : ℤ) := by omega
        have hne2 : (j : ℤ) - (n : ℤ) ≠ 2 - (n : ℤ) := by omega
        simp [hj1, hj2, hne1, hne2]
  rw [hsum, Finset.sum_sub_distrib, Finset.sum_sub_distrib, sum_two_pow_rev (2 * n)]
  have hmem1 : 1 ∈ Finset.range (2 * n + 1) := Finset.mem_range.mpr (by omega)
  have hmem2 : 2 ∈ Finset.range (2 * n + 1) := Finset.mem_range.mpr (by omega)
  rw [Finset.sum_ite_eq' (Finset.range (2 * n + 1)) 1 (fun j => (2 : ℤ) ^ (2 * n - j)),
    if_pos hmem1,
    Finset.sum_ite_eq' (Finset.range (2 * n + 1)) 2 (fun j => (2 : ℤ) ^ (2 * n - j)),
    if_pos hmem2]
  have hp1 : (2 : ℤ) ^ (2 * n + 1) = 8 * (2 : ℤ) ^ (2 * n - 2) := by
    rw [show 2 * n + 1 = (2 * n - 2) + 3 by omega, pow_add]
    ring
  have hp2 : (2 : ℤ) ^ (2 * n - 1) = 2 * (2 : ℤ) ^ (2 * n - 2) := by
    rw [show 2 * n - 1 = (2 * n - 2) + 1 by omega, pow_succ]
    ring
  linarith

private lemma a_step2 (m : ℕ) (hm : 1 ≤ m) : a (m + 2) = 16 * a m + 15 := by
  rcases Nat.even_or_odd m with he | ho
  · have he2 : Even (m + 2) := by obtain ⟨k, rfl⟩ := he; exact ⟨k + 1, by omega⟩
    rw [a_even (m + 2) (by omega) he2, a_even m (by omega) he]
    have hp : (2 : ℤ) ^ (2 * (m + 2) - 2) = 16 * (2 : ℤ) ^ (2 * m - 2) := by
      rw [show 2 * (m + 2) - 2 = (2 * m - 2) + 4 by omega, pow_add]
      ring
    linarith
  · have ho2 : Odd (m + 2) := by obtain ⟨k, rfl⟩ := ho; exact ⟨k + 1, by omega⟩
    rw [a_odd (m + 2) ho2, a_odd m ho]
    have hp : (2 : ℤ) ^ (2 * (m + 2) - 1) = 16 * (2 : ℤ) ^ (2 * m - 1) := by
      rw [show 2 * (m + 2) - 1 = (2 * m - 1) + 4 by omega, pow_add]
      ring
    linarith

private lemma a_rec : ∀ n > 3, a n = a (n - 1) + 16 * a (n - 2) - 16 * a (n - 3) := by
  intro n hn
  have h1 := a_step2 (n - 2) (by omega)
  have h2 := a_step2 (n - 3) (by omega)
  rw [show n - 2 + 2 = n by omega] at h1
  rw [show n - 3 + 2 = n - 1 by omega] at h2
  linarith

private lemma a_one : a 1 = 5 := by
  rw [a_odd 1 ⟨0, rfl⟩]; norm_num

private lemma a_two : a 2 = 19 := by
  rw [a_even 2 (by omega) ⟨1, rfl⟩]; norm_num

private lemma a_three : a 3 = 95 := by
  rw [a_odd 3 ⟨1, rfl⟩]; norm_num

private lemma gf_eq :
    PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - X) * (1 - 4 * X) * (1 + 4 * X)) =
      1 + 4 * X - 2 * X ^ 2 + 12 * X ^ 3 := by
  have hfactor : ((1 - X) * (1 - 4 * X) * (1 + 4 * X) : PowerSeries ℚ) =
      1 - X - C (16 : ℚ) * X ^ 2 + C (16 : ℚ) * X ^ 3 := by
    have h16 : C (16 : ℚ) = (16 : PowerSeries ℚ) := map_ofNat C 16
    rw [h16]
    ring
  have hrhs_eq : (1 + 4 * X - 2 * X ^ 2 + 12 * X ^ 3 : PowerSeries ℚ) =
      C (1 : ℚ) + C (4 : ℚ) * X ^ 1 - C (2 : ℚ) * X ^ 2 + C (12 : ℚ) * X ^ 3 := by
    have h1 : C (1 : ℚ) = (1 : PowerSeries ℚ) := map_one C
    have h4 : C (4 : ℚ) = (4 : PowerSeries ℚ) := map_ofNat C 4
    have h2 : C (2 : ℚ) = (2 : PowerSeries ℚ) := map_ofNat C 2
    have h12 : C (12 : ℚ) = (12 : PowerSeries ℚ) := map_ofNat C 12
    rw [h1, h4, h2, h12, pow_one]
  rw [hfactor, hrhs_eq]
  ext n
  have hcoeff_mul :
      PowerSeries.coeff n (PowerSeries.mk (fun k => (a k : ℚ)) *
          (1 - X - C (16 : ℚ) * X ^ 2 + C (16 : ℚ) * X ^ 3)) =
        (a n : ℚ)
        - (if 1 ≤ n then (a (n - 1) : ℚ) else 0)
        - 16 * (if 2 ≤ n then (a (n - 2) : ℚ) else 0)
        + 16 * (if 3 ≤ n then (a (n - 3) : ℚ) else 0) := by
    have hdistrib :
        PowerSeries.mk (fun k => (a k : ℚ)) *
            (1 - X - C (16 : ℚ) * X ^ 2 + C (16 : ℚ) * X ^ 3) =
          PowerSeries.mk (fun k => (a k : ℚ))
          - PowerSeries.mk (fun k => (a k : ℚ)) * X
          - C (16 : ℚ) * (PowerSeries.mk (fun k => (a k : ℚ)) * X ^ 2)
          + C (16 : ℚ) * (PowerSeries.mk (fun k => (a k : ℚ)) * X ^ 3) := by
      ring
    rw [hdistrib]
    simp only [map_add, map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_mk]
    have h1 : PowerSeries.coeff n (PowerSeries.mk (fun k => (a k : ℚ)) * X) =
        if 1 ≤ n then (a (n - 1) : ℚ) else 0 := by
      cases n with
      | zero => simp
      | succ m => simp [PowerSeries.coeff_succ_mul_X]
    have h2 : PowerSeries.coeff n (PowerSeries.mk (fun k => (a k : ℚ)) * X ^ 2) =
        if 2 ≤ n then (a (n - 2) : ℚ) else 0 := by
      rw [PowerSeries.coeff_mul_X_pow']
      simp
    have h3 : PowerSeries.coeff n (PowerSeries.mk (fun k => (a k : ℚ)) * X ^ 3) =
        if 3 ≤ n then (a (n - 3) : ℚ) else 0 := by
      rw [PowerSeries.coeff_mul_X_pow']
      simp
    rw [h1, h2, h3]
  have hcoeff_rhs :
      PowerSeries.coeff n (C (1 : ℚ) + C (4 : ℚ) * X ^ 1 - C (2 : ℚ) * X ^ 2 + C (12 : ℚ) * X ^ 3) =
        (if n = 0 then (1 : ℚ) else 0)
        + (if n = 1 then (4 : ℚ) else 0)
        - (if n = 2 then (2 : ℚ) else 0)
        + (if n = 3 then (12 : ℚ) else 0) := by
    simp only [map_add, map_sub, PowerSeries.coeff_C, PowerSeries.coeff_C_mul_X_pow]
  rw [hcoeff_mul, hcoeff_rhs]
  rcases n with _ | _ | _ | _ | n
  · simp [a_zero]
  · simp [a_one, a_zero]; norm_num
  · simp [a_two, a_one, a_zero]; norm_num
  · simp [a_three, a_two, a_one, a_zero]; norm_num
  · have hr := a_rec (n + 4) (by omega)
    have hrq : (a (n + 4) : ℚ) =
        (a (n + 3) : ℚ) + 16 * (a (n + 2) : ℚ) - 16 * (a (n + 1) : ℚ) := by
      exact_mod_cast hr
    simp only [show 1 ≤ n + 4 by omega, show 2 ≤ n + 4 by omega, show 3 ≤ n + 4 by omega,
      ite_true, show n + 4 - 1 = n + 3 by omega, show n + 4 - 2 = n + 2 by omega,
      show n + 4 - 3 = n + 1 by omega, show n + 4 ≠ 0 by omega, show n + 4 ≠ 1 by omega,
      show n + 4 ≠ 2 by omega, show n + 4 ≠ 3 by omega, ite_false]
    linarith

private lemma a_odd_rat (n : ℕ) (hn : Odd n) :
    (a n : ℚ) = (3 * (4 : ℚ) ^ (((n : ℤ) - 1) / 2) * (2 : ℚ) ^ (n : ℤ) - 1 : ℚ) := by
  obtain ⟨k, rfl⟩ := hn
  rw [a_odd (2 * k + 1) ⟨k, rfl⟩]
  have hdiv : (((2 * k + 1 : ℕ) : ℤ) - 1) / 2 = (k : ℤ) := by omega
  rw [hdiv]
  simp only [zpow_natCast]
  push_cast
  have h4 : (4 : ℚ) ^ k = (2 : ℚ) ^ (2 * k) := by
    rw [pow_mul]
    norm_num
  rw [h4, show 2 * (2 * k + 1) - 1 = 2 * k + (2 * k + 1) by omega, pow_add]
  ring

private lemma a_even_rat (n : ℕ) (h0 : 0 < n) (hn : Even n) :
    (a n : ℚ) = (5 * (4 : ℚ) ^ ((n : ℤ) / 2 - 1) * (2 : ℚ) ^ (n : ℤ) - 1 : ℚ) := by
  obtain ⟨k, hk⟩ := hn
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  have hneq : n = 2 * m + 2 := by omega
  subst hneq
  rw [a_even (2 * m + 2) (by omega) ⟨m + 1, by omega⟩]
  have hdiv : ((2 * m + 2 : ℕ) : ℤ) / 2 - 1 = (m : ℤ) := by omega
  rw [hdiv]
  simp only [zpow_natCast]
  push_cast
  have h4 : (4 : ℚ) ^ m = (2 : ℚ) ^ (2 * m) := by
    rw [pow_mul]
    norm_num
  rw [h4, show 2 * (2 * m + 2) - 2 = 2 * m + (2 * m + 2) by omega, pow_add]
  ring

end OMA.Proof_oeis_a263245

theorem OMA.solution : type_of% @OMA.S_oeis_a263245.main := by
  exact ⟨OMA.Proof_oeis_a263245.a_rec,
    OMA.Proof_oeis_a263245.gf_eq,
    OMA.Proof_oeis_a263245.a_odd_rat,
    OMA.Proof_oeis_a263245.a_even_rat⟩
