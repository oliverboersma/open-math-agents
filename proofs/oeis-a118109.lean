import OMAStatements.S_oeis_a118109

/- OEIS A118109. Colin Barker conjectured the recurrence and generating function.
Karl V. Keller, Jr. conjectured the floor formula. The Lean statement is from
snoozingnewt, project PR 807. Michael De Vlieger illustrated the four-digit
blocks in the OEIS entry.
At even times the light cone consists of isolated ones every four cells.
At odd times the repeating block is 1110, truncated at the light cone. -/

namespace Rule54Rows

open OMA.S_oeis_a118109 Finset

private theorem rule_truth (l c r : Bool) :
    ruleOut 54 l c r = true ↔
      (c = true ∧ l ≠ true ∧ r ≠ true) ∨ (c ≠ true ∧ (l = true ∨ r = true)) := by
  cases l <;> cases c <;> cases r <;> decide

private theorem row (t : ℕ) (i : ℤ) :
    cell 54 t i = true ↔
      -(t : ℤ) ≤ i ∧ i ≤ (t : ℤ) ∧
      ((t % 2 = 0 ∧ (i + t) % 4 = 0) ∨ (t % 2 = 1 ∧ (i + t) % 4 ≠ 3)) := by
  induction t generalizing i with
  | zero =>
    simp [cell]
    omega
  | succ t ih =>
    simp only [cell, rule_truth, ne_eq, ih, Nat.cast_succ]
    have ht : t % 2 = 0 ∨ t % 2 = 1 := by omega
    have hi : (i + (t : ℤ)) % 4 = 0 ∨ (i + t) % 4 = 1 ∨ (i + t) % 4 = 2 ∨ (i + t) % 4 = 3 := by omega
    rcases ht with ht | ht <;> rcases hi with hi | hi | hi | hi <;> omega

private def digit (n j : ℕ) : Prop :=
  (n % 2 = 0 ∧ j % 4 = 0) ∨ (n % 2 = 1 ∧ j % 4 ≠ 3)

private instance (n j : ℕ) : Decidable (digit n j) := by
  unfold digit
  infer_instance

private theorem word (n : ℕ) :
    a n = ∑ j ∈ range (2 * n + 1), if digit n j then (10 : ℤ) ^ (2 * n - j) else 0 := by
  unfold a
  refine sum_congr rfl fun j hj => ?_
  have hj' := mem_range.mp hj
  have iffDigit : cell 54 n ((j : ℤ) - n) = true ↔ digit n j := by
    rw [row]
    unfold digit
    omega
  simp only [iffDigit]

private def suffix (n : ℕ) : ℤ := if n % 2 = 0 then 1 else 111

/-- Advancing two rows appends 0001 at even times and 0111 at odd times. -/
private theorem append_four (n : ℕ) : a (n + 2) = 10000 * a n + suffix n := by
  rw [word, word]
  have len : 2 * (n + 2) + 1 = (2 * n + 1) + 4 := by omega
  rw [len, sum_range_add, mul_sum]
  congr 1
  · refine sum_congr rfl fun j hj => ?_
    have hj' := mem_range.mp hj
    have exp : 2 * (n + 2) - j = (2 * n - j) + 4 := by omega
    have eqd : digit (n + 2) j ↔ digit n j := by
      unfold digit
      omega
    rw [exp, pow_add]
    simp only [eqd]
    split <;> ring
  · simp only [sum_range_succ, sum_range_zero, zero_add]
    rw [show 2 * (n + 2) - (2 * n + 1 + 0) = 3 by omega,
        show 2 * (n + 2) - (2 * n + 1 + 1) = 2 by omega,
        show 2 * (n + 2) - (2 * n + 1 + 2) = 1 by omega,
        show 2 * (n + 2) - (2 * n + 1 + 3) = 0 by omega]
    unfold digit suffix
    split_ifs <;> omega

private theorem suffix_period (n : ℕ) : suffix (n + 2) = suffix n := by
  unfold suffix
  simp

private theorem rec_four (n : ℕ) : a (n + 4) = 10001 * a (n + 2) - 10000 * a n := by
  have h := append_four (n + 2)
  rw [suffix_period] at h
  linarith [append_four n]

private theorem start_zero : a 0 = 1 := by decide
private theorem start_one : a 1 = 111 := by decide

/-- The suffix is also the remainder in the division by 9999. -/
private theorem scaled_word (n : ℕ) :
    9999 * a n + suffix n = (10000 + 1100 * ((n : ℤ) % 2)) * 100 ^ n := by
  induction n using Nat.twoStepInduction with
  | zero =>
    rw [start_zero]
    decide
  | one =>
    rw [start_one]
    decide
  | more n ih _ =>
    rw [append_four, suffix_period, pow_add]
    have hm : ((n + 2 : ℕ) : ℤ) % 2 = (n : ℤ) % 2 := by omega
    rw [hm]
    nlinarith only [ih]

private theorem row_floor (n : ℕ) :
    (a n : ℚ) = ((⌊((10000 + 1100 * (((n : ℤ) % 2 : ℤ) : ℚ)) * (100 : ℚ) ^ (n : ℤ) / 9999 : ℚ)⌋ : ℤ) : ℚ) := by
  have hq := congrArg (fun x : ℤ => (x : ℚ)) (scaled_word n)
  push_cast at hq
  rw [zpow_natCast]
  have hb : 0 ≤ (suffix n : ℚ) ∧ (suffix n : ℚ) < 9999 := by
    unfold suffix
    split <;> norm_num
  have hh : ⌊((10000 + 1100 * (((n : ℤ) % 2 : ℤ) : ℚ)) * (100 : ℚ) ^ n / 9999 : ℚ)⌋ = a n := by
    apply Int.floor_eq_iff.mpr
    constructor <;> linarith
  rw [hh]

open PowerSeries

private theorem series :
    PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - X) * (1 + X) * (1 - 100 * X) * (1 + 100 * X)) = 1 + 111 * X := by
  let F := PowerSeries.mk (fun n => (a n : ℚ))
  change F * _ = _
  have poly : F * ((1 - X) * (1 + X) * (1 - 100 * X) * (1 + 100 * X)) = F - (10001 : ℕ) • (F * X ^ 2) + (10000 : ℕ) • (F * X ^ 4) := by
    simp only [nsmul_eq_mul]
    ring
  rw [poly, show (111 : ℚ⟦X⟧) * X = (111 : ℕ) • X by simp [nsmul_eq_mul]]
  ext n
  simp only [map_add, map_sub, map_nsmul, coeff_one, coeff_X, coeff_mul_X_pow', F, coeff_mk]
  simp only [nsmul_eq_mul]
  have a2 := append_four 0
  have a3 := append_four 1
  rw [start_zero] at a2
  rw [start_one] at a3
  norm_num [suffix] at a2 a3
  by_cases h : n < 4
  · interval_cases n <;> norm_num [start_zero, start_one, a2, a3]
  · have hr := rec_four (n - 4)
    rw [show n - 4 + 4 = n by omega, show n - 4 + 2 = n - 2 by omega] at hr
    simp only [if_pos (show 2 ≤ n by omega), if_pos (show 4 ≤ n by omega),
      if_neg (show n ≠ 0 by omega), if_neg (show n ≠ 1 by omega), mul_zero, add_zero]
    exact_mod_cast (by linarith [hr] : a n - 10001 * a (n - 2) + 10000 * a (n - 4) = 0)

end Rule54Rows

theorem OMA.solution : type_of% @OMA.S_oeis_a118109.main := by
  refine ⟨?_, Rule54Rows.series, Rule54Rows.row_floor⟩
  intro n hn
  have h := Rule54Rows.rec_four (n - 4)
  rwa [show n - 4 + 4 = n by omega, show n - 4 + 2 = n - 2 by omega] at h
