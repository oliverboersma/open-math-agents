import OMAStatements.S_oeis_a265427

namespace R188
open OMA.S_oeis_a265427

def G (t : ℕ) (i : ℤ) : Bool := decide (0 ≤ i ∧ i ≤ t ∧ (i = 0 ∨ (i + t) % 4 ≠ 3))

theorem rule188 (l c r : Bool) :
    ruleOut 188 l c r = ((l && !c) || (!l && c) || (l && c && r)) := by
  cases l <;> cases c <;> cases r <;> decide

theorem step (t : ℕ) (i : ℤ) :
    ruleOut 188 (G t (i - 1)) (G t i) (G t (i + 1)) = G (t + 1) i := by
  rw [rule188]
  simp only [G]
  push_cast
  rw [Bool.eq_iff_iff]
  simp only [Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq,
    decide_eq_false_iff_not]
  omega

theorem cell_eq (t : ℕ) (i : ℤ) : cell 188 t i = G t i := by
  induction t generalizing i with
  | zero =>
    show decide (i = 0) = _
    simp only [G]
    rw [Bool.eq_iff_iff]
    simp only [decide_eq_true_eq]
    push_cast
    omega
  | succ t ih =>
    show ruleOut 188 (cell 188 t (i - 1)) (cell 188 t i) (cell 188 t (i + 1)) = _
    rw [ih, ih, ih, step]

def B (n : ℕ) : ℤ :=
  ∑ d ∈ Finset.range (n + 1), if (d = n ∨ (2 * n - d) % 4 ≠ 3) then (10 : ℤ) ^ d else 0

theorem a_eq_B (n : ℕ) : a n = B n := by
  let f : ℕ → ℤ := fun d => if (d ≤ n ∧ (d = n ∨ (2 * n - d) % 4 ≠ 3)) then (10 : ℤ) ^ d else 0
  have h1 : a n = ∑ j ∈ Finset.range (2 * n + 1), f (2 * n + 1 - 1 - j) := by
    unfold a
    refine Finset.sum_congr rfl (fun j hj => ?_)
    rw [Finset.mem_range] at hj
    rw [cell_eq]
    simp only [G, f, show 2 * n + 1 - 1 - j = 2 * n - j by omega, decide_eq_true_eq]
    split_ifs <;> first | rfl | (exfalso; omega)
  rw [h1, Finset.sum_range_reflect f (2 * n + 1), show 2 * n + 1 = (n + 1) + n by ring,
    Finset.sum_range_add]
  have h2 : ∑ x ∈ Finset.range n, f (n + 1 + x) = 0 := by
    refine Finset.sum_eq_zero (fun x _ => ?_)
    simp only [f]
    rw [if_neg (by omega)]
  rw [h2, add_zero]
  unfold B
  refine Finset.sum_congr rfl (fun d hd => ?_)
  rw [Finset.mem_range] at hd
  simp only [f]
  by_cases hc : (d = n ∨ (2 * n - d) % 4 ≠ 3)
  · rw [if_pos ⟨by omega, hc⟩, if_pos hc]
  · rw [if_neg (by omega), if_neg hc]

def P : ℕ → ℤ
  | 0 => 11100
  | 1 => 11010
  | 2 => 10110
  | _ => 11109

def Q : ℕ → ℤ
  | 0 => -1101
  | 1 => -111
  | 2 => -1101
  | _ => -111

theorem B_step (m : ℕ) : B (m + 4) = B m + P (m % 4) * 10 ^ m := by
  have hC : ∀ d ∈ Finset.range m,
      (if (d = m + 4 ∨ (2 * (m + 4) - d) % 4 ≠ 3) then (10 : ℤ) ^ d else 0) =
      (if (2 * m - d) % 4 ≠ 3 then (10 : ℤ) ^ d else 0) := by
    intro d hd
    rw [Finset.mem_range] at hd
    by_cases hc : (2 * m - d) % 4 ≠ 3
    · rw [if_pos (by omega), if_pos hc]
    · rw [if_neg (by omega), if_neg hc]
  have hC' : ∀ d ∈ Finset.range m,
      (if (d = m ∨ (2 * m - d) % 4 ≠ 3) then (10 : ℤ) ^ d else 0) =
      (if (2 * m - d) % 4 ≠ 3 then (10 : ℤ) ^ d else 0) := by
    intro d hd
    rw [Finset.mem_range] at hd
    by_cases hc : (2 * m - d) % 4 ≠ 3
    · rw [if_pos (by omega), if_pos hc]
    · rw [if_neg (by omega), if_neg hc]
  unfold B
  rw [show m + 4 + 1 = m + 1 + 1 + 1 + 1 + 1 by ring]
  simp only [Finset.sum_range_succ]
  rw [Finset.sum_congr rfl hC, Finset.sum_congr rfl hC']
  simp only [true_or, if_true]
  have h4 : m % 4 < 4 := Nat.mod_lt _ (by norm_num)
  rcases (by omega : m % 4 = 0 ∨ m % 4 = 1 ∨ m % 4 = 2 ∨ m % 4 = 3) with h | h | h | h
  all_goals
    rw [h]
    split_ifs <;> first | (exfalso; omega) | (simp only [P]; ring)

theorem B_closed (n : ℕ) : 9999 * B n = P (n % 4) * 10 ^ n + Q (n % 4) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases (by omega : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ 4 ≤ n) with h | h | h | h | h
    · subst h; decide
    · subst h; decide
    · subst h; decide
    · subst h; decide
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
      rw [B_step, mul_add, ih m (by omega), show (m + 4) % 4 = m % 4 by omega]
      ring

theorem a_closed (n : ℕ) : 9999 * a n = P (n % 4) * 10 ^ n + Q (n % 4) := by
  rw [a_eq_B]; exact B_closed n

theorem recur (m : ℕ) : a (m + 6) = a (m + 4) + 10000 * a (m + 2) - 10000 * a m := by
  have h6 := a_closed (m + 6)
  have h4 := a_closed (m + 4)
  have h2 := a_closed (m + 2)
  have h0 := a_closed m
  rw [show (m + 6) % 4 = (m + 2) % 4 by omega] at h6
  rw [show (m + 4) % 4 = m % 4 by omega] at h4
  have hQ : Q ((m + 2) % 4) = Q (m % 4) := by
    rw [show (m + 2) % 4 = (m % 4 + 2) % 4 by omega]
    rcases (by omega : m % 4 = 0 ∨ m % 4 = 1 ∨ m % 4 = 2 ∨ m % 4 = 3) with h | h | h | h <;>
      rw [h] <;> rfl
  apply mul_left_cancel₀ (show (9999 : ℤ) ≠ 0 by norm_num)
  linear_combination h6 - h4 - 10000 * h2 + 10000 * h0 + (1 - 10000) * hQ

theorem pow_mod (k : ℕ) : ∃ q : ℤ, (10000 : ℤ) ^ k = 9999 * q + 1 := by
  induction k with
  | zero => exact ⟨0, by norm_num⟩
  | succ k ih =>
    obtain ⟨q, hq⟩ := ih
    exact ⟨10000 * q + 1, by rw [pow_succ, hq]; ring⟩

theorem fl (x : ℚ) (z : ℤ) (R : ℚ) (h : x = z + R / 9999) (h0 : 0 ≤ R) (h1 : R < 9999) :
    ⌊x⌋ = z := by
  rw [Int.floor_eq_iff, h]
  constructor
  · have : 0 ≤ R / 9999 := div_nonneg h0 (by norm_num)
    linarith
  · have : R / 9999 < 1 := by rw [div_lt_one (by norm_num)]; exact h1
    linarith

theorem floor_part (k r : ℕ) (F1 R1 F2 R2 : ℤ)
    (hA : 9999 * a (4 * k + r) = (9999 + R1) * 10 ^ (4 * k + r) - R2)
    (hF1 : 11100 * 10 ^ r = 9999 * F1 + R1) (hR1 : 0 ≤ R1 ∧ R1 < 9999)
    (hF2 : 11100 * 10 ^ (2 * r) = 9999 * F2 + R2) (hR2 : 0 ≤ R2 ∧ R2 < 9999) :
    (a (4 * k + r) : ℚ) = (((⌊(11100 * (100 : ℚ) ^ ((4 * k + r : ℕ) : ℤ) / 9999 : ℚ)⌋ : ℤ) : ℚ)
      + (10 : ℚ) ^ ((4 * k + r : ℕ) : ℤ)
      - ((⌊(11100 * (10 : ℚ) ^ ((4 * k + r : ℕ) : ℤ) / 9999 : ℚ)⌋ : ℤ) : ℚ)
        * (10 : ℚ) ^ ((4 * k + r : ℕ) : ℤ) : ℚ) := by
  obtain ⟨q, hq⟩ := pow_mod k
  have hX : (10 : ℚ) ^ (4 * k + r) = 10 ^ r * (9999 * q + 1) := by
    rw [pow_add, pow_mul, mul_comm]
    congr 1
    have := congrArg (fun z : ℤ => (z : ℚ)) hq
    push_cast at this
    rw [← this]
    norm_num
  have hF1q : (11100 * 10 ^ r : ℚ) = 9999 * F1 + R1 := by exact_mod_cast hF1
  have hF2q : (11100 * 10 ^ (2 * r) : ℚ) = 9999 * F2 + R2 := by exact_mod_cast hF2
  have hAq : (9999 * a (4 * k + r) : ℚ) = (9999 + R1) * 10 ^ (4 * k + r) - R2 := by
    exact_mod_cast congrArg (fun z : ℤ => (z : ℚ)) hA
  simp only [zpow_natCast]
  have e2 : (100 : ℚ) ^ (4 * k + r) = 10 ^ (2 * r) * (9999 * (9999 * q ^ 2 + 2 * q) + 1) := by
    have : (100 : ℚ) ^ (4 * k + r) = ((10 : ℚ) ^ (4 * k + r)) ^ 2 := by
      rw [show (100 : ℚ) = 10 ^ 2 by norm_num, ← pow_mul, ← pow_mul, Nat.mul_comm 2]
    rw [this, hX]
    ring
  rw [fl (11100 * (100 : ℚ) ^ (4 * k + r) / 9999) (11100 * 10 ^ (2 * r) * (9999 * q ^ 2 + 2 * q) + F2)
      R2 (by rw [e2]; push_cast; linear_combination (1 / 9999) * hF2q)
      (by exact_mod_cast hR2.1) (by exact_mod_cast hR2.2)]
  rw [fl (11100 * (10 : ℚ) ^ (4 * k + r) / 9999) (11100 * 10 ^ r * q + F1) R1
      (by rw [hX]; push_cast; linear_combination (1 / 9999) * hF1q)
      (by exact_mod_cast hR1.1) (by exact_mod_cast hR1.2)]
  push_cast
  rw [hX] at hAq ⊢
  apply mul_left_cancel₀ (show (9999 : ℚ) ≠ 0 by norm_num)
  linear_combination hAq - (10 ^ r * (9999 * q + 1)) * hF1q + hF2q

end R188

open PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a265427.main := by
  open OMA.S_oeis_a265427 R188 in
  refine ⟨?_, ?_, ?_⟩
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 6 := ⟨n - 6, by omega⟩
    rw [show m + 6 - 2 = m + 4 by omega, show m + 6 - 4 = m + 2 by omega,
      show m + 6 - 6 = m by omega]
    exact recur m
  · have v : ∀ n, n < 6 → (a n : ℚ) = [1, 11, 101, 1111, 11101, 110111].getD n 0 := by
      intro n hn
      have h := a_closed n
      interval_cases n <;> norm_num [P, Q] at h ⊢ <;> exact_mod_cast (by omega)
    have v0 := v 0 (by norm_num)
    have v1 := v 1 (by norm_num)
    have v2 := v 2 (by norm_num)
    have v3 := v 3 (by norm_num)
    have v4 := v 4 (by norm_num)
    have v5 := v 5 (by norm_num)
    simp only [List.getD_cons_zero, List.getD_cons_succ] at v0 v1 v2 v3 v4 v5
    rw [show ((1 - X) * (1 + X) * (1 - 10 * X) * (1 + 10 * X) * (1 + 100 * X ^ 2) : PowerSeries ℚ)
        = 1 - X ^ 2 - C 10000 * X ^ 4 + C 10000 * X ^ 6 by simp only [map_ofNat]; ring,
      show (1 + 11 * X + 100 * X ^ 2 + 1100 * X ^ 3 + 1000 * X ^ 4 - 1000 * X ^ 5 : PowerSeries ℚ)
        = 1 + C 11 * X ^ 1 + C 100 * X ^ 2 + C 1100 * X ^ 3 + C 1000 * X ^ 4 - C 1000 * X ^ 5 by
          simp only [map_ofNat]; ring]
    rw [show ∀ p : PowerSeries ℚ, p * (1 - X ^ 2 - C 10000 * X ^ 4 + C 10000 * X ^ 6)
        = p - p * X ^ 2 - C 10000 * (p * X ^ 4) + C 10000 * (p * X ^ 6) from fun p => by ring]
    ext n
    simp only [map_sub, map_add, coeff_C_mul, coeff_mul_X_pow', coeff_one, coeff_mk]
    rcases n with _ | _ | _ | _ | _ | _ | n
    · simp [v0]
    · simp [v1]
    · simp [v0, v2]; norm_num
    · simp [v1, v3]; norm_num
    · simp [v0, v2, v4]; norm_num
    · simp [v1, v3, v5]; norm_num
    · have := recur n
      simp only [show n + 1 + 1 + 1 + 1 + 1 + 1 = n + 6 by ring]
      simp
      rw [this]
      push_cast
      ring
  · intro n
    obtain ⟨k, r, hr, rfl⟩ : ∃ k r, r < 4 ∧ n = 4 * k + r := ⟨n / 4, n % 4, Nat.mod_lt _ (by norm_num), by omega⟩
    have hA := a_closed (4 * k + r)
    rw [show (4 * k + r) % 4 = r by omega] at hA
    interval_cases r
    · exact floor_part k 0 1 1101 1 1101 (by rw [hA]; simp only [P, Q]; ring) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num)
    · exact floor_part k 1 11 1011 111 111 (by rw [hA]; simp only [P, Q]; ring) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num)
    · exact floor_part k 2 111 111 11101 1101 (by rw [hA]; simp only [P, Q]; ring) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num)
    · exact floor_part k 3 1110 1110 1110111 111 (by rw [hA]; simp only [P, Q]; ring) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num)
