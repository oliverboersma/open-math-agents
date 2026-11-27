import OMAStatements.S_oeis_a265723

-- The state of rule 1 repeats after two steps. Count its cells in each phase
-- and use the resulting recurrence to verify the power-series identity.
-- Proof by @anmolspace. The statement is due to @snoozingnewt.

namespace CellCountProof

open OMA.S_oeis_a265723
open PowerSeries

private theorem new_on (l c r : Bool) : ruleOut 1 l c r = true ↔
    l ≠ true ∧ c ≠ true ∧ r ≠ true := by
  cases l <;> cases c <;> cases r <;> decide

private theorem phases (k : ℕ) : (∀ i, cell 1 (2 * k) i = true ↔ i = 0) ∧
    (∀ i, cell 1 (2 * k + 1) i = true ↔ i < -1 ∨ 1 < i) := by
  have odd_phase (m : ℕ) (h : ∀ i, cell 1 (2 * m) i = true ↔ i = 0) :
      ∀ i, cell 1 (2 * m + 1) i = true ↔ i < -1 ∨ 1 < i := by
    intro i
    rw [cell, new_on]
    simp only [ne_eq, h]
    omega
  induction k with
  | zero =>
    have h : ∀ i, cell 1 (2 * 0) i = true ↔ i = 0 := by simp [cell]
    exact ⟨h, odd_phase 0 h⟩
  | succ k ih =>
    have h : ∀ i, cell 1 (2 * (k + 1)) i = true ↔ i = 0 := by
      intro i
      rw [show 2 * (k + 1) = (2 * k + 1) + 1 by omega, cell, new_on]
      simp only [ne_eq, ih.2]
      omega
    exact ⟨h, odd_phase _ h⟩

private theorem even_count (k : ℕ) : a (2 * k) = 4 * (k : ℤ) := by
  let n := 2 * k
  change a n = _
  have val (j : ℕ) : (if cell 1 n ((j : ℤ) - n) then (0 : ℤ) else (1 : ℤ)) = 1 - (if j = n then (1 : ℤ) else 0) := by
    simp only [n, (phases k).1]
    split_ifs <;> omega
  have hn : n < 2 * n + 1 := by omega
  simp only [a, val]
  simp [Finset.sum_sub_distrib, hn]
  dsimp [n]
  ring

private theorem odd_count (k : ℕ) : a (2 * k + 1) = 3 := by
  let n := 2 * k + 1
  change a n = _
  have val (j : ℕ) : (if cell 1 n ((j : ℤ) - n) then (0 : ℤ) else (1 : ℤ)) = (if j = n - 1 then (1 : ℤ) else 0) + (if j = n then (1 : ℤ) else 0) + (if j = n + 1 then (1 : ℤ) else 0) := by
    simp only [n, (phases k).2]
    split_ifs <;> omega
  have h₁ : n - 1 < 2 * n + 1 := by omega
  have h₂ : n < 2 * n + 1 := by omega
  have h₃ : n + 1 < 2 * n + 1 := by dsimp [n]; omega
  simp only [a, val]
  simp [Finset.sum_add_distrib, h₁, h₂, h₃]

private theorem stride (n : ℕ) : a (n + 4) = 2 * a (n + 2) - a n := by
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' n
  · rw [show 2 * k + 4 = 2 * (k + 2) by omega, show 2 * k + 2 = 2 * (k + 1) by omega,
      even_count, even_count, even_count]
    push_cast
    ring
  · rw [show 2 * k + 1 + 4 = 2 * (k + 2) + 1 by omega,
      show 2 * k + 1 + 2 = 2 * (k + 1) + 1 by omega, odd_count, odd_count, odd_count]
    norm_num

private theorem recurrence (n : ℕ) (hn : 3 < n) : a n = 2 * a (n - 2) - a (n - 4) := by
  have h := stride (n - 4)
  rwa [show n - 4 + 4 = n by omega, show n - 4 + 2 = n - 2 by omega] at h

open scoped PowerSeries

private theorem generating : mk (fun n => (a n : ℚ)) * ((1 - X) ^ 2 * (1 + X) ^ 2) = X * (3 + 4 * X - 3 * X ^ 2) := by
  let f := mk (fun n => (a n : ℚ))
  change f * _ = _
  rw [show f * ((1 - X) ^ 2 * (1 + X) ^ 2) = f - (f * X ^ 2 + f * X ^ 2) + f * X ^ 4 by ring]
  have num : (X * (3 + 4 * X - 3 * X ^ 2) : ℚ⟦X⟧) = C 3 * X ^ 1 + C 4 * X ^ 2 - C 3 * X ^ 3 := by
    rw [show C (3 : ℚ) = (3 : ℚ⟦X⟧) from map_ofNat C 3,
      show C (4 : ℚ) = (4 : ℚ⟦X⟧) from map_ofNat C 4]
    ring
  rw [num]
  ext n
  simp only [map_add, map_sub, coeff_C_mul_X_pow]
  simp only [coeff_mul_X_pow', f, coeff_mk]
  by_cases hn : n < 4
  · have h₀ : a 0 = 0 := by decide
    have h₁ : a 1 = 3 := by decide
    have h₂ : a 2 = 4 := by decide
    have h₃ : a 3 = 3 := by decide
    interval_cases n <;> norm_num [h₀, h₁, h₂, h₃]
  · have hr : (a n : ℚ) = 2 * (a (n - 2) : ℚ) - (a (n - 4) : ℚ) := by
      exact_mod_cast recurrence n (by omega)
    simp [show 2 ≤ n by omega, show 4 ≤ n by omega, show n ≠ 1 by omega, show n ≠ 2 by omega, show n ≠ 3 by omega]
    linarith

end CellCountProof

open OMA.S_oeis_a265723 CellCountProof in
theorem OMA.solution : type_of% @OMA.S_oeis_a265723.main := by
  refine ⟨?_, recurrence, generating⟩
  intro n
  rw [zpow_natCast]
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' n
  · norm_num [even_count, pow_mul, pow_add]
    ring
  · norm_num [odd_count, pow_mul, pow_add]
