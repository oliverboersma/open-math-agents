import OMAReductions.R_OeisA4290_conjecture_R1_H1_R1
import Mathlib

-- Step OeisA4290.conjecture.R1.H1.R1.H2: hypothesis H2 of reduction OeisA4290.conjecture.R1.H1.R1
-- Credit: @ivillar. Short repunits: if 9n divides 10^t - 1 with t < 9k, the repunit with t digits works.

/-! Repunit multiples for divisors of short repunits. -/

namespace P7A4290H2

/-- All decimal digits are `0` or `1`. -/
def D01 (m : ℕ) : Prop := ∀ d ∈ Nat.digits 10 m, d = 0 ∨ d = 1

lemma d01_step (a y : ℕ) (ha : a ≤ 1) (hy : D01 y) : D01 (a + 10 * y) := by
  rcases Nat.eq_zero_or_pos y with rfl | hy0
  · interval_cases a <;> simp [D01]
  · intro d hd
    rw [Nat.digits_add 10 (by norm_num) a y (by omega) (Or.inr hy0.ne')] at hd
    rcases List.mem_cons.mp hd with rfl | hd
    · omega
    · exact hy d hd

lemma finish (k m : ℕ) (h : 9 * m + 2 ≤ 10 ^ (9 * k)) : m < (10 ^ (9 * k) - 1) / 9 := by
  have hd : 9 ∣ 10 ^ (9 * k) - 1 := by
    have h := (show 10 ≡ 1 [MOD 9] by decide).pow (9 * k)
    rw [one_pow] at h
    exact (Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ (by norm_num))).mp h.symm
  obtain ⟨R, hR⟩ := hd
  rw [hR, Nat.mul_div_cancel_left _ (by norm_num)]
  omega

/-- The repunit with `j` digits. -/
def rep : ℕ → ℕ
  | 0 => 0
  | j + 1 => 1 + 10 * rep j

lemma rep_d01 (j : ℕ) : D01 (rep j) := by
  induction j with
  | zero => simp [rep, D01]
  | succ j ih => exact d01_step 1 _ le_rfl ih

lemma rep_eq (j : ℕ) : 9 * rep j + 1 = 10 ^ j := by
  induction j with
  | zero => simp [rep]
  | succ j ih =>
    simp only [rep, pow_succ]
    omega

end P7A4290H2

open P7A4290H2

theorem OMA.solution : OMA.R_OeisA4290_conjecture_R1_H1_R1.H2 := by
  unfold OMA.R_OeisA4290_conjecture_R1_H1_R1.H2
  intro k n t hn hnk ht htk hdvd
  have hr := rep_eq t
  refine ⟨rep t, ?_, ?_, ?_, rep_d01 t⟩
  · apply finish
    have : 10 ^ t < 10 ^ (9 * k) := Nat.pow_lt_pow_right (by norm_num) htk
    omega
  · have : 10 ^ 1 ≤ 10 ^ t := Nat.pow_le_pow_right (by norm_num) ht
    omega
  · have h9 : 9 * n ∣ 9 * rep t := by
      have : 10 ^ t - 1 = 9 * rep t := by omega
      rwa [this] at hdvd
    exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) h9
