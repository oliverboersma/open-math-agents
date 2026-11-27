import OMAStatements.S_oeis_a267622
import Mathlib

namespace R187
open OMA.S_oeis_a267622

theorem rule_eq (l c r : Bool) : rule l c r = (r || !c) := by
  cases l <;> cases c <;> cases r <;> decide

theorem state_succ (n : ℕ) : state (n + 1) = fun x => !decide (x = -(n : ℤ)) := by
  induction n with
  | zero =>
    funext x
    show rule (initial (x - 1)) (initial x) (initial (x + 1)) = _
    simp only [rule_eq, initial]
    by_cases h : x = 0
    · subst h; simp
    · by_cases h' : x = -1
      · subst h'; simp
      · have h2 : x + 1 ≠ 0 := by omega
        simp [h, h2]
  | succ n ih =>
    funext x
    show rule (state (n + 1) (x - 1)) (state (n + 1) x) (state (n + 1) (x + 1)) = _
    rw [ih]
    simp only [rule_eq]
    by_cases h : x = -((n + 1 : ℕ) : ℤ)
    · have h1 : x + 1 = -(n : ℤ) := by push_cast at h; omega
      have h2 : x ≠ -(n : ℤ) := by push_cast at h; omega
      simp [h, h1, h2]
    · have h1 : x + 1 ≠ -(n : ℤ) := by push_cast at h; omega
      simp [h1]
      push_cast at h
      omega

theorem enc (left : ℤ) (m : ℕ) :
    9 * (encode (fun x => !decide (x = left + 1)) left (m + 2) : ℤ) + 1 + 9 * 10 ^ m
      = 10 ^ (m + 2) := by
  induction m with
  | zero =>
    have h : left ≠ left + 1 := by omega
    simp [encode, bit, h]
  | succ m ih =>
    have hE : encode (fun x => !decide (x = left + 1)) left (m + 1 + 2)
        = 10 * encode (fun x => !decide (x = left + 1)) left (m + 2)
          + bit (!decide (left + ((m + 2 : ℕ) : ℤ) = left + 1)) := rfl
    rw [hE]
    have h : left + ((m + 2 : ℕ) : ℤ) ≠ left + 1 := by push_cast; omega
    simp only [h, decide_false, Bool.not_false, bit, if_true]
    push_cast
    linear_combination 10 * ih

theorem ha (n : ℕ) : 9 * (a (n + 1) : ℤ) + 1 + 9 * 10 ^ (2 * n + 1) = 10 ^ (2 * n + 3) := by
  unfold a
  rw [state_succ]
  have := enc (-((n + 1 : ℕ) : ℤ)) (2 * n + 1)
  have e : -((n + 1 : ℕ) : ℤ) + 1 = -(n : ℤ) := by push_cast; ring
  rw [e] at this
  rw [show 2 * (n + 1) + 1 = 2 * n + 1 + 2 by ring, show 2 * n + 3 = 2 * n + 1 + 2 by ring]
  exact this

theorem ha0 : a 0 = 1 := by decide

theorem recur (m : ℕ) : (a (m + 3) : ℤ) = 101 * (a (m + 2) : ℤ) - 100 * (a (m + 1) : ℤ) := by
  have h3 := ha (m + 2)
  have h2 := ha (m + 1)
  have h1 := ha m
  have : (9 : ℤ) * (a (m + 3) : ℤ) = 9 * (101 * (a (m + 2) : ℤ) - 100 * (a (m + 1) : ℤ)) := by
    rw [show 2 * (m + 2) + 3 = 2 * m + 1 + 6 by ring, show 2 * (m + 2) + 1 = 2 * m + 1 + 4 by ring,
      show 2 * (m + 1) + 3 = 2 * m + 1 + 4 by ring, show 2 * (m + 1) + 1 = 2 * m + 1 + 2 by ring,
      show 2 * m + 3 = 2 * m + 1 + 2 by ring] at *
    simp only [pow_add] at *
    linear_combination h3 - 101 * h2 + 100 * h1
  exact mul_left_cancel₀ (by norm_num) this

end R187

open PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a267622.main := by
  open OMA.S_oeis_a267622 R187 in
  refine ⟨?_, ?_⟩
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
    rw [show m + 3 - 1 = m + 2 by omega, show m + 3 - 2 = m + 1 by omega]
    exact recur m
  · have h1 : (a 1 : ℤ) = 101 := by have := ha 0; norm_num at this; linarith
    have h2 : (a 2 : ℤ) = 10111 := by have := ha 1; norm_num at this; linarith
    rw [show ((1 - X) * (1 - 100 * X) : PowerSeries ℤ)
        = 1 - C 101 * X ^ 1 + C 100 * X ^ 2 by simp only [map_ofNat]; ring,
      show (1 + 10 * X ^ 2 : PowerSeries ℤ) = 1 + X ^ 2 * C 10 by rw [map_ofNat]; ring]
    rw [show ∀ p : PowerSeries ℤ, p * (1 - C 101 * X ^ 1 + C 100 * X ^ 2)
        = p - C 101 * (p * X ^ 1) + C 100 * (p * X ^ 2) from fun p => by ring]
    ext n
    simp only [series, map_sub, map_add, coeff_C_mul, coeff_mul_X_pow', coeff_one, coeff_mk,
      coeff_mul_C, coeff_X_pow]
    rcases n with _ | _ | _ | n
    · simp [ha0]
    · simp [ha0, h1]
    · simp [ha0, h1, h2, coeff_C]
    · have := recur n
      simp only [show n + 1 + 1 + 1 = n + 3 by ring]
      simp [coeff_C]
      rw [this]
      ring
