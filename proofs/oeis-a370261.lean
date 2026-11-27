import OMAStatements.S_oeis_a370261
import Mathlib

open OMA.S_oeis_a370261

namespace OMA.P_oeis_a370261

open Polynomial

/-- Pell identity for Chebyshev polynomials: T_m^2 - (X^2-1) U_{m-1}^2 = 1. -/
theorem pell (m : ℕ) :
    Chebyshev.T ℤ (m : ℤ) ^ 2 - (X ^ 2 - 1) * Chebyshev.U ℤ ((m : ℤ) - 1) ^ 2 = 1 := by
  induction m with
  | zero => simp [Chebyshev.T_zero, Chebyshev.U_neg_one]
  | succ m ih =>
    have h1 : Chebyshev.T ℤ ((m : ℤ) + 1) =
        X * Chebyshev.T ℤ (m : ℤ) + (X ^ 2 - 1) * Chebyshev.U ℤ ((m : ℤ) - 1) := by
      have := Chebyshev.T_eq_X_mul_T_sub_pol_U ℤ ((m : ℤ) - 1)
      have e1 : (m : ℤ) - 1 + 2 = (m : ℤ) + 1 := by ring
      have e2 : (m : ℤ) - 1 + 1 = (m : ℤ) := by ring
      rw [e1, e2] at this
      rw [this]; ring
    have h2 : Chebyshev.U ℤ (m : ℤ) =
        X * Chebyshev.U ℤ ((m : ℤ) - 1) + Chebyshev.T ℤ (m : ℤ) := by
      have := Chebyshev.U_eq_X_mul_U_add_T ℤ ((m : ℤ) - 1)
      have e2 : (m : ℤ) - 1 + 1 = (m : ℤ) := by ring
      rw [e2] at this
      exact this
    have e3 : (((m + 1 : ℕ) : ℤ)) = (m : ℤ) + 1 := by push_cast; ring
    have e4 : (m : ℤ) + 1 - 1 = (m : ℤ) := by ring
    rw [e3, e4, h1, h2]
    linear_combination ih

theorem main_proof : ∀ n : ℕ, 1 ≤ n → ∃ k : ℕ, a n = k := by
  intro n hn
  set x : ℤ := 2 * (n : ℤ) + 1 with hx
  set u : ℤ := (Chebyshev.U ℤ ((n : ℤ) - 1)).eval x with hu
  set t : ℤ := (Chebyshev.T ℤ (n : ℤ)).eval x with ht
  have hpell : t ^ 2 - (x ^ 2 - 1) * u ^ 2 = 1 := by
    have := congrArg (Polynomial.eval x) (pell n)
    simpa [ht, hu] using this
  have hdouble : (Chebyshev.T ℤ ((2 * n : ℕ) : ℤ)).eval ((((2 * n : ℕ) : ℤ)) + 1) = 2 * t ^ 2 - 1 := by
    have := congrArg (Polynomial.eval x) (Chebyshev.T_mul_T ℤ (n : ℤ) (n : ℤ))
    have e : (((2 * n : ℕ) : ℤ)) = (n : ℤ) + (n : ℤ) := by push_cast; ring
    have e' : (((2 * n : ℕ) : ℤ)) + 1 = x := by rw [hx]; push_cast; ring
    rw [e', e]
    simp only [eval_mul, eval_ofNat, sub_self, Chebyshev.T_zero, eval_one, eval_add] at this
    rw [← ht] at this
    linear_combination -this
  -- divisibility n ∣ u
  have hdvd : (n : ℤ) ∣ u := by
    have h := Polynomial.sub_dvd_eval_sub x 1 (Chebyshev.U ℤ ((n : ℤ) - 1))
    rw [Chebyshev.U_eval_one, ← hu] at h
    have h2 : x - 1 = 2 * (n : ℤ) := by rw [hx]; ring
    rw [h2] at h
    have h3 : (n : ℤ) ∣ u - ((n : ℤ) - 1 + 1) := dvd_trans (Dvd.intro_left 2 rfl) h
    have h4 : (n : ℤ) ∣ ((n : ℤ) - 1 + 1) := ⟨1, by ring⟩
    have := dvd_add h3 h4
    simpa using this
  obtain ⟨c, hc⟩ := hdvd
  refine ⟨c.natAbs, ?_⟩
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hval : (A370259 (2 * n) : ℝ) / ((n : ℝ) + 1) = (c : ℝ) ^ 2 := by
    unfold A370259
    rw [hdouble]
    have key : ((2 * t ^ 2 - 1 : ℤ) : ℚ) - 1 = 8 * (n : ℚ) ^ 3 * ((n : ℚ) + 1) * (c : ℚ) ^ 2 := by
      have : 2 * t ^ 2 - 1 - 1 = 8 * (n : ℤ) ^ 3 * ((n : ℤ) + 1) * c ^ 2 := by
        rw [hc] at hpell
        rw [hx] at hpell
        linear_combination 2 * hpell
      exact_mod_cast this
    rw [key]
    push_cast
    have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnpos
    have hn1 : (n : ℝ) + 1 ≠ 0 := by positivity
    field_simp
    ring
  unfold a
  rw [hval, Real.sqrt_sq_eq_abs]
  simp

end OMA.P_oeis_a370261

theorem OMA.solution : type_of% @OMA.S_oeis_a370261.main := OMA.P_oeis_a370261.main_proof
