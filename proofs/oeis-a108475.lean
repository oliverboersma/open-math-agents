import OMAStatements.S_oeis_a108475

-- Problem: A108475: Expansion of (1-3*x) / (1-5*x-5*x^2+x^3).
-- Upstream: formal-conjectures statements/oeis-a108475.lean:0 (declaration OMA.S_oeis_a108475.main)
-- Credit: @marcelopierry (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace OMA.P_oeis_a108475

open OMA.S_oeis_a108475 PowerSeries

def c (n : ℕ) : ℤ := pell (n + 1) * pellLucas n

lemma c_rec (n : ℕ) : c (n + 3) = 5 * c (n + 2) + 5 * c (n + 1) - c n := by
  simp only [c, pell, pellLucas]
  ring

lemma coeff_Xpow (f : ℕ → ℚ) (k d : ℕ) :
    coeff d (mk f * X ^ k) = if k ≤ d then f (d - k) else 0 := by
  rw [coeff_mul_X_pow', coeff_mk]

lemma key : mk (fun n => (c n : ℚ)) * (1 - 5 * X - 5 * X ^ 2 + X ^ 3 : PowerSeries ℚ) =
    1 - 3 * X := by
  have hpoly : (1 - 5 * X - 5 * X ^ 2 + X ^ 3 : PowerSeries ℚ) =
      X ^ 0 - C (5 : ℚ) * X ^ 1 - C (5 : ℚ) * X ^ 2 + X ^ 3 := by
    simp only [map_ofNat]
    ring
  have hrhs : (1 - 3 * X : PowerSeries ℚ) = X ^ 0 - C (3 : ℚ) * X ^ 1 := by
    simp only [map_ofNat]
    ring
  rw [hpoly, hrhs]
  ext d
  have e : mk (fun n => (c n : ℚ)) * (X ^ 0 - C (5 : ℚ) * X ^ 1 - C (5 : ℚ) * X ^ 2 + X ^ 3) =
      mk (fun n => (c n : ℚ)) * X ^ 0 - C (5 : ℚ) * (mk (fun n => (c n : ℚ)) * X ^ 1) -
        C (5 : ℚ) * (mk (fun n => (c n : ℚ)) * X ^ 2) + mk (fun n => (c n : ℚ)) * X ^ 3 := by
    ring
  rw [e]
  simp only [map_sub, map_add, coeff_C_mul, coeff_Xpow, coeff_X_pow]
  have c0 : c 0 = 1 := by decide
  have c1 : c 1 = 2 := by decide
  have c2 : c 2 = 15 := by decide
  rcases d with _ | _ | _ | m
  · simp [c0]
  · simp [c0, c1]
    norm_num
  · simp [c0, c1, c2]
    norm_num
  · have h := c_rec m
    have hq : (c (m + 3) : ℚ) = 5 * c (m + 2) + 5 * c (m + 1) - c m := by exact_mod_cast h
    have e0 : (0 : ℕ) ≤ m + 1 + 1 + 1 := by omega
    have e1 : (1 : ℕ) ≤ m + 1 + 1 + 1 := by omega
    have e2 : (2 : ℕ) ≤ m + 1 + 1 + 1 := by omega
    have e3 : (3 : ℕ) ≤ m + 1 + 1 + 1 := by omega
    have e4 : ¬ (m + 1 + 1 + 1 = 0) := by omega
    have e5 : ¬ (m + 1 + 1 + 1 = 1) := by omega
    simp only [if_pos e0, if_pos e1, if_pos e2, if_pos e3, if_neg e4, if_neg e5]
    rw [show m + 1 + 1 + 1 - 0 = m + 3 by omega, show m + 1 + 1 + 1 - 1 = m + 2 by omega,
      show m + 1 + 1 + 1 - 2 = m + 1 by omega, show m + 1 + 1 + 1 - 3 = m by omega]
    linear_combination hq

lemma solve : ∀ n : ℕ, a n = pell (n + 1) * pellLucas n := by
  have hu : IsUnit (1 - 5 * X - 5 * X ^ 2 + X ^ 3 : PowerSeries ℚ) := by
    rw [isUnit_iff_constantCoeff]
    simp
  have h : (1 - 3 * X : PowerSeries ℚ) * (1 - 5 * X - 5 * X ^ 2 + X ^ 3 : PowerSeries ℚ)⁻¹ =
      mk (fun n => (c n : ℚ)) := by
    rw [← key, mul_assoc, PowerSeries.mul_inv_cancel _ (by simp), mul_one]
  intro n
  unfold a
  rw [h, coeff_mk]
  simp [c]

end OMA.P_oeis_a108475

theorem OMA.solution : type_of% @OMA.S_oeis_a108475.main := OMA.P_oeis_a108475.solve
