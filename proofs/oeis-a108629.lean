import OMAStatements.S_oeis_a108629

-- Problem: A108629: Expansion of g.f.: (1+x - sqrt(1-2*x-3*x^2-4*x^3))/(2+2*x+2*x^2).
-- Upstream: formal-conjectures statements/oeis-a108629.lean:0 (declaration OMA.S_oeis_a108629.main)
-- Credit: @Raimo33 (the owner of the agent is credited as the solver)
-- Proof: R = rootSeries satisfies R^2 = 1 + t, so 2 (1 + t) R' = t' R. Substituting
-- R = 1 + X - 2 (1 + X + X^2) A gives a first-order linear ODE for A, whose coefficient
-- of X^(n-1) is the recurrence.

namespace OMA.P_a108629
open OMA.S_oeis_a108629 PowerSeries

lemma hasSubst_t : HasSubst radicandTail :=
  HasSubst.of_constantCoeff_zero' (by simp [radicandTail])

lemma root_sq : rootSeries ^ 2 = 1 + radicandTail := by
  have hB : (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)) ^ 2 = (1 + X : PowerSeries ℚ) := by
    rw [sq, ← PowerSeries.binomialSeries_add]
    norm_num
    simpa using binomialSeries_nat (A := ℚ) (R := ℚ) 1
  unfold rootSeries
  rw [← subst_pow hasSubst_t, hB, ← coe_substAlgHom hasSubst_t, map_add, map_one,
    coe_substAlgHom, subst_X hasSubst_t]

lemma d_t : d⁄dX ℚ radicandTail = -2 - 6 * X - 12 * X ^ 2 := by
  have : radicandTail = C (-2 : ℚ) * X + C (-3 : ℚ) * X ^ 2 + C (-4 : ℚ) * X ^ 3 := by
    simp only [radicandTail, map_neg, map_ofNat]; ring
  rw [this]
  simp only [map_add, Derivation.leibniz, Derivation.leibniz_pow, derivative_C, derivative_X,
    smul_eq_mul]
  simp only [map_neg, map_ofNat]
  ring

lemma two_D_A : 2 * (1 + X + X ^ 2) * series = 1 + X - rootSeries := by
  unfold series
  have h : constantCoeff (2 * (1 + X + X ^ 2) : PowerSeries ℚ) ≠ 0 := by
    rw [map_mul, map_ofNat]; simp
  rw [mul_comm, mul_assoc, mul_comm _ (2 * (1 + X + X ^ 2)), PowerSeries.mul_inv_cancel _ h,
    mul_one]

lemma ode :
    4 * (4 * X ^ 5 + 7 * X ^ 4 + 9 * X ^ 3 + 4 * X ^ 2 + X - 1) * d⁄dX ℚ series
      + 4 * (2 * X ^ 4 + X ^ 3 - 3 * X ^ 2 - 4 * X - 2) * series
      + 4 * (X ^ 3 + 3 * X ^ 2 + X + 1) = 0 := by
  have hR : rootSeries = 1 + X - 2 * (1 + X + X ^ 2) * series := by rw [two_D_A]; ring
  have h2 := congrArg (d⁄dX ℚ) root_sq
  rw [sq, Derivation.leibniz, map_add, derivative_one, d_t, smul_eq_mul,
    zero_add] at h2
  have h3 : 2 * (1 + radicandTail) * d⁄dX ℚ rootSeries
      = rootSeries * (-2 - 6 * X - 12 * X ^ 2) := by
    rw [← root_sq]; linear_combination rootSeries * h2
  have hdR := congrArg (d⁄dX ℚ) hR
  simp only [map_add, map_sub, Derivation.leibniz, Derivation.leibniz_pow, derivative_one,
    derivative_X, smul_eq_mul] at hdR
  have h2d : d⁄dX ℚ (2 : PowerSeries ℚ) = 0 := by
    rw [show (2 : PowerSeries ℚ) = C 2 by simp only [map_ofNat], derivative_C]
  rw [h2d] at hdR
  simp only [radicandTail] at h3
  linear_combination h3 - 2 * (1 + (-2 * X - 3 * X ^ 2 - 4 * X ^ 3)) * hdR
    + (-2 - 6 * X - 12 * X ^ 2) * hR

lemma ode' :
    C (16 : ℚ) * X ^ 5 * d⁄dX ℚ series + C (28 : ℚ) * X ^ 4 * d⁄dX ℚ series
      + C (36 : ℚ) * X ^ 3 * d⁄dX ℚ series + C (16 : ℚ) * X ^ 2 * d⁄dX ℚ series
      + C (4 : ℚ) * X ^ 1 * d⁄dX ℚ series + C (-4 : ℚ) * X ^ 0 * d⁄dX ℚ series
      + C (8 : ℚ) * X ^ 4 * series + C (4 : ℚ) * X ^ 3 * series
      + C (-12 : ℚ) * X ^ 2 * series + C (-16 : ℚ) * X ^ 1 * series
      + C (-8 : ℚ) * X ^ 0 * series
      + (C (4 : ℚ) * X ^ 3 + C (12 : ℚ) * X ^ 2 + C (4 : ℚ) * X ^ 1 + C (4 : ℚ) * X ^ 0) = 0 := by
  simp only [map_neg, map_ofNat]
  linear_combination ode

end OMA.P_a108629

open OMA.S_oeis_a108629 OMA.P_a108629 PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a108629.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 6 := ⟨n - 6, by omega⟩
  have h := congrArg (coeff (m + 5)) ode'
  simp only [mul_assoc, map_add, map_zero, coeff_C_mul, coeff_X_pow_mul', coeff_derivative,
    coeff_X_pow] at h
  simp at h
  unfold a
  have e1 : m + 6 - 1 = m + 5 := by omega
  have e2 : m + 6 - 2 = m + 4 := by omega
  have e3 : m + 6 - 3 = m + 3 := by omega
  have e4 : m + 6 - 4 = m + 2 := by omega
  have e5 : m + 6 - 5 = m + 1 := by omega
  rw [e1, e2, e3, e4, e5]
  push_cast
  linear_combination (-1 / 4 : ℚ) * h
