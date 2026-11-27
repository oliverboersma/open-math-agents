import OMAStatements.S_oeis_a101918

namespace OMA.P_a101918

open OMA.S_oeis_a101918 PowerSeries

lemma key : a 73 + a 72 + a 65 = -1 := by decide +kernel

end OMA.P_a101918

open OMA.S_oeis_a101918 PowerSeries in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a101918.main) := by
  intro h
  have h73 := congrArg (coeff (R := ℤ) 73) h
  have e1 : coeff (R := ℤ) 73 (series * X) = a 72 := by
    rw [show (73 : ℕ) = 72 + 1 from rfl, coeff_succ_mul_X]; simp [series]
  have e8 : coeff (R := ℤ) 73 (series * X ^ 8) = a 65 := by
    rw [show (73 : ℕ) = 65 + 8 from rfl, coeff_mul_X_pow]; simp [series]
  have e0 : coeff (R := ℤ) 73 (1 + X ^ 8 : PowerSeries ℤ) = 0 := by
    simp [coeff_one, coeff_X_pow]
  rw [mul_add, mul_add, mul_one, map_add, map_add, e1, e8, e0] at h73
  have h0 : coeff (R := ℤ) 73 series = a 73 := by simp [series]
  rw [h0] at h73
  have := OMA.P_a101918.key
  omega
