import FormalConjectures.OEIS.«183129»

-- Credit: @harshshah1618

/-! Only the linear term of the exponential contributes to the first coefficient,
since the substituted series is divisible by `X`. -/

open OeisA183129 PowerSeries in
theorem OMA.solution : type_of% @OeisA183129.a_1 := by
  let L : ℚ⟦X⟧ := hannaLog fun n k => ((n + k - 1).choose k : ℤ) ^ (k ^ 2 + k)
  have h0 : coeff 0 L = 0 := by simp [L, hannaLog, coeff_mk]
  have h1 : coeff 1 L = 1 := by simp [L, hannaLog, coeff_mk]
  have hX : (X : ℚ⟦X⟧) ∣ L := X_dvd_iff.mpr (by simpa using h0)
  have hs : HasSubst L := HasSubst.of_constantCoeff_zero' (by simpa using h0)
  change coeff 1 (subst L (exp ℚ)) = 1
  rw [coeff_subst' hs, finsum_eq_single _ 1]
  · simp [coeff_exp, h1]
  · intro d hd
    cases d with
    | zero => simp
    | succ k =>
      have hdiv := pow_dvd_pow_of_dvd hX (k + 1)
      rw [X_pow_dvd_iff] at hdiv
      rw [hdiv 1 (by omega), smul_zero]
