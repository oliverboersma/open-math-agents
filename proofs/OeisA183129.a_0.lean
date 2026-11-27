import FormalConjectures.OEIS.«183129»

open PowerSeries OeisA183129

theorem OMA.solution : type_of% @OeisA183129.a_0 := by
  unfold a hannaExp
  suffices h : ∀ L : ℚ⟦X⟧, constantCoeff L = 0 → coeff 0 (subst L (exp ℚ)) = 1 by
    exact h _ (by simp [hannaLog, constantCoeff_mk])
  intro L hL
  rw [coeff_subst' (HasSubst.of_constantCoeff_zero' hL), finsum_eq_single _ 0]
  · simp [coeff_exp]
  · intro i hi
    rw [coeff_zero_eq_constantCoeff_apply, map_pow, hL, zero_pow hi, smul_zero]
