import FormalConjectures.OEIS.«181078»


open PowerSeries OeisA181078

namespace OMA.A181078

lemma subst_coeff_sum (g f : ℚ⟦X⟧) (hg : g.constantCoeff = 0) (n : ℕ) :
    coeff n (subst g f) = ∑ d ∈ Finset.range (n+1), coeff d f * coeff n (g^d) := by
  rw [coeff_subst' (HasSubst.of_constantCoeff_zero' hg)]
  simp only [smul_eq_mul]
  apply finsum_eq_sum_of_support_subset
  intro d hd
  apply Finset.mem_range.mpr
  by_contra hn
  have hnd : n < d := by omega
  have hz : coeff n (g^d) = 0 := coeff_of_lt_order _
    ((by exact_mod_cast hnd : (n : ℕ∞) < d).trans_le
      (le_order_pow_of_constantCoeff_eq_zero d hg))
  exact hd (by simp [hz])

lemma log_const (f : ℕ → ℕ → ℤ) : (hannaLog f).constantCoeff = 0 := by
  simp [hannaLog, ← coeff_zero_eq_constantCoeff_apply]

end OMA.A181078

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
theorem OMA.solution : type_of% @OeisA181078.a_3 := by
  unfold a hannaExp
  rw [OMA.A181078.subst_coeff_sum _ _ (OMA.A181078.log_const _) 3]
  norm_num [Finset.sum_range_succ, coeff_exp, pow_succ, coeff_mul,
    Finset.Nat.antidiagonal_succ, Finset.Nat.antidiagonal_zero,
    hannaLog, coeff_mk, Finset.sum_Icc_succ_top, Nat.factorial]
