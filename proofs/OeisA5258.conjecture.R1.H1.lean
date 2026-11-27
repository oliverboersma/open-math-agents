import OMAReductions.R_OeisA5258_conjecture_R1

/-! The Apéry polynomial with n + 1 prime has constant coefficient 1 and reduces
to 1 modulo n + 1. Any two positive-degree integer factors would therefore both
have leading coefficient divisible by n + 1, contradicting the valuation of
the central binomial coefficient. -/
open Polynomial Finset
namespace AperyPrime
private def a (n k : ℕ) := (n.choose k)^2 * (n+k).choose k
private noncomputable def F (n : ℕ) : ℤ[X] :=
  ∑ k ∈ range (n+1), C (a n k : ℤ) * X^k

private theorem coeff (n i : ℕ) : (F n).coeff i = if i ≤ n then (a n i : ℤ) else 0 := by
  simp [F,finsetSum_coeff]

private theorem primitive (n : ℕ) : (F n).IsPrimitive := by
  apply isPrimitive_iff_isUnit_of_C_dvd.mpr
  intro c hc
  apply isUnit_iff_dvd_one.mpr
  simpa [coeff,a] using (C_dvd_iff_dvd_coeff _ _).mp hc 0

private theorem lc_dvd {p : ℕ} [Fact p.Prime] (g : ℤ[X])
    (hg : IsUnit (g.map (Int.castRingHom (ZMod p)))) (h0 : IsUnit (g.coeff 0))
    (hu : ¬ IsUnit g) : (p : ℤ) ∣ g.leadingCoeff := by
  have hdeg : 0 < g.natDegree := by
    by_contra! hn
    have he := eq_C_of_natDegree_eq_zero (Nat.eq_zero_of_le_zero hn)
    exact hu (he ▸ isUnit_C.mpr h0)
  have hsmall : (g.map (Int.castRingHom (ZMod p))).natDegree < g.natDegree := by
    rwa [natDegree_eq_zero_of_isUnit hg]
  have hcoeff := coeff_eq_zero_of_natDegree_lt hsmall
  rw [coeff_map] at hcoeff
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd g.leadingCoeff p).mp hcoeff

private theorem irr (n : ℕ) (hn : 1 ≤ n) (hp : (n+1).Prime) : Irreducible (F n) := by
  let p := n+1
  have hp' : p.Prime := hp
  have : Fact p.Prime := ⟨hp⟩
  have ht : 0 < (n+n).choose n := Nat.choose_pos (by omega)
  have hdeg : (F n).natDegree = n := by
    apply natDegree_eq_of_le_of_coeff_ne_zero
    · apply natDegree_le_iff_coeff_eq_zero.mpr
      intro j hj
      simp [coeff,not_le.mpr hj]
    · simpa [coeff,a] using ht.ne'
  have hlead : (F n).leadingCoeff = ((n+n).choose n : ℤ) := by simp [leadingCoeff,hdeg,coeff,a]
  have hmap : (F n).map (Int.castRingHom (ZMod p)) = 1 := by
    ext i
    rw [coeff_map,coeff]
    by_cases hi : i = 0
    · subst i; simp [a]
    rw [coeff_one,if_neg hi]
    by_cases hin : i ≤ n
    · rw [if_pos hin]
      apply (ZMod.intCast_zmod_eq_zero_iff_dvd (a n i : ℤ) p).mpr
      have hdiv : p ∣ (n+i).choose i := hp'.dvd_choose (by dsimp [p]; omega)
        (by dsimp [p]; omega) (by dsimp [p]; omega)
      exact_mod_cast (dvd_mul_of_dvd_right hdiv (n.choose i ^ 2))
    · simp [hin]
  refine ⟨not_isUnit_of_natDegree_pos _ (by rw [hdeg]; omega),?_⟩
  intro g h hgh
  by_contra! hboth
  have hunit : IsUnit ((g.map (Int.castRingHom (ZMod p))) * h.map (Int.castRingHom (ZMod p))) := by
    rw [← Polynomial.map_mul,←hgh,hmap]
    exact isUnit_one
  have hunit0 : IsUnit (g.coeff 0 * h.coeff 0) := by
    rw [← mul_coeff_zero,←hgh]
    simp [coeff,a]
  have hdiv := mul_dvd_mul (lc_dvd g (IsUnit.mul_iff.mp hunit).1 (IsUnit.mul_iff.mp hunit0).1 hboth.1)
    (lc_dvd h (IsUnit.mul_iff.mp hunit).2 (IsUnit.mul_iff.mp hunit0).2 hboth.2)
  rw [← leadingCoeff_mul,←hgh,hlead,←sq] at hdiv
  have hnat : p^2 ∣ (n+n).choose n := by exact_mod_cast hdiv
  have hlo := (hp'.pow_dvd_iff_le_factorization ht.ne').mp hnat
  have hhi : ((n+n).choose n).factorization p ≤ 1 := Nat.factorization_choose_le_one (by dsimp [p]; nlinarith)
  omega
end AperyPrime

theorem OMA.solution : OMA.R_OeisA5258_conjecture_R1.H1 := by
  intro n hn hp
  have h := (Polynomial.IsPrimitive.Int.irreducible_iff_irreducible_map_cast
    (AperyPrime.primitive n)).mp (AperyPrime.irr n hn hp)
  simpa [AperyPrime.F,AperyPrime.a,OeisA5258.aperyPoly,Polynomial.map_sum,Polynomial.map_mul,Polynomial.map_pow] using h
