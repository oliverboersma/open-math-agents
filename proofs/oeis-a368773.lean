import OMAStatements.S_oeis_a368773
import Mathlib

namespace OMA.A368773Proof

open PowerSeries OMA.S_oeis_a368773

lemma dnum (m : ℕ) [m.AtLeastTwo] : derivative ℚ (no_index (OfNat.ofNat m : ℚ⟦X⟧)) = 0 := by
  rw [← map_ofNat C m]; exact derivative_C

lemma cnum (m n : ℕ) [m.AtLeastTwo] (f : ℚ⟦X⟧) :
    coeff n ((no_index (OfNat.ofNat m : ℚ⟦X⟧)) * f) = (OfNat.ofNat m : ℚ) * coeff n f := by
  rw [← map_ofNat C m, coeff_C_mul]

lemma hasSubst : HasSubst (-10 * X ^ 2 + 9 * X ^ 4 : PowerSeries ℚ) :=
  HasSubst.of_constantCoeff_zero' (by simp)

lemma radical_sq : radical ^ 2 = 1 - 10 * X ^ 2 + 9 * X ^ 4 := by
  have h : PowerSeries.binomialSeries ℚ (1 / 2 : ℚ) ^ 2 = 1 + X := by
    rw [sq, ← PowerSeries.binomialSeries_add]
    have : (1 / 2 + 1 / 2 : ℚ) = ((1 : ℕ) : ℚ) := by norm_num
    rw [this, PowerSeries.binomialSeries_nat, pow_one]
  unfold radical
  rw [← subst_pow hasSubst, h, ← coe_substAlgHom hasSubst, map_add, map_one,
    coe_substAlgHom hasSubst, subst_X hasSubst]
  ring

lemma ode_R : 2 * (1 - 10 * X ^ 2 + 9 * X ^ 4) * derivative ℚ radical =
    radical * (-20 * X + 36 * X ^ 3) := by
  have hsq := radical_sq
  have hD : derivative ℚ (radical ^ 2) = derivative ℚ (1 - 10 * X ^ 2 + 9 * X ^ 4 : ℚ⟦X⟧) :=
    congrArg _ hsq
  have hP : derivative ℚ (1 - 10 * X ^ 2 + 9 * X ^ 4 : PowerSeries ℚ) = -20 * X + 36 * X ^ 3 := by
    simp [dnum]
    ring
  rw [hP, sq, Derivation.leibniz, smul_eq_mul] at hD
  linear_combination (-2 * derivative ℚ radical) * hsq + radical * hD

lemma ode_B : 2 * (1 - 10 * X ^ 2 + 9 * X ^ 4) * derivative ℚ B =
    (6 - 2 * X - 6 * X ^ 2 + 18 * X ^ 3) * B := by
  have hU : (1 - 3 * X : ℚ⟦X⟧) * (1 - 3 * X)⁻¹ = 1 :=
    PowerSeries.mul_inv_cancel _ (by simp)
  have hDU : derivative ℚ ((1 - 3 * X : ℚ⟦X⟧)⁻¹) = 3 * ((1 - 3 * X : ℚ⟦X⟧)⁻¹) ^ 2 := by
    rw [derivative_inv']
    simp [dnum]
    ring
  have h1 := ode_R
  unfold B
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, hDU]
  linear_combination ((1 - 3 * X : ℚ⟦X⟧)⁻¹) * h1 +
    (6 * radical * (1 - 3 * X : ℚ⟦X⟧)⁻¹ * (1 - X ^ 2) * (1 + 3 * X)) * hU

lemma cx (f : ℚ⟦X⟧) (j k : ℕ) : coeff (k + j) (X ^ j * f) = coeff k f :=
  coeff_X_pow_mul f j k

lemma rec_B (k : ℕ) :
    2 * ((k : ℚ) + 5) * coeff (k + 5) B - 20 * ((k : ℚ) + 3) * coeff (k + 3) B +
      18 * ((k : ℚ) + 1) * coeff (k + 1) B =
    6 * coeff (k + 4) B - 2 * coeff (k + 3) B - 6 * coeff (k + 2) B + 18 * coeff (k + 1) B := by
  have E := ode_B
  have E' : 2 * derivative ℚ B - 20 * (X ^ 2 * derivative ℚ B) + 18 * (X ^ 4 * derivative ℚ B) =
      6 * B - 2 * (X ^ 1 * B) - 6 * (X ^ 2 * B) + 18 * (X ^ 3 * B) := by
    linear_combination E
  have h := congrArg (coeff (k + 4)) E'
  simp only [map_add, map_sub, cnum] at h
  rw [cx _ 2 (k + 2), cx _ 4 k, cx _ 1 (k + 3), cx _ 2 (k + 2), cx _ 3 (k + 1)] at h
  simp only [coeff_derivative] at h
  push_cast at h
  linear_combination h

end OMA.A368773Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a368773.main := by
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 := ⟨n - 4, by omega⟩
  have hr := OMA.A368773Proof.rec_B k
  simp only [show k + 4 - 1 = k + 3 by omega, show k + 4 - 2 = k + 2 by omega,
    show k + 4 - 3 = k + 1 by omega, show k + 4 - 4 = k by omega]
  unfold OMA.S_oeis_a368773.a
  simp only [map_add, map_sub, PowerSeries.coeff_one, PowerSeries.coeff_X]
  rcases k with _ | k
  · simp
    push_cast at hr ⊢
    linear_combination hr / 8
  · simp
    push_cast at hr ⊢
    linear_combination hr / 8
