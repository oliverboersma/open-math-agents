import FormalConjectures.GreensOpenProblems.«47»
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Data.ZMod.Basic

/-!
If one fixed affine discriminant takes square values modulo all large
primes, those values are integer squares. This gives a single rational
quadratic for all points outside the chosen finite exceptional set.
-/

namespace OMA.R_Green47_green_47_variants_finite_exceptions_R1

open Filter Polynomial

def H1 : Prop :=
  ∀ d : ℕ, (∀ᶠ p : ℕ in atTop, p.Prime → IsSquare (d : ZMod p)) → IsSquare d

def H2 : Prop :=
  ∀ A : Set ℕ,
    (∀ᶠ p in atTop, Nat.Prime p →
      Set.ncard (Set.image (fun a : ℕ => (a : ZMod p)) A) ≤ (p + 1) / 2) →
    ¬ ((fun X : ℕ => ((A ∩ Set.Iic X).ncard : ℝ)) ≪
      (fun X : ℕ => Real.sqrt (X : ℝ) / (Real.log (X : ℝ)) ^ 100)) →
    ∃ m : ℕ, 0 < m ∧ ∃ b : ℤ, ∃ F : Finset ℕ,
      (∀ a ∈ A, a ∉ F → 0 ≤ (m : ℤ) * a + b) ∧
      ∀ᶠ p : ℕ in atTop, p.Prime →
        ∀ a ∈ A, a ∉ F → IsSquare (((m : ℤ) * a + b : ℤ) : ZMod p)

section Proof

theorem main : H1 → H2 → type_of% @Green47.green_47.variants.finite_exceptions := by
  intro squareLocal discriminant A hResidue
  by_cases hsmall : ((fun X : ℕ => ((A ∩ Set.Iic X).ncard : ℝ)) ≪
      (fun X : ℕ => Real.sqrt (X : ℝ) / (Real.log (X : ℝ)) ^ 100))
  · exact Or.inl hsmall
  obtain ⟨m, hm, b, F, hpos, hmod⟩ := discriminant A hResidue hsmall
  let P : Polynomial ℚ := C ((m : ℚ)⁻¹) * (X ^ 2 - C (b : ℚ))
  have hm0 : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
  have hDegree : P.degree = 2 := by
    dsimp only [P]
    rw [degree_mul, degree_C (inv_ne_zero hm0), degree_sub_eq_left_of_degree_lt]
    · simp [degree_X_pow]
    · rw [degree_X_pow]
      exact (degree_C_le (a := (b : ℚ))).trans_lt (by norm_num)
  refine Or.inr ⟨P, hDegree, F.finite_toSet.subset ?_⟩
  rintro a ⟨ha, hadd⟩
  by_contra hF
  have ha0 : 0 ≤ (m : ℤ) * a + b := hpos a ha hF
  let d := ((m : ℤ) * a + b).toNat
  have hd : (d : ℤ) = (m : ℤ) * a + b := Int.toNat_of_nonneg ha0
  have hSquare : IsSquare d := squareLocal d (by
    filter_upwards [hmod] with p hp
    intro hprime
    have hdmod : (d : ZMod p) = (((m : ℤ) * a + b : ℤ) : ZMod p) := by
      exact_mod_cast congrArg (fun z : ℤ => (z : ZMod p)) hd
    rw [hdmod]
    exact hp hprime a ha hF)
  obtain ⟨u, hu⟩ := hSquare
  apply hadd
  refine ⟨(u : ℤ), ?_⟩
  have hnumZ : (m : ℤ) * a + b = (u : ℤ) * u := hd.symm.trans (by exact_mod_cast hu)
  have hnum : (m : ℚ) * a + b = (u : ℚ) * u := by exact_mod_cast hnumZ
  simp only [P, eval_mul, eval_C, eval_sub, eval_pow, eval_X, Int.cast_natCast]
  field_simp
  nlinarith [hnum]

end Proof

end OMA.R_Green47_green_47_variants_finite_exceptions_R1
