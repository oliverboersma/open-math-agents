import OMAReductions.R_ERH_extended_riemann_hypothesis_R1_H1_R1_H2_R1

/-! Separate Hecke's ideal-class theta expansion from Poisson summation on the ideal
lattices. In the logarithmic variables the missing coordinate is the negative sum
of the others; the unit fundamental domain therefore has volume the regulator. -/

-- Reduction ERH.extended_riemann_hypothesis.R1.H1.R1.H2.R1.H2.R1 of step ERH.extended_riemann_hypothesis.R1.H1.R1.H2.R1.H2
-- Credit: @STARDUSTLC666

namespace OMA.R_ERH_extended_riemann_hypothesis_R1_H1_R1_H2_R1_H2_R1

open Complex NumberField NumberField.Units NumberField.Units.dirichletUnitTheorem
open NumberField.InfinitePlace NumberField.mixedEmbedding MeasureTheory
open scoped NumberField nonZeroDivisors Classical

/-- The completed inverse Mellin kernel, including the origins, is the normalized sum
of ideal-class theta averages. This is a statement about one positive scale at a time. -/
def H1 : Prop := ∀ (K : Type) [Field K] [NumberField K], 3 ≤ Module.finrank ℚ K →
    let f := mellinInv 2 (fun s => exp (s * (Real.log (discr K).natAbs / 2 : ℝ)) *
      Gammaℝ s ^ nrRealPlaces K * Gammaℂ s ^ nrComplexPlaces K * dedekindZeta K s)
    let c : ℂ := ((2 : ℝ) ^ (nrRealPlaces K + nrComplexPlaces K) * regulator K * classNumber K / torsionOrder K : ℝ)
    let D := ZSpan.fundamentalDomain ((basisUnitLattice K).ofZLatticeBasis ℝ _)
    let u (y : logSpace K) (w : InfinitePlace K) := if h : w = w₀ then -∑ v, y v else y ⟨w, h⟩
    let A (C : ClassGroup (𝓞 K)) (t : ℝ) :=
      let J : (Ideal (𝓞 K))⁰ := (ClassGroup.mk0_surjective C⁻¹).choose
      let s := ((Real.sqrt ((discr K).natAbs : ℝ))⁻¹ * t / Ideal.absNorm (J : Ideal (𝓞 K))) ^ ((2 : ℝ) / Module.finrank ℚ K)
      ∫ y in D, ∑' a : idealLattice K (FractionalIdeal.mk0 K J),
        (Real.exp (-(Real.pi * s) * ∑ w : InfinitePlace K, (mult w : ℝ) * (Real.exp (u y w / mult w) * normAtPlace w a.val) ^ 2) : ℂ)
    ∀ t : ℝ, 0 < t → f t + c = (2 : ℂ) ^ (nrRealPlaces K + nrComplexPlaces K) / (torsionOrder K : ℂ) * ∑ C, A C t

/-- A fixed permutation of ideal classes pairs their Gaussian averages at reciprocal
scales. No zeta function, gamma function, or Mellin transform occurs here. -/
def H2 : Prop := ∀ (K : Type) [Field K] [NumberField K], 3 ≤ Module.finrank ℚ K →
    let D := ZSpan.fundamentalDomain ((basisUnitLattice K).ofZLatticeBasis ℝ _)
    let u (y : logSpace K) (w : InfinitePlace K) := if h : w = w₀ then -∑ v, y v else y ⟨w, h⟩
    let A (C : ClassGroup (𝓞 K)) (t : ℝ) :=
      let J : (Ideal (𝓞 K))⁰ := (ClassGroup.mk0_surjective C⁻¹).choose
      let s := ((Real.sqrt ((discr K).natAbs : ℝ))⁻¹ * t / Ideal.absNorm (J : Ideal (𝓞 K))) ^ ((2 : ℝ) / Module.finrank ℚ K)
      ∫ y in D, ∑' a : idealLattice K (FractionalIdeal.mk0 K J),
        (Real.exp (-(Real.pi * s) * ∑ w : InfinitePlace K, (mult w : ℝ) * (Real.exp (u y w / mult w) * normAtPlace w a.val) ^ 2) : ℂ)
    ∃ p : Equiv.Perm (ClassGroup (𝓞 K)), ∀ (C : ClassGroup (𝓞 K)) (t : ℝ), 0 < t → A C (1 / t) = (t : ℂ) * A (p C) t

theorem sum_reciprocal {ι : Type*} [Fintype ι] {f g : ι → ℂ} (p : Equiv.Perm ι) (x m : ℂ)
    (hp : ∀ C, f C = x * g (p C)) : m * (∑ C, f C) = x * (m * ∑ C, g C) := by
  simp_rw [hp]; rw [← Finset.mul_sum, Equiv.sum_comp p g, mul_left_comm]

theorem main : H1 → H2 → OMA.R_ERH_extended_riemann_hypothesis_R1_H1_R1_H2_R1.H2 := by
  intro h1 h2 K _ _ hd f c x hx
  have hx' := zero_lt_one.trans_le hx
  obtain ⟨p, hp⟩ := h2 K hd
  rw [h1 K hd (1 / x) (one_div_pos.mpr hx'), h1 K hd x hx']
  exact sum_reciprocal p x _ (fun C => hp C x hx')

end OMA.R_ERH_extended_riemann_hypothesis_R1_H1_R1_H2_R1_H2_R1
