import FormalConjectures.Wikipedia.Transcendental
import Mathlib

/-!
# Euler's constant and the exponential integral at minus one

Rivoal, Michigan Mathematical Journal 61 (2012), equation (2.2) and
Section 5(ii), reduces the assertion to the independence of two E-values.
The constant in this checkout is the negative of the usual positive
Gompertz constant. Consequently the series E(-1) is the formal Gompertz
constant times exp(-1), minus Euler's constant.

We identify the logarithmic integral on the positive half-line with the
Gamma derivative at one. Integration by parts identifies its tail with
the integral defining the formal constant. The analytic hypothesis only
concerns a convergent series on the unit interval. For the algebraic step
we extend scalars to the field of real algebraic numbers. If both
constants were algebraic, E(-1) would lie in the subalgebra generated
by exp(-1) over that field. Credit: @ZedingZhang.
-/

namespace OMA.R_Transcendental_transcendental_eulerMascheroniConstant_or_gompertzConstant_R1

open Filter Set Real MeasureTheory
open scoped Topology

private lemma log_moment :
    (∫ t : ℝ in Ioi 0, log t * exp (-t)) = -eulerMascheroniConstant := by
  have positive : Complex.Gamma =ᶠ[𝓝 (1:ℂ)] Complex.GammaIntegral := by
    have op : IsOpen {s : ℂ | 0 < s.re} := isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [op.mem_nhds (show (1:ℂ) ∈ {s : ℂ | 0 < s.re} by norm_num)] with s hs
    exact Complex.Gamma_eq_integral hs
  have hd := (Complex.hasDerivAt_GammaIntegral (s := (1:ℂ)) (by norm_num)).congr_of_eventuallyEq positive
  have eqn := hd.unique Complex.hasDerivAt_Gamma_one
  apply Complex.ofReal_injective
  simpa only [sub_self, Complex.cpow_zero, one_mul, ← Complex.ofReal_mul, integral_complex_ofReal,
    Complex.ofReal_neg] using eqn

private lemma tail_integral
    (integ : IntegrableOn (fun t : ℝ => log t * exp (-t)) (Ioi 1)) :
    (∫ t : ℝ in Ioi 1, log t * exp (-t)) = ∫ t : ℝ in Ioi 1, exp (-t)/t := by
  have tail : IntegrableOn (fun t : ℝ => exp (-t)/t) (Ioi 1) := by
    refine (integrableOn_exp_neg_Ioi 1).mono'
      ((Real.measurable_exp.comp measurable_neg).div measurable_id).aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with t ht
    have h : (1:ℝ) < t := ht
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (exp_pos _).le (by linarith))]
    exact div_le_self (exp_pos _).le h.le
  have hu (t : ℝ) (ht : t ∈ Ioi (1:ℝ)) : HasDerivAt log t⁻¹ t :=
    hasDerivAt_log (by have h : 1 < t := ht; linarith)
  have hv (t : ℝ) (_ht : t ∈ Ioi (1:ℝ)) :
      HasDerivAt (fun x : ℝ => exp (-x)) (-exp (-t)) t := by
    simpa only [mul_neg_one] using (hasDerivAt_neg t).exp
  have atOne : Tendsto (fun t : ℝ => log t * exp (-t)) (𝓝[>] 1) (𝓝 0) := by
    have hc : ContinuousAt (fun t : ℝ => log t * exp (-t)) 1 := by fun_prop (disch := norm_num)
    have hh : Tendsto (fun t : ℝ => log t * exp (-t)) (𝓝[>] 1) (𝓝 (log 1 * exp (-1))) :=
      hc.continuousWithinAt (s := Ioi 1)
    simpa only [log_one, zero_mul] using hh
  have atInf : Tendsto (fun t : ℝ => log t * exp (-t)) atTop (𝓝 0) := by
    apply squeeze_zero' (g := fun t : ℝ => t * exp (-t))
    · filter_upwards [eventually_ge_atTop (1:ℝ)] with t ht
      exact mul_nonneg (log_nonneg ht) (exp_pos _).le
    · filter_upwards [eventually_ge_atTop (1:ℝ)] with t ht
      exact mul_le_mul_of_nonneg_right ((log_le_sub_one_of_pos (by linarith)).trans (by linarith))
        (exp_pos _).le
    · simpa using tendsto_pow_mul_exp_neg_atTop_nhds_zero 1
  have hleft : IntegrableOn (fun t : ℝ => log t * -exp (-t)) (Ioi 1) := by
    simpa only [Pi.neg_def, mul_neg] using integ.neg
  have hright : IntegrableOn (fun t : ℝ => t⁻¹ * exp (-t)) (Ioi 1) := by
    simpa only [div_eq_mul_inv, mul_comm] using tail
  have eqn := integral_Ioi_mul_deriv_eq_deriv_mul hu hv hleft hright atOne atInf
  have tailEq : (∫ t : ℝ in Ioi 1, log t * exp (-t)) =
      ∫ t : ℝ in Ioi 1, t⁻¹ * exp (-t) := by
    simpa only [mul_neg, integral_neg, sub_self, zero_sub, neg_inj] using eqn
  simpa only [div_eq_mul_inv, mul_comm] using tailEq

private lemma interval_relation :
    (∫ t : ℝ in Ioc 0 1, log t * exp (-t)) =
      gompertzConstant * exp (-1) - eulerMascheroniConstant := by
  have integ : IntegrableOn (fun t : ℝ => log t * exp (-t)) (Ioi 0) := by
    by_contra h
    have eqn := log_moment
    rw [integral_undef h] at eqn
    linarith [Real.one_half_lt_eulerMascheroniConstant]
  have hi := integ.mono_set (show Ioc (0:ℝ) 1 ⊆ Ioi 0 from fun _ h => h.1)
  have ht := integ.mono_set (Ioi_subset_Ioi (show (0:ℝ) ≤ 1 by norm_num))
  have split := setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi hi ht
  rw [Ioc_union_Ioi_eq_Ioi (by norm_num : (0:ℝ) ≤ 1), log_moment, tail_integral ht] at split
  have cancel : exp 1 * exp (-1) = 1 := by rw [← exp_add]; norm_num
  unfold gompertzConstant
  linarith [show (-(exp 1) * (∫ t : ℝ in Ioi 1, exp (-t)/t)) * exp (-1) =
      -(∫ t : ℝ in Ioi 1, exp (-t)/t) by
    calc
      _ = -(exp 1 * exp (-1)) * (∫ t : ℝ in Ioi 1, exp (-t)/t) := by ring
      _ = _ := by rw [cancel]; ring]

private lemma affine_obstruction {a g z y : ℝ}
    (ind : AlgebraicIndependent ℚ (fun b : Bool => if b then y else z))
    (affine : y = g*z-a) : Transcendental ℚ a ∨ Transcendental ℚ g := by
  classical
  by_cases ha : IsAlgebraic ℚ a
  · right
    intro hg
    let K := algebraicClosure ℚ ℝ
    let v (b : Bool) := if b then y else z
    let A := Algebra.adjoin K (v '' ({false} : Set Bool))
    have independent : AlgebraicIndependent K v := ind.algebraicClosure
    have trans := independent.transcendental_adjoin (s := ({false} : Set Bool))
      (i := true) (by simp)
    have az : z ∈ A := Algebra.subset_adjoin ⟨false, by simp, rfl⟩
    have aa : a ∈ A := A.algebraMap_mem (⟨a, mem_algebraicClosure_iff.mpr ha⟩ : K)
    have ag : g ∈ A := A.algebraMap_mem (⟨g, mem_algebraicClosure_iff.mpr hg⟩ : K)
    have ay : y ∈ A := by rw [affine]; exact A.sub_mem (A.mul_mem ag az) aa
    exact trans (isAlgebraic_algebraMap (⟨y,ay⟩ : A))
  · exact Or.inl ha

/-- The integrated exponential series at minus one. -/
def H1 : Prop :=
  HasSum (fun n : ℕ => (-1:ℝ)^(n+1) / (((n:ℝ)+1) * ((n+1).factorial:ℝ)))
    (∫ t : ℝ in Ioc 0 1, log t * exp (-t))

/-- Rivoal's E-function value and exp(-1) are algebraically independent. -/
def H2 : Prop :=
  let y : ℝ := ∑' n : ℕ, (-1:ℝ)^(n+1) / (((n:ℝ)+1) * ((n+1).factorial:ℝ))
  AlgebraicIndependent ℚ (fun b : Bool => if b then y else exp (-1))

theorem main : H1 → H2 → type_of% @Transcendental.transcendental_eulerMascheroniConstant_or_gompertzConstant := by
  intro series ind
  exact affine_obstruction ind (series.tsum_eq.trans interval_relation)

end OMA.R_Transcendental_transcendental_eulerMascheroniConstant_or_gompertzConstant_R1
