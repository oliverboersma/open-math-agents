import OMAReductions.R_RiemannHypothesis_beurling_nyman_criterion_R1
import Mathlib

/-! A closed linear space containing all initial interval indicators is all
of real L². Orthogonality converts membership into vanishing interval integrals;
the pi-lambda theorem and uniqueness of an integrable density finish. -/
-- Credit: @marcusbuffett
namespace OMA.R_RiemannHypothesis_beurling_nyman_criterion_R1_H1_R1
open MeasureTheory Set Filter RiemannHypothesis
open scoped RealInnerProductSpace

/-- Approximation of the single constant by the constrained fractional-part sums. -/
def H1 : Prop := RiemannHypothesis →
  indicatorConstLp 2 MeasurableSet.univ (measure_ne_top (volume.restrict (Ioc (0:ℝ) 1)) univ)
    (1:ℝ) ∈ closure { RiemannHypothesis.fractScalarInvSumL2 n c θ | (n) (c) (θ)
      (hθ : ∀ ν, θ ν ∈ Set.Ioc 0 1) (h : ∑ ν, c ν * θ ν = 0) }

/-- Dilation of an approximation of one gives each initial-interval indicator. -/
def H2 : Prop :=
  let μ := volume.restrict (Ioc (0:ℝ) 1)
  let S := { RiemannHypothesis.fractScalarInvSumL2 n c θ | (n) (c) (θ)
      (hθ : ∀ ν, θ ν ∈ Set.Ioc 0 1) (h : ∑ ν, c ν * θ ν = 0) }
  indicatorConstLp 2 MeasurableSet.univ (measure_ne_top μ univ) (1:ℝ) ∈ closure S →
  ∀ a : ℝ, indicatorConstLp 2 measurableSet_Iic (measure_ne_top μ (Iic a)) (1:ℝ) ∈ closure S

lemma dense_Iic {μ : Measure ℝ} [IsFiniteMeasure μ] (V : Submodule ℝ (Lp ℝ 2 μ))
    (one : indicatorConstLp 2 MeasurableSet.univ (measure_ne_top μ univ) (1:ℝ) ∈ V.topologicalClosure)
    (rays : ∀ t : ℝ, indicatorConstLp 2 measurableSet_Iic (measure_ne_top μ (Iic t)) (1:ℝ) ∈ V.topologicalClosure) :
    Dense (V : Set (Lp ℝ 2 μ)) := by
  have zero : Vᗮ = ⊥ := by
    apply bot_unique
    intro f fin
    have orth : f ∈ V.topologicalClosureᗮ := by rwa [Submodule.orthogonal_closure]
    have int : Integrable f μ := (Lp.memLp f).integrable (by norm_num)
    have whole := orth _ one
    rw [L2.inner_indicatorConstLp_one,Measure.restrict_univ] at whole
    have ray (t : ℝ) : ∫ x in Iic t, f x ∂μ=0 := by
      rw [←L2.inner_indicatorConstLp_one measurableSet_Iic (measure_ne_top μ _) f]
      exact orth _ (rays t)
    have all (s : Set ℝ) (ms : MeasurableSet s) : ∫ x in s,f x ∂μ=0 := by
      induction s,ms using MeasurableSpace.induction_on_inter (borel_eq_generateFrom_Iic (α := ℝ)) isPiSystem_Iic with
      | empty => simp
      | basic s h => obtain ⟨t,rfl⟩ := h; exact ray t
      | compl s ms ih =>
        have e := integral_add_compl ms int
        rw [ih,whole] at e
        simpa using e
      | iUnion f d m ih => rw [integral_iUnion m d int.integrableOn]; simp [ih]
    have he := int.ae_eq_zero_of_forall_setIntegral_eq_zero (fun s hs _ => all s hs)
    apply Lp.ext
    exact he.trans (Lp.coeFn_zero ℝ 2 μ).symm
  have htop : V.topologicalClosure=⊤ := by
    rw [←V.orthogonal_orthogonal_eq_closure,zero,Submodule.bot_orthogonal_eq_top]
  exact dense_iff_closure_eq.mpr (by rw [←Submodule.topologicalClosure_coe,htop]; rfl)

lemma sums_subspace :
    ∃ V : Submodule ℝ (Lp ℝ 2 (volume.restrict (Ioc (0:ℝ) 1))),
      (V : Set _) = { RiemannHypothesis.fractScalarInvSumL2 n c θ | (n) (c) (θ)
      (hθ : ∀ ν, θ ν ∈ Set.Ioc 0 1) (h : ∑ ν, c ν * θ ν = 0) } := by
  refine ⟨{ carrier := _
            zero_mem' := ?_
            add_mem' := ?_
            smul_mem' := ?_ },rfl⟩
  · rintro f g ⟨n,c,t,ht,hc,rfl⟩ ⟨m,d,u,hu,hd,rfl⟩
    refine ⟨n+m,Fin.append c d,Fin.append t u,?_,?_,?_⟩
    · intro i
      exact Fin.addCases (fun j => by simpa using ht j) (fun j => by simpa using hu j) i
    · simpa only [Fin.sum_univ_add,Fin.append_left,Fin.append_right,hc,hd,add_zero]
    · simp [fractScalarInvSumL2,Fin.sum_univ_add]
  · refine ⟨0,Fin.elim0,Fin.elim0,(fun i => Fin.elim0 i),by simp,?_⟩
    simp [fractScalarInvSumL2]
  · rintro k f ⟨n,c,t,ht,hc,rfl⟩
    refine ⟨n,fun i => k*c i,t,ht,?_,?_⟩
    · simp only [mul_assoc,←Finset.mul_sum,hc,mul_zero]
    · simp [fractScalarInvSumL2,Finset.smul_sum,mul_smul]

theorem main : H1 → H2 → OMA.R_RiemannHypothesis_beurling_nyman_criterion_R1.H1 := by
  intro approx dilate rh
  have one := approx rh
  have rays := dilate one
  obtain ⟨V,eq⟩ := sums_subspace
  rw [←eq] at one rays ⊢
  exact dense_Iic V one rays

end OMA.R_RiemannHypothesis_beurling_nyman_criterion_R1_H1_R1

