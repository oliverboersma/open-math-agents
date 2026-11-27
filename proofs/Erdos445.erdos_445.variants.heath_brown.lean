import FormalConjectures.ErdosProblems.«445»
import Mathlib

/-!
# Inverse pairs in intervals of length p^c for c > 3/4

The prime-field Kloosterman estimate below is adapted from the rational Weil
and Stepanov developments in Boris Alexeev’s plby/lean-proofs, revision
8822f7ddef30fadbd92e1c6ab4ed897af356af5e, ErdosProblems/Erdos387 and
Waring/Analytic (formal authors credited there: Codex and GPT-5.6 Sol).
The smoothed interval count is adapted from Noah Puckett's
Heilbronn proof (open-math-agents PR 2351). We account for the term at zero
when passing to the unit Kloosterman sum. Its square-root bound makes the
Fourier main term dominate as soon as the interval length exceeds a constant
times p^(3/4), uniformly in the starting point.
-/

/-! ## ErdosProblems.Erdos387.AdditiveCharacterOrthogonality -/

noncomputable section

namespace Erdos387

open scoped BigOperators ComplexConjugate

namespace AdditiveOrthogonality

theorem sum_stdAddChar_mul (q : ℕ) [NeZero q] (x : ZMod q) :
    ∑ u : ZMod q, ZMod.stdAddChar (u * x) =
      if x = 0 then (q : ℂ) else 0 := by
  simpa using
    (AddChar.sum_mulShift x (ZMod.isPrimitive_stdAddChar q))

section Fibres

variable {q : ℕ}

variable {A : Type*}

noncomputable def stdAddCharFourierSum
    [NeZero q] (F : ZMod q → ℂ) (u : ZMod q) : ℂ :=
  ∑ v : ZMod q, F v * ZMod.stdAddChar (u * v)

end Fibres

end AdditiveOrthogonality

end Erdos387

end

/-! ## ErdosProblems.Erdos387.KloostermanOrthogonality -/

noncomputable section

namespace Erdos387

open scoped BigOperators

namespace Kloosterman

noncomputable def coefficient
    (q : ℕ) [NeZero q] (b v : ZMod q) : ℂ :=
  if IsUnit v then ZMod.stdAddChar (b * v⁻¹) else 0

noncomputable def sum
    (q : ℕ) [NeZero q] (a b : ZMod q) : ℂ :=
  AdditiveOrthogonality.stdAddCharFourierSum (coefficient q b) a

theorem sum_eq_inverse_phase
    (q : ℕ) [NeZero q] (a b : ZMod q) :
    sum q a b =
      ∑ v : ZMod q,
        if IsUnit v then
          ZMod.stdAddChar (a * v + b * v⁻¹)
        else 0 := by
  classical
  unfold Kloosterman.sum AdditiveOrthogonality.stdAddCharFourierSum
  apply Finset.sum_congr rfl
  intro v _hv
  by_cases hv : IsUnit v
  · simp only [coefficient, if_pos hv]
    rw [AddChar.map_add_eq_mul]
    ring
  · simp [coefficient, hv]

end Kloosterman

end Erdos387

end

/-! ## Waring.Analytic.Basic -/

noncomputable section

namespace Waring.Analytic

open scoped BigOperators

theorem norm_stdAddChar (q : Nat) [NeZero q] (x : ZMod q) :
    ‖ZMod.stdAddChar x‖ = 1 := by
  rw [ZMod.stdAddChar_apply]
  exact Circle.norm_coe _

theorem sum_stdAddChar_mul {q : Nat} [NeZero q] (a : ZMod q) :
    ∑ x : ZMod q, ZMod.stdAddChar (x * a) = if a = 0 then q else 0 := by
  simpa using AddChar.sum_mulShift a (ZMod.isPrimitive_stdAddChar q)

end Waring.Analytic

end

/-! ## ErdosProblems.Erdos387.PoleTranslation -/

noncomputable section

namespace Erdos387

namespace InverseRational

noncomputable def poleSupport
    {p : ℕ} [NeZero p] (coeff : ZMod p → ZMod p) :
    Finset (ZMod p) := by
  classical
  exact Finset.univ.filter fun r => coeff r ≠ 0

@[simp] theorem mem_poleSupport
    {p : ℕ} [NeZero p] (coeff : ZMod p → ZMod p) (r : ZMod p) :
    r ∈ poleSupport coeff ↔ coeff r ≠ 0 := by
  simp [poleSupport]

noncomputable def simplePolePhase
    {p : ℕ} [NeZero p] (coeff : ZMod p → ZMod p) (x : ZMod p) :
    ZMod p :=
  ∑ r : ZMod p, coeff r * (x - r)⁻¹

end InverseRational

end Erdos387

end

/-! ## ErdosProblems.Erdos387.ArtinSchreierObstruction -/

noncomputable section

namespace Erdos387

open Polynomial

namespace InverseRational

noncomputable def simplePoleDenominatorPolynomial
    {p : ℕ} [NeZero p] (coeff : ZMod p → ZMod p) : (ZMod p)[X] :=
  ∏ r ∈ poleSupport coeff, (X - C r)

noncomputable def simplePoleNumeratorPolynomial
    {p : ℕ} [NeZero p] (coeff : ZMod p → ZMod p) : (ZMod p)[X] :=
  ∑ r ∈ poleSupport coeff,
    C (coeff r) * ∏ s ∈ (poleSupport coeff).erase r, (X - C s)

theorem monic_simplePoleDenominatorPolynomial
    {p : ℕ} [NeZero p] (coeff : ZMod p → ZMod p) :
    (simplePoleDenominatorPolynomial coeff).Monic := by
  exact monic_prod_X_sub_C (fun r : ZMod p => r) (poleSupport coeff)

theorem natDegree_simplePoleDenominatorPolynomial
    {p : ℕ} [NeZero p] [Fact p.Prime] (coeff : ZMod p → ZMod p) :
    (simplePoleDenominatorPolynomial coeff).natDegree =
      (poleSupport coeff).card := by
  exact natDegree_finsetProd_X_sub_C_eq_card
    (poleSupport coeff) (fun r : ZMod p => r)

theorem simplePolePhase_eq_sum_poleSupport
    {p : ℕ} [NeZero p] (coeff : ZMod p → ZMod p) (x : ZMod p) :
    simplePolePhase coeff x =
      ∑ r ∈ poleSupport coeff, coeff r * (x - r)⁻¹ := by
  classical
  unfold simplePolePhase
  apply (Finset.sum_subset (Finset.subset_univ (poleSupport coeff)) ?_).symm
  intro r _hrUniv hrSupport
  have hcoeff : coeff r = 0 := by
    simpa only [mem_poleSupport, not_ne_iff] using hrSupport
  simp only [hcoeff, zero_mul]

theorem simplePoleDenominatorPolynomial_eq_mul_erase
    {p : ℕ} [NeZero p] (coeff : ZMod p → ZMod p)
    {r : ZMod p} (hr : r ∈ poleSupport coeff) :
    simplePoleDenominatorPolynomial coeff =
      (X - C r) * ∏ s ∈ (poleSupport coeff).erase r, (X - C s) := by
  exact (Finset.mul_prod_erase (poleSupport coeff)
    (fun s : ZMod p => X - C s) hr).symm

theorem eval_simplePoleComplement_ne_zero
    {p : ℕ} [NeZero p] [Fact p.Prime] (coeff : ZMod p → ZMod p)
    {r : ZMod p} (_hr : r ∈ poleSupport coeff) :
    eval r (∏ s ∈ (poleSupport coeff).erase r, (X - C s)) ≠ 0 := by
  rw [eval_prod, Finset.prod_ne_zero_iff]
  intro s hs
  simp only [eval_sub, eval_X, eval_C, sub_ne_zero]
  exact (Finset.ne_of_mem_erase hs).symm

theorem eval_simplePoleNumeratorPolynomial
    {p : ℕ} [NeZero p] [Fact p.Prime] (coeff : ZMod p → ZMod p)
    {r : ZMod p} (hr : r ∈ poleSupport coeff) :
    eval r (simplePoleNumeratorPolynomial coeff) =
      coeff r *
        eval r (∏ s ∈ (poleSupport coeff).erase r, (X - C s)) := by
  classical
  rw [simplePoleNumeratorPolynomial, eval_finsetSum]
  rw [Finset.sum_eq_single r]
  · simp only [eval_mul, eval_C]
  · intro s hs hsr
    have hrs : r ∈ (poleSupport coeff).erase s :=
      Finset.mem_erase.mpr ⟨hsr.symm, hr⟩
    have hprod :
        eval r (∏ t ∈ (poleSupport coeff).erase s, (X - C t)) = 0 := by
      rw [eval_prod]
      exact Finset.prod_eq_zero hrs (by simp)
    simp only [eval_mul, eval_C, hprod, mul_zero]
  · exact fun hnot => (hnot hr).elim

theorem eval_simplePoleNumeratorPolynomial_ne_zero
    {p : ℕ} [NeZero p] [Fact p.Prime] (coeff : ZMod p → ZMod p)
    {r : ZMod p} (hr : r ∈ poleSupport coeff) :
    eval r (simplePoleNumeratorPolynomial coeff) ≠ 0 := by
  rw [eval_simplePoleNumeratorPolynomial coeff hr]
  exact mul_ne_zero ((mem_poleSupport coeff r).mp hr)
    (eval_simplePoleComplement_ne_zero coeff hr)

end InverseRational

end Erdos387

end

/-! ## ErdosProblems.Erdos387.RationalWeilWeight -/

noncomputable section

namespace Erdos387

open Polynomial

namespace RationalWeil

def AvoidsPoleSupport
    {p : ℕ} [NeZero p] (coeff : ZMod p → ZMod p)
    (F : (ZMod p)[X]) : Prop :=
  ∀ r ∈ InverseRational.poleSupport coeff, eval r F ≠ 0

noncomputable def logarithmicDerivativePhase
    {p : ℕ} [NeZero p] (coeff : ZMod p → ZMod p)
    (F : (ZMod p)[X]) : ZMod p :=
  -∑ r ∈ InverseRational.poleSupport coeff,
    coeff r * eval r F.derivative * (eval r F)⁻¹

noncomputable def polynomialWeight
    {p : ℕ} [NeZero p] (coeff : ZMod p → ZMod p)
    (F : (ZMod p)[X]) : ℂ := by
  classical
  exact if AvoidsPoleSupport coeff F then
    ZMod.stdAddChar (logarithmicDerivativePhase coeff F)
  else 0

theorem avoidsPoleSupport_mul_iff
    {p : ℕ} [NeZero p] [Fact p.Prime]
    (coeff : ZMod p → ZMod p) (F G : (ZMod p)[X]) :
    AvoidsPoleSupport coeff (F * G) ↔
      AvoidsPoleSupport coeff F ∧ AvoidsPoleSupport coeff G := by
  simp only [AvoidsPoleSupport, eval_mul, mul_ne_zero_iff, forall_and]

theorem logarithmicDerivativePhase_mul
    {p : ℕ} [NeZero p] [Fact p.Prime]
    (coeff : ZMod p → ZMod p) {F G : (ZMod p)[X]}
    (hF : AvoidsPoleSupport coeff F)
    (hG : AvoidsPoleSupport coeff G) :
    logarithmicDerivativePhase coeff (F * G) =
      logarithmicDerivativePhase coeff F +
        logarithmicDerivativePhase coeff G := by
  classical
  simp only [logarithmicDerivativePhase, derivative_mul, eval_add, eval_mul]
  rw [← neg_add, ← Finset.sum_add_distrib]
  apply congrArg Neg.neg
  apply Finset.sum_congr rfl
  intro r hr
  have hFr := hF r hr
  have hGr := hG r hr
  field_simp [hFr, hGr]

theorem polynomialWeight_mul
    {p : ℕ} [NeZero p] [Fact p.Prime]
    (coeff : ZMod p → ZMod p) (F G : (ZMod p)[X]) :
    polynomialWeight coeff (F * G) =
      polynomialWeight coeff F * polynomialWeight coeff G := by
  classical
  by_cases hF : AvoidsPoleSupport coeff F
  · by_cases hG : AvoidsPoleSupport coeff G
    · rw [polynomialWeight, polynomialWeight, polynomialWeight,
        if_pos hF, if_pos hG,
        if_pos ((avoidsPoleSupport_mul_iff coeff F G).2 ⟨hF, hG⟩),
        logarithmicDerivativePhase_mul coeff hF hG,
        AddChar.map_add_eq_mul]
    · have hFG : ¬AvoidsPoleSupport coeff (F * G) := by
        exact fun h => hG ((avoidsPoleSupport_mul_iff coeff F G).1 h).2
      simp only [polynomialWeight, hF, hG, hFG, if_true, if_false, mul_zero]
  · have hFG : ¬AvoidsPoleSupport coeff (F * G) := by
      exact fun h => hF ((avoidsPoleSupport_mul_iff coeff F G).1 h).1
    simp only [polynomialWeight, hF, hFG, if_false, zero_mul]

theorem avoidsPoleSupport_X_sub_C_iff
    {p : ℕ} [NeZero p] [Fact p.Prime]
    (coeff : ZMod p → ZMod p) (x : ZMod p) :
    AvoidsPoleSupport coeff (X - C x) ↔
      x ∉ InverseRational.poleSupport coeff := by
  constructor
  · intro h hx
    exact h x hx (by simp)
  · intro hx r hr
    simp only [eval_sub, eval_X, eval_C, sub_ne_zero]
    intro hrx
    apply hx
    subst r
    exact hr

theorem polynomialWeight_X_sub_C_of_mem
    {p : ℕ} [NeZero p] [Fact p.Prime]
    (coeff : ZMod p → ZMod p) {x : ZMod p}
    (hx : x ∈ InverseRational.poleSupport coeff) :
    polynomialWeight coeff (X - C x) = 0 := by
  rw [polynomialWeight, if_neg]
  exact fun h => ((avoidsPoleSupport_X_sub_C_iff coeff x).1 h) hx

end RationalWeil

end Erdos387

end

/-! ## ErdosProblems.Erdos387.RationalWeilProbe -/

noncomputable section

namespace Erdos387

open Polynomial

namespace RationalWeil

noncomputable def poleComplementPolynomial
    {p : ℕ} [NeZero p] (coeff : ZMod p → ZMod p) (r : ZMod p) :
    (ZMod p)[X] :=
  ∏ s ∈ (InverseRational.poleSupport coeff).erase r, (X - C s)

noncomputable def derivativeProbe
    {p : ℕ} [NeZero p] (coeff : ZMod p → ZMod p) (r : ZMod p) :
    (ZMod p)[X] :=
  InverseRational.simplePoleDenominatorPolynomial coeff *
    poleComplementPolynomial coeff r

theorem monic_poleComplementPolynomial
    {p : ℕ} [NeZero p] (coeff : ZMod p → ZMod p) (r : ZMod p) :
    (poleComplementPolynomial coeff r).Monic := by
  exact monic_prod_X_sub_C (fun s : ZMod p => s)
    ((InverseRational.poleSupport coeff).erase r)

theorem monic_derivativeProbe
    {p : ℕ} [NeZero p] (coeff : ZMod p → ZMod p) (r : ZMod p) :
    (derivativeProbe coeff r).Monic := by
  exact (InverseRational.monic_simplePoleDenominatorPolynomial coeff).mul
    (monic_poleComplementPolynomial coeff r)

theorem derivativeProbe_eq_linear_mul_complement_sq
    {p : ℕ} [NeZero p] (coeff : ZMod p → ZMod p)
    {r : ZMod p} (hr : r ∈ InverseRational.poleSupport coeff) :
    derivativeProbe coeff r =
      (X - C r) * (poleComplementPolynomial coeff r) ^ 2 := by
  rw [derivativeProbe,
    InverseRational.simplePoleDenominatorPolynomial_eq_mul_erase coeff hr]
  unfold poleComplementPolynomial
  ring

theorem eval_derivativeProbe_eq_zero
    {p : ℕ} [NeZero p] [Fact p.Prime]
    (coeff : ZMod p → ZMod p) (r : ZMod p)
    {s : ZMod p} (hs : s ∈ InverseRational.poleSupport coeff) :
    eval s (derivativeProbe coeff r) = 0 := by
  rw [derivativeProbe, eval_mul]
  have hden :
      eval s (InverseRational.simplePoleDenominatorPolynomial coeff) = 0 := by
    rw [InverseRational.simplePoleDenominatorPolynomial_eq_mul_erase coeff hs,
      eval_mul]
    simp
  rw [hden, zero_mul]

theorem eval_derivative_derivativeProbe_at_selected
    {p : ℕ} [NeZero p] [Fact p.Prime]
    (coeff : ZMod p → ZMod p) {r : ZMod p}
    (hr : r ∈ InverseRational.poleSupport coeff) :
    eval r (derivativeProbe coeff r).derivative =
      eval r (poleComplementPolynomial coeff r) ^ 2 := by
  rw [derivativeProbe_eq_linear_mul_complement_sq coeff hr,
    derivative_mul, eval_add, eval_mul, eval_mul]
  simp

theorem eval_derivative_derivativeProbe_at_selected_ne_zero
    {p : ℕ} [NeZero p] [Fact p.Prime]
    (coeff : ZMod p → ZMod p) {r : ZMod p}
    (hr : r ∈ InverseRational.poleSupport coeff) :
    eval r (derivativeProbe coeff r).derivative ≠ 0 := by
  rw [eval_derivative_derivativeProbe_at_selected coeff hr]
  exact pow_ne_zero 2
    (InverseRational.eval_simplePoleComplement_ne_zero coeff hr)

theorem eval_derivative_derivativeProbe_at_other
    {p : ℕ} [NeZero p] [Fact p.Prime]
    (coeff : ZMod p → ZMod p) {r s : ZMod p}
    (hr : r ∈ InverseRational.poleSupport coeff)
    (hs : s ∈ InverseRational.poleSupport coeff) (hsr : s ≠ r) :
    eval s (derivativeProbe coeff r).derivative = 0 := by
  rw [derivativeProbe_eq_linear_mul_complement_sq coeff hr,
    derivative_mul, eval_add, eval_mul, eval_mul]
  have hscomp : s ∈ (InverseRational.poleSupport coeff).erase r :=
    Finset.mem_erase.mpr ⟨hsr, hs⟩
  have hcomp : eval s (poleComplementPolynomial coeff r) = 0 := by
    rw [poleComplementPolynomial, eval_prod]
    exact Finset.prod_eq_zero hscomp (by simp)
  simp [derivative_pow, eval_pow, eval_mul, hcomp]

theorem eval_add_C_mul_derivativeProbe
    {p : ℕ} [NeZero p] [Fact p.Prime]
    (coeff : ZMod p → ZMod p) (r t : ZMod p) (F : (ZMod p)[X])
    {s : ZMod p} (hs : s ∈ InverseRational.poleSupport coeff) :
    eval s (F + C t * derivativeProbe coeff r) = eval s F := by
  rw [eval_add, eval_mul, eval_C, eval_derivativeProbe_eq_zero coeff r hs,
    mul_zero, add_zero]

theorem avoidsPoleSupport_add_C_mul_derivativeProbe_iff
    {p : ℕ} [NeZero p] [Fact p.Prime]
    (coeff : ZMod p → ZMod p) (r t : ZMod p) (F : (ZMod p)[X]) :
    AvoidsPoleSupport coeff (F + C t * derivativeProbe coeff r) ↔
      AvoidsPoleSupport coeff F := by
  simp only [AvoidsPoleSupport]
  constructor <;> intro h s hs
  · simpa only [eval_add_C_mul_derivativeProbe coeff r t F hs] using h s hs
  · simpa only [eval_add_C_mul_derivativeProbe coeff r t F hs] using h s hs

theorem natDegree_derivativeProbe
    {p : ℕ} [NeZero p] [Fact p.Prime]
    (coeff : ZMod p → ZMod p) {r : ZMod p}
    (hr : r ∈ InverseRational.poleSupport coeff) :
    (derivativeProbe coeff r).natDegree =
      2 * (InverseRational.poleSupport coeff).card - 1 := by
  rw [derivativeProbe, Polynomial.Monic.natDegree_mul
    (InverseRational.monic_simplePoleDenominatorPolynomial coeff)
    (monic_poleComplementPolynomial coeff r),
    InverseRational.natDegree_simplePoleDenominatorPolynomial,
    show (poleComplementPolynomial coeff r).natDegree =
        ((InverseRational.poleSupport coeff).erase r).card by
      exact natDegree_finsetProd_X_sub_C_eq_card
        ((InverseRational.poleSupport coeff).erase r)
        (fun s : ZMod p => s),
    Finset.card_erase_of_mem hr]
  omega

end RationalWeil

end Erdos387

end

/-! ## ErdosProblems.Erdos387.RationalArtinCancellation -/

noncomputable section

namespace Erdos387

open Polynomial

open scoped BigOperators

namespace RationalWeil

noncomputable def probeSlope
    {p : ℕ} [NeZero p] (coeff : ZMod p → ZMod p)
    (F : (ZMod p)[X]) (r : ZMod p) : ZMod p :=
  -(coeff r * eval r (derivativeProbe coeff r).derivative *
      (eval r F)⁻¹)

theorem logarithmicDerivativePhase_add_of_eval_eq_zero
    {p : ℕ} [NeZero p] [Fact p.Prime]
    (coeff : ZMod p → ZMod p) (F G : (ZMod p)[X])
    (hG : ∀ s ∈ InverseRational.poleSupport coeff, eval s G = 0) :
    logarithmicDerivativePhase coeff (F + G) =
      logarithmicDerivativePhase coeff F -
        ∑ s ∈ InverseRational.poleSupport coeff,
          coeff s * eval s G.derivative * (eval s F)⁻¹ := by
  classical
  simp only [logarithmicDerivativePhase, derivative_add, eval_add]
  have hsum :
      (∑ s ∈ InverseRational.poleSupport coeff,
          coeff s * (eval s F.derivative + eval s G.derivative) *
            (eval s F + eval s G)⁻¹) =
        (∑ s ∈ InverseRational.poleSupport coeff,
          coeff s * eval s F.derivative * (eval s F)⁻¹) +
        ∑ s ∈ InverseRational.poleSupport coeff,
          coeff s * eval s G.derivative * (eval s F)⁻¹ := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro s hs
    rw [hG s hs, add_zero]
    ring
  rw [hsum]
  ring

theorem logarithmicDerivativePhase_add_probe
    {p : ℕ} [NeZero p] [Fact p.Prime]
    (coeff : ZMod p → ZMod p) (F : (ZMod p)[X])
    {r : ZMod p} (hr : r ∈ InverseRational.poleSupport coeff)
    (t : ZMod p) :
    logarithmicDerivativePhase coeff
        (F + C t * derivativeProbe coeff r) =
      logarithmicDerivativePhase coeff F + t * probeSlope coeff F r := by
  classical
  rw [logarithmicDerivativePhase_add_of_eval_eq_zero coeff F
    (C t * derivativeProbe coeff r) (by
      intro s hs
      simp [eval_derivativeProbe_eq_zero coeff r hs])]
  have hsum :
      (∑ s ∈ InverseRational.poleSupport coeff,
          coeff s * eval s (C t * derivativeProbe coeff r).derivative *
            (eval s F)⁻¹) =
        t * coeff r * eval r (derivativeProbe coeff r).derivative *
          (eval r F)⁻¹ := by
    rw [Finset.sum_eq_single r]
    · simp only [derivative_mul, derivative_C, zero_mul, zero_add,
        eval_mul, eval_C]
      ring
    · intro s hs hsr
      simp only [derivative_mul, derivative_C, zero_mul, zero_add,
        eval_mul, eval_C,
        eval_derivative_derivativeProbe_at_other coeff hr hs hsr,
        mul_zero, zero_mul]
    · exact fun hnot => (hnot hr).elim
  rw [hsum]
  unfold probeSlope
  ring

theorem probeSlope_ne_zero
    {p : ℕ} [NeZero p] [Fact p.Prime]
    (coeff : ZMod p → ZMod p) {F : (ZMod p)[X]} {r : ZMod p}
    (hr : r ∈ InverseRational.poleSupport coeff)
    (hF : AvoidsPoleSupport coeff F) :
    probeSlope coeff F r ≠ 0 := by
  unfold probeSlope
  exact neg_ne_zero.mpr <| mul_ne_zero
    (mul_ne_zero ((InverseRational.mem_poleSupport coeff r).mp hr)
      (eval_derivative_derivativeProbe_at_selected_ne_zero coeff hr))
    (inv_ne_zero (hF r hr))

theorem polynomialWeight_add_probe_of_avoids
    {p : ℕ} [NeZero p] [Fact p.Prime]
    (coeff : ZMod p → ZMod p) {F : (ZMod p)[X]} {r : ZMod p}
    (hr : r ∈ InverseRational.poleSupport coeff)
    (hF : AvoidsPoleSupport coeff F) (t : ZMod p) :
    polynomialWeight coeff (F + C t * derivativeProbe coeff r) =
      polynomialWeight coeff F * ZMod.stdAddChar (t * probeSlope coeff F r) := by
  classical
  rw [polynomialWeight, polynomialWeight,
    if_pos hF,
    if_pos ((avoidsPoleSupport_add_C_mul_derivativeProbe_iff
      coeff r t F).2 hF),
    logarithmicDerivativePhase_add_probe coeff F hr t,
    AddChar.map_add_eq_mul]

theorem sum_polynomialWeight_add_probe_eq_zero
    {p : ℕ} [NeZero p] [Fact p.Prime]
    (coeff : ZMod p → ZMod p) (F : (ZMod p)[X])
    {r : ZMod p} (hr : r ∈ InverseRational.poleSupport coeff) :
    ∑ t : ZMod p,
      polynomialWeight coeff (F + C t * derivativeProbe coeff r) = 0 := by
  classical
  by_cases hF : AvoidsPoleSupport coeff F
  · simp_rw [polynomialWeight_add_probe_of_avoids coeff hr hF]
    rw [← Finset.mul_sum,
      AdditiveOrthogonality.sum_stdAddChar_mul p (probeSlope coeff F r),
      if_neg (probeSlope_ne_zero coeff hr hF), mul_zero]
  · apply Finset.sum_eq_zero
    intro t _ht
    rw [polynomialWeight, if_neg]
    exact fun h => hF
      ((avoidsPoleSupport_add_C_mul_derivativeProbe_iff coeff r t F).1 h)

noncomputable def lowerPolynomial
    {K : Type*} [Field K] (n : ℕ) (c : Fin n → K) : K[X] :=
  ((degreeLTEquiv K n).symm c).1

noncomputable def monicPolynomial
    {K : Type*} [Field K] (n : ℕ) (c : Fin n → K) : K[X] :=
  X ^ n + lowerPolynomial n c

theorem lowerPolynomial_add
    {K : Type*} [Field K] (n : ℕ) (c d : Fin n → K) :
    lowerPolynomial n (c + d) =
      lowerPolynomial n c + lowerPolynomial n d := by
  change (((degreeLTEquiv K n).symm (c + d)).1 : K[X]) = _
  rw [map_add]
  rfl

theorem lowerPolynomial_smul
    {K : Type*} [Field K] (n : ℕ) (t : K) (c : Fin n → K) :
    lowerPolynomial n (t • c) = C t * lowerPolynomial n c := by
  change (((degreeLTEquiv K n).symm (t • c)).1 : K[X]) = _
  rw [map_smul]
  change t • lowerPolynomial n c = C t * lowerPolynomial n c
  exact smul_eq_C_mul t

noncomputable def lowerCoefficientVector
    {K : Type*} [Field K] (n : ℕ) (H : K[X])
    (hH : H ∈ degreeLT K n) : Fin n → K :=
  degreeLTEquiv K n ⟨H, hH⟩

theorem lowerPolynomial_lowerCoefficientVector
    {K : Type*} [Field K] (n : ℕ) (H : K[X])
    (hH : H ∈ degreeLT K n) :
    lowerPolynomial n (lowerCoefficientVector n H hH) = H := by
  change (((degreeLTEquiv K n).symm
    (degreeLTEquiv K n ⟨H, hH⟩)).1 : K[X]) = H
  rw [LinearEquiv.symm_apply_apply]

theorem monicPolynomial_add_smul_lowerCoefficientVector
    {K : Type*} [Field K] (n : ℕ) (c : Fin n → K)
    (t : K) (H : K[X]) (hH : H ∈ degreeLT K n) :
    monicPolynomial n
        (c + t • lowerCoefficientVector n H hH) =
      monicPolynomial n c + C t * H := by
  rw [monicPolynomial, monicPolynomial, lowerPolynomial_add,
    lowerPolynomial_smul,
    lowerPolynomial_lowerCoefficientVector n H hH]
  ring

theorem sum_polynomialWeight_monicPolynomial_eq_zero
    {p : ℕ} [NeZero p] [Fact p.Prime]
    (coeff : ZMod p → ZMod p) {n : ℕ}
    (hn : 2 * (InverseRational.poleSupport coeff).card ≤ n)
    (hne : (InverseRational.poleSupport coeff).Nonempty) :
    ∑ c : Fin n → ZMod p,
      polynomialWeight coeff (monicPolynomial n c) = 0 := by
  classical
  obtain ⟨r, hr⟩ := hne
  let H : (ZMod p)[X] := derivativeProbe coeff r
  have hmpos : 0 < (InverseRational.poleSupport coeff).card :=
    Finset.card_pos.mpr ⟨r, hr⟩
  have hHdegree : H.natDegree < n := by
    change (derivativeProbe coeff r).natDegree < n
    rw [natDegree_derivativeProbe coeff hr]
    omega
  have hH : H ∈ degreeLT (ZMod p) n := by
    rw [mem_degreeLT, ← natDegree_lt_iff_degree_lt
      (monic_derivativeProbe coeff r).ne_zero]
    exact hHdegree
  let v : Fin n → ZMod p := lowerCoefficientVector n H hH
  let w : (Fin n → ZMod p) → ℂ := fun c =>
    polynomialWeight coeff (monicPolynomial n c)
  have htranslate (t : ZMod p) :
      (∑ c : Fin n → ZMod p, w (c + t • v)) = ∑ c, w c := by
    let e : (Fin n → ZMod p) ≃ (Fin n → ZMod p) :=
      Equiv.addRight (t • v)
    change (∑ c, w (e c)) = ∑ c, w c
    exact e.sum_comp w
  have hline (c : Fin n → ZMod p) :
      ∑ t : ZMod p, w (c + t • v) = 0 := by
    have hpoly (t : ZMod p) :
        monicPolynomial n (c + t • v) =
          monicPolynomial n c + C t * derivativeProbe coeff r := by
      simpa only [v, H] using
        monicPolynomial_add_smul_lowerCoefficientVector n c t H hH
    simp_rw [w, hpoly]
    exact sum_polynomialWeight_add_probe_eq_zero coeff
      (monicPolynomial n c) hr
  have hpMul :
      (p : ℂ) * (∑ c : Fin n → ZMod p, w c) = 0 := by
    calc
      (p : ℂ) * (∑ c : Fin n → ZMod p, w c) =
          ∑ t : ZMod p, ∑ c : Fin n → ZMod p, w c := by
        simp [ZMod.card]
      _ = ∑ t : ZMod p, ∑ c : Fin n → ZMod p, w (c + t • v) := by
        apply Finset.sum_congr rfl
        intro t _ht
        exact (htranslate t).symm
      _ = ∑ c : Fin n → ZMod p, ∑ t : ZMod p, w (c + t • v) := by
        rw [Finset.sum_comm]
      _ = 0 := by simp only [hline, Finset.sum_const_zero]
  have hpComplex : (p : ℂ) ≠ 0 := by
    exact_mod_cast (Fact.out : p.Prime).ne_zero
  exact mul_left_cancel₀ hpComplex (by simpa only [mul_zero] using hpMul)

end RationalWeil

end Erdos387

end

/-! ## ErdosProblems.Erdos387.RationalArtinPolynomial -/

noncomputable section

namespace Erdos387

open Polynomial

open scoped BigOperators

namespace RationalWeil

noncomputable def monicWeightSum
    {p : ℕ} [NeZero p] [Fact p.Prime]
    (coeff : ZMod p → ZMod p) (n : ℕ) : ℂ :=
  ∑ c : Fin n → ZMod p, polynomialWeight coeff (monicPolynomial n c)

noncomputable def artinLPolynomial
    {p : ℕ} [NeZero p] [Fact p.Prime]
    (coeff : ZMod p → ZMod p) : ℂ[X] :=
  ∑ n ∈ Finset.range (2 * (InverseRational.poleSupport coeff).card),
    monomial n (monicWeightSum coeff n)

theorem coeff_artinLPolynomial
    {p : ℕ} [NeZero p] [Fact p.Prime]
    (coeff : ZMod p → ZMod p) (n : ℕ) :
    (artinLPolynomial coeff).coeff n =
      if n < 2 * (InverseRational.poleSupport coeff).card then
        monicWeightSum coeff n
      else 0 := by
  classical
  rw [artinLPolynomial, finsetSum_coeff]
  by_cases hn : n < 2 * (InverseRational.poleSupport coeff).card
  · rw [if_pos hn, Finset.sum_eq_single n]
    · simp
    · intro m hm hmn
      rw [coeff_monomial]
      simp only [if_neg hmn]
    · simp [hn]
  · rw [if_neg hn]
    apply Finset.sum_eq_zero
    intro m hm
    rw [coeff_monomial]
    have hmn : m ≠ n := by
      intro h
      subst m
      exact hn (Finset.mem_range.mp hm)
    simp only [if_neg hmn]

theorem coeff_artinLPolynomial_eq_monicWeightSum
    {p : ℕ} [NeZero p] [Fact p.Prime]
    (coeff : ZMod p → ZMod p)
    (hne : (InverseRational.poleSupport coeff).Nonempty) (n : ℕ) :
    (artinLPolynomial coeff).coeff n = monicWeightSum coeff n := by
  rw [coeff_artinLPolynomial]
  split_ifs with hn
  · rfl
  · symm
    unfold monicWeightSum
    exact sum_polynomialWeight_monicPolynomial_eq_zero coeff
      (Nat.le_of_not_gt hn) hne

theorem monicPolynomial_zero_eq_one
    {K : Type*} [Field K] (c : Fin 0 → K) :
    monicPolynomial 0 c = 1 := by
  rw [monicPolynomial]
  have hc : c = 0 := Subsingleton.elim _ _
  subst c
  simp [lowerPolynomial]

theorem monicWeightSum_zero
    {p : ℕ} [NeZero p] [Fact p.Prime]
    (coeff : ZMod p → ZMod p) :
    monicWeightSum coeff 0 = 1 := by
  classical
  rw [monicWeightSum]
  simp only [monicPolynomial_zero_eq_one]
  have havoid : AvoidsPoleSupport coeff (1 : (ZMod p)[X]) := by
    intro r hr
    simp
  rw [show polynomialWeight coeff (1 : (ZMod p)[X]) = 1 by
    rw [polynomialWeight, if_pos havoid]
    simp [logarithmicDerivativePhase]]
  simp

theorem coeff_zero_artinLPolynomial
    {p : ℕ} [NeZero p] [Fact p.Prime]
    (coeff : ZMod p → ZMod p)
    (hne : (InverseRational.poleSupport coeff).Nonempty) :
    (artinLPolynomial coeff).coeff 0 = 1 := by
  rw [coeff_artinLPolynomial_eq_monicWeightSum coeff hne,
    monicWeightSum_zero]

theorem natDegree_artinLPolynomial_lt
    {p : ℕ} [NeZero p] [Fact p.Prime]
    (coeff : ZMod p → ZMod p)
    (hne : (InverseRational.poleSupport coeff).Nonempty) :
    (artinLPolynomial coeff).natDegree <
      2 * (InverseRational.poleSupport coeff).card := by
  have hcard : 0 < (InverseRational.poleSupport coeff).card :=
    Finset.card_pos.mpr hne
  rw [Nat.lt_iff_le_pred (by omega :
    0 < 2 * (InverseRational.poleSupport coeff).card)]
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro n hn
  rw [coeff_artinLPolynomial, if_neg]
  omega

end RationalWeil

end Erdos387

end

/-! ## ErdosProblems.Erdos387.RationalLocalEuler -/

noncomputable section

namespace Erdos387

namespace RationalWeil

variable {R : Type*} [CommRing R]

noncomputable def localEuler (e : Nat) (z : R) : PowerSeries R :=
  PowerSeries.subst (PowerSeries.X ^ e)
    (PowerSeries.rescale z (PowerSeries.mk 1))

@[simp]

theorem coeff_localEuler (z : R) {e n : Nat} (he : e ≠ 0) :
    PowerSeries.coeff n (localEuler e z) =
      if e ∣ n then z ^ (n / e) else 0 := by
  rw [localEuler, PowerSeries.coeff_subst_X_pow he,
    PowerSeries.coeff_rescale, PowerSeries.coeff_mk]
  simp

theorem localEuler_mul_one_sub (z : R) {e : Nat} (he : e ≠ 0) :
    localEuler e z *
      (1 - PowerSeries.C z * PowerSeries.X ^ e) = 1 := by
  have hbase := PowerSeries.mk_one_mul_one_sub_eq_one R
  have hscale := congrArg (PowerSeries.rescale z) hbase
  simp only [map_mul, map_sub, map_one, PowerSeries.rescale_X] at hscale
  let hs := PowerSeries.HasSubst.X_pow (R := R) he
  let phi : PowerSeries R →ₐ[R] PowerSeries R :=
    PowerSeries.substAlgHom hs
  have hsubst := congrArg phi hscale
  simp only [map_mul, map_sub, map_one, phi,
    PowerSeries.substAlgHom_X] at hsubst
  rw [PowerSeries.coe_substAlgHom hs] at hsubst
  rw [PowerSeries.subst_C] at hsubst
  exact hsubst

private theorem RationalLocalEuler_derivative_one_sub_C_mul_X_pow (z : R) (e : Nat) :
    PowerSeries.derivative R
        (1 - PowerSeries.C z * PowerSeries.X ^ e) =
      -PowerSeries.C ((e : R) * z) * PowerSeries.X ^ (e - 1) := by
  rw [map_sub, ← map_one (PowerSeries.C (R := R)),
    PowerSeries.derivative_C, Derivation.leibniz,
    PowerSeries.derivative_C, PowerSeries.derivative_pow,
    PowerSeries.derivative_X]
  simp only [smul_eq_mul, mul_one, zero_sub]
  rw [map_mul]
  simp only [map_natCast]
  ring

theorem X_mul_derivativeFun_localEuler (z : R) {e : Nat} (he : e ≠ 0) :
    PowerSeries.X * PowerSeries.derivative R (localEuler e z) =
      PowerSeries.C (e : R) * localEuler e z * (localEuler e z - 1) := by
  let L : PowerSeries R := localEuler e z
  let Q : PowerSeries R :=
    1 - PowerSeries.C z * PowerSeries.X ^ e
  have hInv : L * Q = 1 := localEuler_mul_one_sub z he
  have hDer :
      L * PowerSeries.derivative R Q +
          Q * PowerSeries.derivative R L = 0 := by
    have h := congrArg (PowerSeries.derivative R) hInv
    rw [Derivation.leibniz,
      Derivation.map_one_eq_zero] at h
    simpa only [smul_eq_mul, add_comm] using h
  have hQDer :
      PowerSeries.derivative R Q =
        -PowerSeries.C ((e : R) * z) *
          PowerSeries.X ^ (e - 1) :=
    RationalLocalEuler_derivative_one_sub_C_mul_X_pow z e
  rw [hQDer] at hDer
  have hPow :
      PowerSeries.X * PowerSeries.X ^ (e - 1) =
        (PowerSeries.X : PowerSeries R) ^ e := by
    cases e with
    | zero => exact (he rfl).elim
    | succ e =>
        rw [Nat.succ_sub_one, pow_succ]
        ac_rfl
  rw [map_mul] at hDer
  simp only [map_natCast] at hDer
  rw [map_natCast]
  linear_combination
    (PowerSeries.X * L) * hDer -
      (PowerSeries.X * PowerSeries.derivative R L +
        (e : PowerSeries R) * L) * hInv +
      ((e : PowerSeries R) * PowerSeries.C z * L ^ 2) * hPow

end RationalWeil

end Erdos387

end

/-! ## ErdosProblems.Erdos387.RationalMonicFactors -/

noncomputable section

namespace Erdos387

open Polynomial

namespace RationalWeil

structure MonicIrreducibleLE (K : Type*) [CommRing K] (N : Nat) where
  poly : K[X]
  irreducible : Irreducible poly
  monic : poly.Monic
  natDegree_le : poly.natDegree ≤ N

namespace MonicIrreducibleLE

variable {K : Type*} [Field K] {N : Nat}

noncomputable def toDegreeLT (P : MonicIrreducibleLE K N) :
    degreeLT K (N + 1) :=
  ⟨P.poly, by
    rw [mem_degreeLT, degree_eq_natDegree P.irreducible.ne_zero]
    exact_mod_cast Nat.lt_succ_of_le P.natDegree_le⟩

theorem toDegreeLT_injective :
    Function.Injective (toDegreeLT : MonicIrreducibleLE K N → degreeLT K (N + 1)) := by
  intro P Q h
  cases P
  cases Q
  simp only [toDegreeLT] at h
  cases h
  rfl

noncomputable instance [Fintype K] : Fintype (MonicIrreducibleLE K N) := by
  letI : Fintype (degreeLT K (N + 1)) :=
    Fintype.ofEquiv (Fin (N + 1) → K) (degreeLTEquiv K (N + 1)).toEquiv.symm
  exact Fintype.ofInjective toDegreeLT toDegreeLT_injective

theorem poly_injective :
    Function.Injective (MonicIrreducibleLE.poly : MonicIrreducibleLE K N → K[X]) := by
  intro P Q h
  cases P
  cases Q
  cases h
  rfl

theorem natDegree_pos (P : MonicIrreducibleLE K N) : 0 < P.poly.natDegree :=
  P.irreducible.natDegree_pos

end MonicIrreducibleLE

variable {K : Type*} [Field K] {N : Nat}

noncomputable def monicFactorProduct
    (m : MonicIrreducibleLE K N →₀ Nat) : K[X] :=
  (m.toMultiset.map MonicIrreducibleLE.poly).prod

noncomputable def monicFactorWeight :
    (MonicIrreducibleLE K N →₀ Nat) →+ Nat :=
  Finsupp.weight (fun P ↦ P.poly.natDegree)

theorem monicFactorProduct_monic
    (m : MonicIrreducibleLE K N →₀ Nat) :
    (monicFactorProduct m).Monic := by
  apply monic_multiset_prod_of_monic
  intro P hP
  exact P.monic

private theorem RationalMonicFactors_sum_map_toMultiset
    (m : MonicIrreducibleLE K N →₀ Nat)
    (w : MonicIrreducibleLE K N → Nat) :
    (m.toMultiset.map w).sum = m.sum (fun P c ↦ c • w P) := by
  classical
  refine m.induction ?_ ?_
  · simp [Finsupp.toMultiset_zero]
  · intro P n f hP hn ih
    rw [Finsupp.toMultiset_add, Multiset.map_add, Multiset.sum_add, ih,
      Finsupp.sum_add_index' (by simp) (by intros; exact add_nsmul _ _ _),
      Finsupp.sum_single_index (by simp), Finsupp.toMultiset_single,
      Multiset.map_nsmul, Multiset.map_singleton, Multiset.sum_nsmul,
      Multiset.sum_singleton]

theorem natDegree_monicFactorProduct
    (m : MonicIrreducibleLE K N →₀ Nat) :
    (monicFactorProduct m).natDegree = monicFactorWeight m := by
  have hmonic :
      ∀ f ∈ (m.toMultiset.map MonicIrreducibleLE.poly), f.Monic := by
    intro f hf
    obtain ⟨P, hP, rfl⟩ := Multiset.mem_map.mp hf
    exact P.monic
  rw [monicFactorProduct, natDegree_multiset_prod_of_monic _ hmonic,
    monicFactorWeight, Finsupp.weight_apply]
  simpa only [Multiset.map_map, Function.comp_apply] using
    RationalMonicFactors_sum_map_toMultiset m (fun P ↦ P.poly.natDegree)

variable [DecidableEq K]

theorem normalizedFactors_monicFactorProduct
    (m : MonicIrreducibleLE K N →₀ Nat) :
    UniqueFactorizationMonoid.normalizedFactors (monicFactorProduct m) =
      m.toMultiset.map MonicIrreducibleLE.poly := by
  let s := m.toMultiset.map MonicIrreducibleLE.poly
  have hirr : ∀ f ∈ s, Irreducible f := by
    intro f hf
    obtain ⟨P, hP, rfl⟩ := Multiset.mem_map.mp hf
    exact P.irreducible
  change UniqueFactorizationMonoid.normalizedFactors s.prod = s
  rw [UniqueFactorizationMonoid.normalizedFactors_prod_eq s hirr]
  calc
    s.map normalize = s.map id := by
      apply Multiset.map_congr rfl
      intro f hf
      obtain ⟨P, hP, rfl⟩ := Multiset.mem_map.mp hf
      exact P.monic.normalize_eq_self
    _ = s := Multiset.map_id s

omit [DecidableEq K] in

theorem monicFactorProduct_injective :
    Function.Injective
      (monicFactorProduct : (MonicIrreducibleLE K N →₀ Nat) → K[X]) := by
  classical
  intro m r h
  have hmaps :
      m.toMultiset.map MonicIrreducibleLE.poly =
        r.toMultiset.map MonicIrreducibleLE.poly := by
    rw [← normalizedFactors_monicFactorProduct,
      ← normalizedFactors_monicFactorProduct, h]
  have hmulti : m.toMultiset = r.toMultiset :=
    Multiset.map_injective MonicIrreducibleLE.poly_injective hmaps
  calc
    m = Multiset.toFinsupp m.toMultiset :=
      (Finsupp.toMultiset_toFinsupp m).symm
    _ = Multiset.toFinsupp r.toMultiset := congrArg Multiset.toFinsupp hmulti
    _ = r := Finsupp.toMultiset_toFinsupp r

noncomputable def boundedNormalizedFactor
    {n : Nat} (hnN : n ≤ N)
    (F : {F : K[X] // F.Monic ∧ F.natDegree = n})
    (P : {P // P ∈ UniqueFactorizationMonoid.normalizedFactors F.1}) :
    MonicIrreducibleLE K N := by
  classical
  have hdata := (Polynomial.mem_normalizedFactors_iff F.2.1.ne_zero).mp P.2
  exact
    { poly := P.1
      irreducible := hdata.1
      monic := hdata.2.1
      natDegree_le :=
        (Polynomial.natDegree_le_of_dvd hdata.2.2 F.2.1.ne_zero).trans
          (F.2.2.le.trans hnN) }

noncomputable def boundedNormalizedFactors {n : Nat} (hnN : n ≤ N)
    (F : {F : K[X] // F.Monic ∧ F.natDegree = n}) :
    Multiset (MonicIrreducibleLE K N) :=
  (UniqueFactorizationMonoid.normalizedFactors F.1).attach.map
    (boundedNormalizedFactor hnN F)

theorem map_boundedNormalizedFactors {n : Nat} (hnN : n ≤ N)
    (F : {F : K[X] // F.Monic ∧ F.natDegree = n}) :
    (boundedNormalizedFactors hnN F).map MonicIrreducibleLE.poly =
      UniqueFactorizationMonoid.normalizedFactors F.1 := by
  rw [boundedNormalizedFactors, Multiset.map_map]
  exact Multiset.attach_map_val _

noncomputable def monicFactorization {n : Nat} (hnN : n ≤ N)
    (F : {F : K[X] // F.Monic ∧ F.natDegree = n}) :
    MonicIrreducibleLE K N →₀ Nat := by
  classical
  exact Multiset.toFinsupp (boundedNormalizedFactors hnN F)

theorem monicFactorProduct_factorization {n : Nat} (hnN : n ≤ N)
    (F : {F : K[X] // F.Monic ∧ F.natDegree = n}) :
    monicFactorProduct (monicFactorization hnN F) = F.1 := by
  classical
  rw [monicFactorProduct, monicFactorization,
    Multiset.toFinsupp_toMultiset, map_boundedNormalizedFactors,
    UniqueFactorizationMonoid.prod_normalizedFactors_eq F.2.1.ne_zero,
    F.2.1.normalize_eq_self]

theorem monicFactorWeight_factorization {n : Nat} (hnN : n ≤ N)
    (F : {F : K[X] // F.Monic ∧ F.natDegree = n}) :
    monicFactorWeight (monicFactorization hnN F) = n := by
  rw [← natDegree_monicFactorProduct, monicFactorProduct_factorization hnN F,
    F.2.2]

noncomputable def weightedFactorsToMonic (n : Nat) :
    {m : MonicIrreducibleLE K N →₀ Nat // monicFactorWeight m = n} →
      {F : K[X] // F.Monic ∧ F.natDegree = n} :=
  fun m ↦ ⟨monicFactorProduct m.1, monicFactorProduct_monic m.1,
    (natDegree_monicFactorProduct m.1).trans m.2⟩

noncomputable def weightedFactorsEquivMonic {n : Nat} (hnN : n ≤ N) :
    {m : MonicIrreducibleLE K N →₀ Nat // monicFactorWeight m = n} ≃
      {F : K[X] // F.Monic ∧ F.natDegree = n} :=
  Equiv.ofBijective (weightedFactorsToMonic n) ⟨by
    intro m r h
    apply Subtype.ext
    apply monicFactorProduct_injective
    exact congrArg Subtype.val h, by
    intro F
    let m : MonicIrreducibleLE K N →₀ Nat := monicFactorization hnN F
    have hm : monicFactorWeight m = n := monicFactorWeight_factorization hnN F
    refine ⟨⟨m, hm⟩, ?_⟩
    apply Subtype.ext
    exact monicFactorProduct_factorization hnN F⟩

end RationalWeil

end Erdos387

end

/-! ## ErdosProblems.Erdos387.RationalEulerCoefficients -/

noncomputable section

namespace Erdos387

open Polynomial

open scoped BigOperators

namespace RationalWeil

variable {K R : Type*} [Field K] [Fintype K] [CommRing R] {N n : Nat}

noncomputable def monicCoefficientEquiv
    {K : Type*} [Field K] (n : ℕ) :
    {F : K[X] // F.Monic ∧ F.natDegree = n} ≃ (Fin n → K) :=
  (monicEquivDegreeLT n).trans (degreeLTEquiv K n).toEquiv

noncomputable instance instFintypeMonicNatDegree
    {K : Type*} [Field K] [Fintype K] (n : ℕ) :
    Fintype {F : K[X] // F.Monic ∧ F.natDegree = n} :=
  Fintype.ofEquiv (Fin n → K) (monicCoefficientEquiv n).symm

theorem monicCoefficientEquiv_symm_apply
    {K : Type*} [Field K] (n : ℕ) (c : Fin n → K) :
    ((monicCoefficientEquiv n).symm c).1 = monicPolynomial n c := by
  rfl

noncomputable instance weightedFactorsFintype :
    Fintype
      {m : MonicIrreducibleLE K N →₀ Nat // monicFactorWeight m = n} := by
  classical
  exact (Finsupp.finite_of_nat_weight_eq
    (fun P : MonicIrreducibleLE K N ↦ P.poly.natDegree)
    (fun P ↦ P.natDegree_pos.ne') n).fintype

noncomputable def multiplicativeFactorWeight
    (w : MonicIrreducibleLE K N → R)
    (m : MonicIrreducibleLE K N →₀ Nat) : R :=
  ∏ P, w P ^ m P

theorem prod_map_toMultiset_eq_multiplicativeFactorWeight
    (w : MonicIrreducibleLE K N → R)
    (m : MonicIrreducibleLE K N →₀ Nat) :
    (m.toMultiset.map w).prod = multiplicativeFactorWeight w m := by
  rw [multiplicativeFactorWeight, ← Finsupp.prod_pow]
  induction m using Finsupp.induction with
  | zero => simp [Finsupp.toMultiset_zero]
  | @single_add P e f hP he ih =>
      rw [Finsupp.toMultiset_add, Multiset.map_add, Multiset.prod_add, ih]
      calc
        (Multiset.map w (Finsupp.toMultiset (Finsupp.single P e))).prod *
            f.prod (fun Q a ↦ w Q ^ a) =
            w P ^ e * f.prod (fun Q a ↦ w Q ^ a) := by
          rw [Finsupp.toMultiset_single, Multiset.map_nsmul,
            Multiset.map_singleton, Multiset.prod_nsmul,
            Multiset.prod_singleton]
        _ = (Finsupp.single P e).prod (fun Q a ↦ w Q ^ a) *
              f.prod (fun Q a ↦ w Q ^ a) := by
          rw [Finsupp.prod_single_index]
          exact pow_zero _
        _ = (Finsupp.single P e + f).prod (fun Q a ↦ w Q ^ a) := by
          symm
          exact Finsupp.prod_add_index' (fun _ ↦ pow_zero _)
            (fun _ _ _ ↦ pow_add _ _ _)

noncomputable def degreeScaledIndex
    (m : MonicIrreducibleLE K N →₀ Nat) :
    MonicIrreducibleLE K N →₀ Nat :=
  Finsupp.onFinset Finset.univ
    (fun P ↦ P.poly.natDegree * m P) (by simp)

@[simp]

theorem degreeScaledIndex_apply
    (m : MonicIrreducibleLE K N →₀ Nat)
    (P : MonicIrreducibleLE K N) :
    degreeScaledIndex m P = P.poly.natDegree * m P := by
  simp [degreeScaledIndex]

noncomputable def degreeUnscaledIndex
    (l : MonicIrreducibleLE K N →₀ Nat) :
    MonicIrreducibleLE K N →₀ Nat :=
  Finsupp.onFinset Finset.univ
    (fun P ↦ l P / P.poly.natDegree) (by simp)

@[simp]

theorem degreeUnscaledIndex_apply
    (l : MonicIrreducibleLE K N →₀ Nat)
    (P : MonicIrreducibleLE K N) :
    degreeUnscaledIndex l P = l P / P.poly.natDegree := by
  simp [degreeUnscaledIndex]

theorem degreeUnscaledIndex_scaled
    (m : MonicIrreducibleLE K N →₀ Nat) :
    degreeUnscaledIndex (degreeScaledIndex m) = m := by
  ext P
  simp [Nat.mul_div_cancel_left _ P.natDegree_pos]

theorem degreeScaledIndex_unscaled
    (l : MonicIrreducibleLE K N →₀ Nat)
    (hl : ∀ P, P.poly.natDegree ∣ l P) :
    degreeScaledIndex (degreeUnscaledIndex l) = l := by
  ext P
  simp only [degreeScaledIndex_apply, degreeUnscaledIndex_apply]
  rw [mul_comm, Nat.div_mul_cancel (hl P)]

private theorem RationalEulerCoefficients_sum_degreeScaledIndex
    (m : MonicIrreducibleLE K N →₀ Nat) :
    ∑ P, degreeScaledIndex m P = monicFactorWeight m := by
  classical
  rw [monicFactorWeight, Finsupp.weight_apply,
    Finsupp.sum_fintype]
  · apply Finset.sum_congr rfl
    intro P hP
    simp [mul_comm]
  · intro P
    simp

private theorem RationalEulerCoefficients_weight_degreeUnscaledIndex
    (l : MonicIrreducibleLE K N →₀ Nat)
    (hl : ∀ P, P.poly.natDegree ∣ l P) :
    monicFactorWeight (degreeUnscaledIndex l) = ∑ P, l P := by
  classical
  rw [monicFactorWeight, Finsupp.weight_apply,
    Finsupp.sum_fintype]
  · apply Finset.sum_congr rfl
    intro P hP
    simp only [degreeUnscaledIndex_apply, nsmul_eq_mul]
    exact Nat.div_mul_cancel (hl P)
  · intro P
    simp

theorem coeff_localEulerProduct_eq_sum_weightedFactors
    (w : MonicIrreducibleLE K N → R) :
    PowerSeries.coeff n
        (∏ P : MonicIrreducibleLE K N,
          localEuler P.poly.natDegree (w P)) =
      ∑ m : {m : MonicIrreducibleLE K N →₀ Nat //
          monicFactorWeight m = n},
        multiplicativeFactorWeight w m.1 := by
  classical
  rw [PowerSeries.coeff_prod]
  let good : Finset (MonicIrreducibleLE K N →₀ Nat) :=
    (Finset.finsuppAntidiag Finset.univ n).filter
      (fun l ↦ ∀ P, P.poly.natDegree ∣ l P)
  have hterm (l : MonicIrreducibleLE K N →₀ Nat) :
      (∏ P, PowerSeries.coeff (l P)
        (localEuler P.poly.natDegree (w P))) =
        if (∀ P, P.poly.natDegree ∣ l P) then
          ∏ P, w P ^ (l P / P.poly.natDegree) else 0 := by
    by_cases hl : ∀ P, P.poly.natDegree ∣ l P
    · rw [if_pos hl]
      apply Finset.prod_congr rfl
      intro P hP
      rw [coeff_localEuler (w P) P.natDegree_pos.ne', if_pos (hl P)]
    · rw [if_neg hl]
      push Not at hl
      obtain ⟨P, hP⟩ := hl
      apply Finset.prod_eq_zero (Finset.mem_univ P)
      rw [coeff_localEuler (w P) P.natDegree_pos.ne', if_neg hP]
  simp_rw [hterm]
  rw [← Finset.sum_filter]
  change (∑ l ∈ good, ∏ P, w P ^ (l P / P.poly.natDegree)) = _
  symm
  apply Finset.sum_bij
      (fun m _ ↦ degreeScaledIndex m.1)
  · intro m hm
    simp only [good, Finset.mem_filter, Finset.mem_finsuppAntidiag]
    refine ⟨⟨?_, Finset.subset_univ _⟩, ?_⟩
    · rw [RationalEulerCoefficients_sum_degreeScaledIndex]
      exact m.2
    · intro P
      simp
  · intro a ha b hb hab
    apply Subtype.ext
    simpa only [degreeUnscaledIndex_scaled] using
      congrArg degreeUnscaledIndex hab
  · intro l hl
    simp only [good, Finset.mem_filter, Finset.mem_finsuppAntidiag] at hl
    let m : MonicIrreducibleLE K N →₀ Nat := degreeUnscaledIndex l
    have hm : monicFactorWeight m = n := by
      rw [RationalEulerCoefficients_weight_degreeUnscaledIndex l hl.2, ← hl.1.1]
    refine ⟨⟨m, hm⟩, Finset.mem_univ _, ?_⟩
    exact degreeScaledIndex_unscaled l hl.2
  · intro m hm
    simp [multiplicativeFactorWeight,
      Nat.mul_div_cancel_left _ (MonicIrreducibleLE.natDegree_pos _)]

variable [DecidableEq K]

theorem coeff_localEulerProduct_eq_sum_monic
    (hnN : n ≤ N) (w : MonicIrreducibleLE K N → R) :
    PowerSeries.coeff n
        (∏ P : MonicIrreducibleLE K N,
          localEuler P.poly.natDegree (w P)) =
      ∑ F : {F : K[X] // F.Monic ∧ F.natDegree = n},
        multiplicativeFactorWeight w (monicFactorization hnN F) := by
  rw [coeff_localEulerProduct_eq_sum_weightedFactors]
  apply Fintype.sum_equiv (weightedFactorsEquivMonic hnN)
  intro m
  congr 1
  apply monicFactorProduct_injective
  rw [monicFactorProduct_factorization]
  rfl

theorem polynomialWeight_one
    {p : ℕ} [NeZero p] [Fact p.Prime]
    (coeff : ZMod p → ZMod p) :
    polynomialWeight coeff (1 : (ZMod p)[X]) = 1 := by
  have havoid : AvoidsPoleSupport coeff (1 : (ZMod p)[X]) := by
    intro r hr
    simp
  rw [polynomialWeight, if_pos havoid]
  simp [logarithmicDerivativePhase]

theorem polynomialWeight_multiset_prod
    {p : ℕ} [NeZero p] [Fact p.Prime]
    (coeff : ZMod p → ZMod p)
    (s : Multiset (ZMod p)[X]) :
    polynomialWeight coeff s.prod =
      (s.map (polynomialWeight coeff)).prod := by
  induction s using Multiset.induction_on with
  | empty => simp [polynomialWeight_one]
  | cons F s ih =>
      rw [Multiset.prod_cons, Multiset.map_cons, Multiset.prod_cons,
        polynomialWeight_mul, ih]

theorem multiplicativeFactorWeight_polynomialWeight
    {p : ℕ} [NeZero p] [Fact p.Prime] {N : ℕ}
    (coeff : ZMod p → ZMod p)
    (m : MonicIrreducibleLE (ZMod p) N →₀ Nat) :
    multiplicativeFactorWeight
        (fun P ↦ polynomialWeight coeff P.poly) m =
      polynomialWeight coeff (monicFactorProduct m) := by
  let s : Multiset (ZMod p)[X] :=
    m.toMultiset.map MonicIrreducibleLE.poly
  calc
    multiplicativeFactorWeight
        (fun P ↦ polynomialWeight coeff P.poly) m =
        (m.toMultiset.map
          (fun P ↦ polynomialWeight coeff P.poly)).prod :=
      (prod_map_toMultiset_eq_multiplicativeFactorWeight _ m).symm
    _ = (s.map (polynomialWeight coeff)).prod := by
      simp only [s, Multiset.map_map, Function.comp_apply]
    _ = polynomialWeight coeff s.prod :=
      (polynomialWeight_multiset_prod coeff s).symm
    _ = polynomialWeight coeff (monicFactorProduct m) := rfl

theorem sum_polynomialWeight_monic_eq_monicWeightSum
    {p : ℕ} [NeZero p] [Fact p.Prime]
    (coeff : ZMod p → ZMod p) (n : ℕ) :
    (∑ F : {F : (ZMod p)[X] // F.Monic ∧ F.natDegree = n},
      polynomialWeight coeff F.1) = monicWeightSum coeff n := by
  rw [monicWeightSum]
  let e := monicCoefficientEquiv (K := ZMod p) n
  calc
    (∑ F : {F : (ZMod p)[X] // F.Monic ∧ F.natDegree = n},
        polynomialWeight coeff F.1) =
        ∑ c : Fin n → ZMod p,
          polynomialWeight coeff (e.symm c).1 := by
      exact (e.symm.sum_comp (fun F ↦ polynomialWeight coeff F.1)).symm
    _ = ∑ c : Fin n → ZMod p,
        polynomialWeight coeff (monicPolynomial n c) := by
      apply Finset.sum_congr rfl
      intro c hc
      rw [monicCoefficientEquiv_symm_apply]

theorem coeff_localEulerProduct_polynomialWeight_eq_monicWeightSum
    {p : ℕ} [NeZero p] [Fact p.Prime]
    (coeff : ZMod p → ZMod p) {N n : ℕ} (hnN : n ≤ N) :
    PowerSeries.coeff n
        (∏ P : MonicIrreducibleLE (ZMod p) N,
          localEuler P.poly.natDegree (polynomialWeight coeff P.poly)) =
      monicWeightSum coeff n := by
  classical
  rw [coeff_localEulerProduct_eq_sum_monic hnN]
  calc
    (∑ F : {F : (ZMod p)[X] // F.Monic ∧ F.natDegree = n},
        multiplicativeFactorWeight
          (fun P ↦ polynomialWeight coeff P.poly)
          (monicFactorization hnN F)) =
        ∑ F : {F : (ZMod p)[X] // F.Monic ∧ F.natDegree = n},
          polynomialWeight coeff F.1 := by
      apply Finset.sum_congr rfl
      intro F hF
      rw [multiplicativeFactorWeight_polynomialWeight,
        monicFactorProduct_factorization]
    _ = monicWeightSum coeff n :=
      sum_polynomialWeight_monic_eq_monicWeightSum coeff n

end RationalWeil

end Erdos387

end

/-! ## ErdosProblems.Erdos387.RationalPowerSeriesRecurrence -/

noncomputable section

namespace Erdos387

open PowerSeries

open scoped PowerSeries

namespace RationalWeil

variable {R : Type*} [CommSemiring R]

theorem coeff_mul_nat_eq_sum_antidiagonal_of_X_mul_derivativeFun_eq_mul
    {L B : R⟦X⟧} (h : X * PowerSeries.derivative R L = L * B) (n : Nat) :
    coeff n L * (n : R) =
      ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, coeff p.1 L * coeff p.2 B := by
  cases n with
  | zero =>
      have hn := congrArg (coeff 0) h
      rw [coeff_zero_X_mul, coeff_mul] at hn
      simpa only [Nat.cast_zero, mul_zero] using hn
  | succ n =>
      have hn := congrArg (coeff (n + 1)) h
      rw [coeff_succ_X_mul, coeff_derivative, coeff_mul] at hn
      simpa only [Nat.cast_add, Nat.cast_one] using hn

theorem nat_mul_coeff_eq_sum_range_of_X_mul_derivativeFun_eq_mul
    {L B : R⟦X⟧} (h : X * PowerSeries.derivative R L = L * B) (n : Nat) :
    (n : R) * coeff n L =
      ∑ i ∈ Finset.range (n + 1), coeff (n - i) L * coeff i B := by
  rw [mul_comm]
  rw [coeff_mul_nat_eq_sum_antidiagonal_of_X_mul_derivativeFun_eq_mul h n]
  rw [← Finset.Nat.sum_antidiagonal_swap]
  exact Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j ↦ coeff j L * coeff i B) n

theorem nat_mul_coeff_eq_sum_positive_of_X_mul_derivativeFun_eq_mul
    {L B : R⟦X⟧} (h : X * PowerSeries.derivative R L = L * B)
    (hB : constantCoeff B = 0) (n : Nat) :
    (n : R) * coeff n L =
      ∑ i ∈ Finset.range n, coeff (n - (i + 1)) L * coeff (i + 1) B := by
  rw [nat_mul_coeff_eq_sum_range_of_X_mul_derivativeFun_eq_mul h n,
    Finset.sum_range_succ']
  simp only [coeff_zero_eq_constantCoeff_apply, hB, mul_zero, add_zero]

theorem coeff_logDerivative_eq_of_coeff_eq_up_to
    [IsLeftCancelAdd R] {L A B C : R⟦X⟧} {N : Nat}
    (hLB : X * PowerSeries.derivative R L = L * B)
    (hAC : X * PowerSeries.derivative R A = A * C)
    (hB0 : constantCoeff B = 0) (hC0 : constantCoeff C = 0)
    (hL0 : coeff 0 L = 1)
    (hcoeff : ∀ j, j ≤ N → coeff j L = coeff j A)
    {n : Nat} (hnN : n ≤ N) :
    coeff n B = coeff n C := by
  have hA0 : coeff 0 A = 1 := by
    rw [← hcoeff 0 (Nat.zero_le N)]
    exact hL0
  induction n using Nat.strong_induction_on with
  | h n ih =>
      cases n with
      | zero =>
          simp only [coeff_zero_eq_constantCoeff_apply, hB0, hC0]
      | succ k =>
          have hrecL :=
            nat_mul_coeff_eq_sum_positive_of_X_mul_derivativeFun_eq_mul
              hLB hB0 (k + 1)
          have hrecA :=
            nat_mul_coeff_eq_sum_positive_of_X_mul_derivativeFun_eq_mul
              hAC hC0 (k + 1)
          have hsums :
              (∑ i ∈ Finset.range (k + 1),
                coeff (k + 1 - (i + 1)) L * coeff (i + 1) B) =
              ∑ i ∈ Finset.range (k + 1),
                coeff (k + 1 - (i + 1)) A * coeff (i + 1) C := by
            rw [← hrecL, ← hrecA, hcoeff (k + 1) hnN]
          rw [Finset.sum_range_succ, Finset.sum_range_succ] at hsums
          have hprevious :
              (∑ i ∈ Finset.range k,
                coeff (k + 1 - (i + 1)) L * coeff (i + 1) B) =
              ∑ i ∈ Finset.range k,
                coeff (k + 1 - (i + 1)) A * coeff (i + 1) C := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [hcoeff _ (Nat.le_trans (Nat.sub_le _ _) hnN)]
            rw [ih (i + 1)
              (by simp only [Finset.mem_range] at hi; omega)
              (by simp only [Finset.mem_range] at hi; omega)]
          rw [hprevious] at hsums
          simp only [Nat.sub_self, hL0, hA0, one_mul] at hsums
          exact add_left_cancel hsums

end RationalWeil

end Erdos387

end

/-! ## ErdosProblems.Erdos387.RationalFiniteEuler -/

noncomputable section

namespace Erdos387

open Polynomial

namespace RationalWeil

variable {K R : Type*} [Field K] [Fintype K] [CommRing R] {N n : Nat}

noncomputable def finiteEulerProduct
    (w : MonicIrreducibleLE K N → R) : PowerSeries R :=
  ∏ P : MonicIrreducibleLE K N,
    localEuler P.poly.natDegree (w P)

noncomputable def finiteEulerLogDerivative
    (w : MonicIrreducibleLE K N → R) : PowerSeries R :=
  ∑ P : MonicIrreducibleLE K N,
    PowerSeries.C (P.poly.natDegree : R) *
      (localEuler P.poly.natDegree (w P) - 1)

private theorem RationalFiniteEuler_X_mul_derivativeFun_prod_localEuler
    {I : Type*} [Fintype I] (e : I → Nat) (he : ∀ i, e i ≠ 0)
    (z : I → R) :
    PowerSeries.X * PowerSeries.derivative R
        (∏ i : I, localEuler (e i) (z i)) =
      (∏ i : I, localEuler (e i) (z i)) *
        (∑ i : I, PowerSeries.C (e i : R) *
          (localEuler (e i) (z i) - 1)) := by
  classical
  let s : Finset I := Finset.univ
  change PowerSeries.X * PowerSeries.derivative R
      (∏ i ∈ s, localEuler (e i) (z i)) =
    (∏ i ∈ s, localEuler (e i) (z i)) *
      (∑ i ∈ s, PowerSeries.C (e i : R) *
        (localEuler (e i) (z i) - 1))
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha,
        Derivation.leibniz]
      simp only [smul_eq_mul]
      have hlocal := X_mul_derivativeFun_localEuler (z a) (he a)
      linear_combination
        localEuler (e a) (z a) * ih +
          (∏ i ∈ s, localEuler (e i) (z i)) * hlocal

theorem X_mul_derivativeFun_finiteEulerProduct
    (w : MonicIrreducibleLE K N → R) :
    PowerSeries.X *
        PowerSeries.derivative R (finiteEulerProduct w) =
      finiteEulerProduct w * finiteEulerLogDerivative w := by
  rw [finiteEulerProduct, finiteEulerLogDerivative]
  exact RationalFiniteEuler_X_mul_derivativeFun_prod_localEuler
    (fun P : MonicIrreducibleLE K N ↦ P.poly.natDegree)
    (fun P ↦ P.natDegree_pos.ne') w

theorem coeff_finiteEulerLogDerivative (hn : n ≠ 0)
    (w : MonicIrreducibleLE K N → R) :
    PowerSeries.coeff n (finiteEulerLogDerivative w) =
      ∑ P : MonicIrreducibleLE K N,
        if P.poly.natDegree ∣ n then
          (P.poly.natDegree : R) *
            w P ^ (n / P.poly.natDegree)
        else 0 := by
  classical
  rw [finiteEulerLogDerivative, map_sum]
  apply Finset.sum_congr rfl
  intro P hP
  rw [PowerSeries.coeff_C_mul, map_sub,
    coeff_localEuler (w P) P.natDegree_pos.ne',
    PowerSeries.coeff_one, if_neg hn]
  simp only [sub_zero]
  split_ifs <;> simp

theorem constantCoeff_finiteEulerLogDerivative
    (w : MonicIrreducibleLE K N → R) :
    PowerSeries.constantCoeff (finiteEulerLogDerivative w) = 0 := by
  classical
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply,
    finiteEulerLogDerivative, map_sum]
  apply Finset.sum_eq_zero
  intro P hP
  rw [PowerSeries.coeff_C_mul, map_sub,
    coeff_localEuler (w P) P.natDegree_pos.ne',
    PowerSeries.coeff_one]
  simp

end RationalWeil

end Erdos387

end

/-! ## ErdosProblems.Erdos387.RationalReciprocalRoots -/

noncomputable section

namespace Erdos387

open Polynomial PowerSeries

open scoped BigOperators PowerSeries

namespace RationalWeil

theorem reverse_reverse_of_coeff_zero_ne_zero
    {R : Type*} [Semiring R] {A : R[X]} (hA0 : A.coeff 0 ≠ 0) :
    A.reverse.reverse = A := by
  have htrail : A.natTrailingDegree = 0 :=
    natTrailingDegree_eq_zero.mpr (Or.inr hA0)
  rw [reverse, reverse_natDegree, htrail, Nat.sub_zero]
  exact reflect_reflect

theorem monic_reverse_artinLPolynomial
    {p : ℕ} [NeZero p] [Fact p.Prime]
    (coeff : ZMod p → ZMod p)
    (hne : (InverseRational.poleSupport coeff).Nonempty) :
    (artinLPolynomial coeff).reverse.Monic := by
  rw [Monic, reverse_leadingCoeff,
    trailingCoeff_eq_coeff_zero (by
      rw [coeff_zero_artinLPolynomial coeff hne]
      exact one_ne_zero),
    coeff_zero_artinLPolynomial coeff hne]

theorem reverse_multiset_prod_of_domain
    {R : Type*} [CommRing R] [IsDomain R] (s : Multiset R[X]) :
    s.prod.reverse = (s.map reverse).prod := by
  induction s using Multiset.induction_on with
  | empty => simp [reverse]
  | cons F s ih => simp [reverse_mul_of_domain, ih]

theorem reverse_X_sub_C (a : ℂ) :
    (Polynomial.X - Polynomial.C a : ℂ[X]).reverse =
      1 - Polynomial.C a * Polynomial.X := by
  rw [reverse, natDegree_X_sub_C, reflect_sub, reflect_one_X,
    reflect_C, pow_one]

theorem artinLPolynomial_eq_prod_roots
    {p : ℕ} [NeZero p] [Fact p.Prime]
    (coeff : ZMod p → ZMod p)
    (hne : (InverseRational.poleSupport coeff).Nonempty) :
    artinLPolynomial coeff =
      ((artinLPolynomial coeff).reverse.roots.map
        (fun a ↦ (1 : ℂ[X]) - Polynomial.C a * Polynomial.X)).prod := by
  let A := artinLPolynomial coeff
  let Q := A.reverse
  have hA0 : A.coeff 0 ≠ 0 := by
    change (artinLPolynomial coeff).coeff 0 ≠ 0
    rw [coeff_zero_artinLPolynomial coeff hne]
    exact one_ne_zero
  have hQmonic : Q.Monic := monic_reverse_artinLPolynomial coeff hne
  have hsplit : Q.Splits := IsAlgClosed.splits Q
  have hfactor := hsplit.eq_prod_roots_of_monic hQmonic
  have hreversed := congrArg reverse hfactor
  rw [reverse_reverse_of_coeff_zero_ne_zero hA0] at hreversed
  rw [reverse_multiset_prod_of_domain] at hreversed
  simpa only [Q, A, Multiset.map_map, Function.comp_apply,
    reverse_X_sub_C] using hreversed

theorem card_roots_reverse_artinLPolynomial_lt
    {p : ℕ} [NeZero p] [Fact p.Prime]
    (coeff : ZMod p → ZMod p)
    (hne : (InverseRational.poleSupport coeff).Nonempty) :
    Multiset.card (artinLPolynomial coeff).reverse.roots <
      2 * (InverseRational.poleSupport coeff).card := by
  rw [Polynomial.splits_iff_card_roots.mp
    (IsAlgClosed.splits (artinLPolynomial coeff).reverse)]
  exact (reverse_natDegree_le _).trans_lt
    (natDegree_artinLPolynomial_lt coeff hne)

noncomputable def reciprocalRootFactor (a : ℂ) : PowerSeries ℂ :=
  1 - PowerSeries.C a * PowerSeries.X

noncomputable def reciprocalRootLogTerm (a : ℂ) : PowerSeries ℂ :=
  PowerSeries.C (-a) * PowerSeries.X * localEuler 1 a

noncomputable def reciprocalRootProduct
    (s : Multiset ℂ) : PowerSeries ℂ :=
  (s.map reciprocalRootFactor).prod

noncomputable def reciprocalRootLogDerivative
    (s : Multiset ℂ) : PowerSeries ℂ :=
  (s.map reciprocalRootLogTerm).sum

@[simp]

theorem reciprocalRootProduct_cons (a : ℂ) (s : Multiset ℂ) :
    reciprocalRootProduct (a ::ₘ s) =
      reciprocalRootFactor a * reciprocalRootProduct s := by
  simp [reciprocalRootProduct]

@[simp]

theorem reciprocalRootLogDerivative_cons
    (a : ℂ) (s : Multiset ℂ) :
    reciprocalRootLogDerivative (a ::ₘ s) =
      reciprocalRootLogTerm a + reciprocalRootLogDerivative s := by
  simp [reciprocalRootLogDerivative]

theorem X_mul_derivative_reciprocalRootFactor (a : ℂ) :
    PowerSeries.X *
        PowerSeries.derivative ℂ (reciprocalRootFactor a) =
      reciprocalRootFactor a * reciprocalRootLogTerm a := by
  have hinverse : localEuler 1 a * reciprocalRootFactor a = 1 := by
    simpa only [reciprocalRootFactor, pow_one] using
      (localEuler_mul_one_sub (R := ℂ) a (e := 1) one_ne_zero)
  have hderivative :
      PowerSeries.derivative ℂ (reciprocalRootFactor a) =
        PowerSeries.C (-a) := by
    change PowerSeries.derivative ℂ
      (1 - PowerSeries.C a * PowerSeries.X) = _
    rw [map_sub, ← map_one (PowerSeries.C (R := ℂ)),
      PowerSeries.derivative_C, Derivation.leibniz,
      PowerSeries.derivative_C, PowerSeries.derivative_X]
    simp only [smul_eq_mul, mul_zero, add_zero, mul_one, zero_sub, map_neg]
  rw [hderivative]
  calc
    PowerSeries.X * PowerSeries.C (-a) =
        PowerSeries.C (-a) * PowerSeries.X := mul_comm _ _
    _ = PowerSeries.C (-a) * PowerSeries.X *
        (localEuler 1 a * reciprocalRootFactor a) := by
      rw [hinverse, mul_one]
    _ = reciprocalRootFactor a * reciprocalRootLogTerm a := by
      simp only [reciprocalRootLogTerm]
      ac_rfl

theorem coeff_reciprocalRootLogTerm (a : ℂ) {n : Nat}
    (hn : n ≠ 0) :
    PowerSeries.coeff n (reciprocalRootLogTerm a) = -(a ^ n) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  rw [reciprocalRootLogTerm]
  rw [show PowerSeries.C (-a) * PowerSeries.X * localEuler 1 a =
      PowerSeries.C (-a) * (PowerSeries.X * localEuler 1 a) by
        rw [mul_assoc]]
  rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_succ_X_mul,
    coeff_localEuler a one_ne_zero, if_pos (one_dvd k)]
  simp only [Nat.div_one]
  rw [pow_succ]
  ring

theorem X_mul_derivative_reciprocalRootProduct
    (s : Multiset ℂ) :
    PowerSeries.X *
        PowerSeries.derivative ℂ (reciprocalRootProduct s) =
      reciprocalRootProduct s * reciprocalRootLogDerivative s := by
  induction s using Multiset.induction_on with
  | empty =>
      simp [reciprocalRootProduct, reciprocalRootLogDerivative]
  | cons a s ih =>
      rw [reciprocalRootProduct_cons,
        reciprocalRootLogDerivative_cons]
      rw [Derivation.leibniz]
      simp only [smul_eq_mul]
      calc
        PowerSeries.X *
            (reciprocalRootFactor a *
                PowerSeries.derivative ℂ (reciprocalRootProduct s) +
              reciprocalRootProduct s *
                PowerSeries.derivative ℂ (reciprocalRootFactor a)) =
            reciprocalRootFactor a *
                (PowerSeries.X *
                  PowerSeries.derivative ℂ (reciprocalRootProduct s)) +
              reciprocalRootProduct s *
                (PowerSeries.X *
                  PowerSeries.derivative ℂ (reciprocalRootFactor a)) := by
          rw [mul_add]
          congr 1 <;> ac_rfl
        _ = reciprocalRootFactor a *
              (reciprocalRootProduct s * reciprocalRootLogDerivative s) +
            reciprocalRootProduct s *
              (reciprocalRootFactor a * reciprocalRootLogTerm a) := by
          rw [ih, X_mul_derivative_reciprocalRootFactor]
        _ = reciprocalRootFactor a * reciprocalRootProduct s *
            (reciprocalRootLogTerm a + reciprocalRootLogDerivative s) := by
          rw [mul_add]
          ac_rfl

theorem coeff_reciprocalRootLogDerivative
    (s : Multiset ℂ) {n : Nat} (hn : n ≠ 0) :
    PowerSeries.coeff n (reciprocalRootLogDerivative s) =
      -(s.map (fun a ↦ a ^ n)).sum := by
  induction s using Multiset.induction_on with
  | empty => simp [reciprocalRootLogDerivative]
  | cons a s ih =>
      rw [reciprocalRootLogDerivative_cons, Multiset.map_cons,
        Multiset.sum_cons]
      change PowerSeries.coeff n
          (reciprocalRootLogTerm a + reciprocalRootLogDerivative s) =
        -(a ^ n + (s.map (fun z ↦ z ^ n)).sum)
      rw [map_add, coeff_reciprocalRootLogTerm a hn, ih]
      rw [neg_add]

theorem constantCoeff_reciprocalRootLogDerivative
    (s : Multiset ℂ) :
    PowerSeries.constantCoeff (reciprocalRootLogDerivative s) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  induction s using Multiset.induction_on with
  | empty => simp [reciprocalRootLogDerivative]
  | cons a s ih =>
      rw [reciprocalRootLogDerivative_cons, map_add, ih, add_zero,
        reciprocalRootLogTerm]
      rw [show PowerSeries.C (-a) * PowerSeries.X * localEuler 1 a =
          PowerSeries.C (-a) * (PowerSeries.X * localEuler 1 a) by
        rw [mul_assoc], PowerSeries.coeff_C_mul,
        PowerSeries.coeff_zero_X_mul, mul_zero]

theorem coe_artinLPolynomial_eq_reciprocalRootProduct
    {p : ℕ} [NeZero p] [Fact p.Prime]
    (coeff : ZMod p → ZMod p)
    (hne : (InverseRational.poleSupport coeff).Nonempty) :
    (artinLPolynomial coeff : PowerSeries ℂ) =
      reciprocalRootProduct (artinLPolynomial coeff).reverse.roots := by
  let s := (artinLPolynomial coeff).reverse.roots
  calc
    (artinLPolynomial coeff : PowerSeries ℂ) =
        (((s.map
          (fun a ↦ 1 - Polynomial.C a * Polynomial.X)).prod :
            Polynomial ℂ) : PowerSeries ℂ) :=
      congrArg (fun F : Polynomial ℂ ↦ (F : PowerSeries ℂ))
        (artinLPolynomial_eq_prod_roots coeff hne)
    _ = (s.map
          (fun a ↦ ((((1 : Polynomial ℂ) -
            Polynomial.C a * Polynomial.X) : Polynomial ℂ) :
              PowerSeries ℂ))).prod := by
      induction s using Multiset.induction_on with
      | empty => simp
      | cons a s ih => simp [ih]
    _ = reciprocalRootProduct s := by
      rw [reciprocalRootProduct]
      apply congrArg Multiset.prod
      apply Multiset.map_congr rfl
      intro a ha
      rw [Polynomial.coe_sub, Polynomial.coe_mul, Polynomial.coe_one,
        Polynomial.coe_C, Polynomial.coe_X]
      rfl

theorem X_mul_derivative_artinLPolynomial
    {p : ℕ} [NeZero p] [Fact p.Prime]
    (coeff : ZMod p → ZMod p)
    (hne : (InverseRational.poleSupport coeff).Nonempty) :
    PowerSeries.X * PowerSeries.derivative ℂ
        (artinLPolynomial coeff : PowerSeries ℂ) =
      (artinLPolynomial coeff : PowerSeries ℂ) *
        reciprocalRootLogDerivative
          (artinLPolynomial coeff).reverse.roots := by
  rw [coe_artinLPolynomial_eq_reciprocalRootProduct coeff hne]
  exact X_mul_derivative_reciprocalRootProduct _

end RationalWeil

end Erdos387

end

/-! ## ErdosProblems.Erdos387.RationalEulerRootIdentity -/

noncomputable section

namespace Erdos387

open Polynomial PowerSeries

open scoped BigOperators PowerSeries

namespace RationalWeil

theorem coeff_finiteEulerProduct_eq_coeff_artinLPolynomial
    {p : ℕ} [NeZero p] [Fact p.Prime]
    (coeff : ZMod p → ZMod p)
    (hne : (InverseRational.poleSupport coeff).Nonempty)
    {N j : ℕ} (hjN : j ≤ N) :
    PowerSeries.coeff j
        (finiteEulerProduct
          (fun P : MonicIrreducibleLE (ZMod p) N ↦
            polynomialWeight coeff P.poly)) =
      PowerSeries.coeff j
        (artinLPolynomial coeff : PowerSeries ℂ) := by
  classical
  rw [finiteEulerProduct,
    coeff_localEulerProduct_polynomialWeight_eq_monicWeightSum coeff hjN,
    Polynomial.coeff_coe,
    coeff_artinLPolynomial_eq_monicWeightSum coeff hne]

theorem coeff_zero_finiteEulerProduct_polynomialWeight
    {p : ℕ} [NeZero p] [Fact p.Prime]
    (coeff : ZMod p → ZMod p) {N : ℕ} :
    PowerSeries.coeff 0
        (finiteEulerProduct
          (fun P : MonicIrreducibleLE (ZMod p) N ↦
            polynomialWeight coeff P.poly)) = 1 := by
  classical
  rw [finiteEulerProduct,
    coeff_localEulerProduct_polynomialWeight_eq_monicWeightSum coeff
      (Nat.zero_le N),
    monicWeightSum_zero]

theorem coeff_finiteEulerLogDerivative_polynomialWeight_eq_neg_powerSum
    {p : ℕ} [NeZero p] [Fact p.Prime]
    (coeff : ZMod p → ZMod p)
    (hne : (InverseRational.poleSupport coeff).Nonempty)
    {N n : ℕ} (hnN : n ≤ N) (hn : n ≠ 0) :
    PowerSeries.coeff n
        (finiteEulerLogDerivative
          (fun P : MonicIrreducibleLE (ZMod p) N ↦
            polynomialWeight coeff P.poly)) =
      -((artinLPolynomial coeff).reverse.roots.map
        (fun a ↦ a ^ n)).sum := by
  let w : MonicIrreducibleLE (ZMod p) N → ℂ :=
    fun P ↦ polynomialWeight coeff P.poly
  calc
    PowerSeries.coeff n (finiteEulerLogDerivative w) =
        PowerSeries.coeff n (reciprocalRootLogDerivative
          (artinLPolynomial coeff).reverse.roots) := by
      exact coeff_logDerivative_eq_of_coeff_eq_up_to
        (X_mul_derivativeFun_finiteEulerProduct w)
        (X_mul_derivative_artinLPolynomial coeff hne)
        (constantCoeff_finiteEulerLogDerivative w)
        (constantCoeff_reciprocalRootLogDerivative _)
        (coeff_zero_finiteEulerProduct_polynomialWeight coeff)
        (fun j hj ↦
          coeff_finiteEulerProduct_eq_coeff_artinLPolynomial coeff hne hj)
        hnN
    _ = -((artinLPolynomial coeff).reverse.roots.map
        (fun a ↦ a ^ n)).sum :=
      coeff_reciprocalRootLogDerivative _ hn

theorem irreducible_sum_eq_neg_artinRootPowerSum
    {p : ℕ} [NeZero p] [Fact p.Prime]
    (coeff : ZMod p → ZMod p)
    (hne : (InverseRational.poleSupport coeff).Nonempty)
    {N n : ℕ} (hnN : n ≤ N) (hn : n ≠ 0) :
    (∑ P : MonicIrreducibleLE (ZMod p) N,
      if P.poly.natDegree ∣ n then
        (P.poly.natDegree : ℂ) *
          polynomialWeight coeff P.poly ^
            (n / P.poly.natDegree)
      else 0) =
      -((artinLPolynomial coeff).reverse.roots.map
        (fun a ↦ a ^ n)).sum := by
  rw [← coeff_finiteEulerLogDerivative hn]
  exact coeff_finiteEulerLogDerivative_polynomialWeight_eq_neg_powerSum
    coeff hne hnN hn

end RationalWeil

end Erdos387

end

/-! ## ErdosProblems.Erdos387.RationalRootPhase -/

noncomputable section

namespace Erdos387

open Polynomial

open scoped BigOperators

namespace RationalWeil

noncomputable def mappedSimplePolePhase
    {p : ℕ} [NeZero p] {E : Type*} [Field E] [Algebra (ZMod p) E]
    (coeff : ZMod p → ZMod p) (x : E) : E :=
  ∑ r ∈ InverseRational.poleSupport coeff,
    algebraMap (ZMod p) E (coeff r) *
      (x - algebraMap (ZMod p) E r)⁻¹

theorem neg_sum_mul_rootRecip_eq_sum_mappedSimplePolePhase
    {p : ℕ} [NeZero p] {E : Type*} [Field E] [Algebra (ZMod p) E]
    (coeff : ZMod p → ZMod p) (roots : Multiset E) :
    -(∑ r ∈ InverseRational.poleSupport coeff,
        algebraMap (ZMod p) E (coeff r) *
          (roots.map fun x =>
            (algebraMap (ZMod p) E r - x)⁻¹).sum) =
      (roots.map (mappedSimplePolePhase coeff)).sum := by
  classical
  induction roots using Multiset.induction_on with
  | empty => simp
  | @cons x roots ih =>
      simp only [Multiset.map_cons, Multiset.sum_cons,
        mappedSimplePolePhase, mul_add, Finset.sum_add_distrib]
      rw [neg_add, ih]
      congr 1
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro r hr
      rw [show algebraMap (ZMod p) E r - x =
          -(x - algebraMap (ZMod p) E r) by ring,
        inv_neg]
      ring

theorem map_logarithmicDerivativePhase_eq_sum_roots
    {p : ℕ} [NeZero p] [Fact p.Prime]
    {E : Type*} [Field E] [Algebra (ZMod p) E]
    (coeff : ZMod p → ZMod p) {F : (ZMod p)[X]}
    (hF : AvoidsPoleSupport coeff F)
    (hSplit : (F.map (algebraMap (ZMod p) E)).Splits) :
    algebraMap (ZMod p) E (logarithmicDerivativePhase coeff F) =
      (((F.map (algebraMap (ZMod p) E)).roots.map
        (mappedSimplePolePhase coeff)).sum) := by
  classical
  let f : (ZMod p)[X] →+* E[X] := mapRingHom (algebraMap (ZMod p) E)
  have hratio (r : ZMod p)
      (hr : r ∈ InverseRational.poleSupport coeff) :
      algebraMap (ZMod p) E
          (eval r F.derivative * (eval r F)⁻¹) =
        (((F.map (algebraMap (ZMod p) E)).roots.map fun x =>
          (algebraMap (ZMod p) E r - x)⁻¹).sum) := by
    have hden :
        eval (algebraMap (ZMod p) E r)
            (F.map (algebraMap (ZMod p) E)) ≠ 0 := by
      rw [eval_map_apply]
      intro hzero
      apply hF r hr
      apply (algebraMap (ZMod p) E).injective
      simpa using hzero
    calc
      algebraMap (ZMod p) E
          (eval r F.derivative * (eval r F)⁻¹) =
          eval (algebraMap (ZMod p) E r)
              (F.map (algebraMap (ZMod p) E)).derivative /
            eval (algebraMap (ZMod p) E r)
              (F.map (algebraMap (ZMod p) E)) := by
        simp only [map_mul, map_inv₀, div_eq_mul_inv,
          derivative_map, eval_map_apply]
      _ = _ := by
        simpa only [one_div] using
          hSplit.eval_derivative_div_eval_of_ne_zero hden
  rw [logarithmicDerivativePhase, map_neg, map_sum]
  simp only [map_mul]
  calc
    -(∑ r ∈ InverseRational.poleSupport coeff,
        algebraMap (ZMod p) E (coeff r) *
          algebraMap (ZMod p) E (eval r F.derivative) *
            algebraMap (ZMod p) E (eval r F)⁻¹) =
        -(∑ r ∈ InverseRational.poleSupport coeff,
          algebraMap (ZMod p) E (coeff r) *
            (((F.map (algebraMap (ZMod p) E)).roots.map fun x =>
              (algebraMap (ZMod p) E r - x)⁻¹).sum)) := by
      congr 1
      apply Finset.sum_congr rfl
      intro r hr
      calc
        algebraMap (ZMod p) E (coeff r) *
            algebraMap (ZMod p) E (eval r F.derivative) *
              algebraMap (ZMod p) E (eval r F)⁻¹ =
            algebraMap (ZMod p) E (coeff r) *
              algebraMap (ZMod p) E
                (eval r F.derivative * (eval r F)⁻¹) := by
          rw [map_mul]
          ring
        _ = _ := by rw [hratio r hr]
    _ = _ :=
      neg_sum_mul_rootRecip_eq_sum_mappedSimplePolePhase coeff _

end RationalWeil

end Erdos387

end

/-! ## ErdosProblems.Erdos387.RationalTraceBridge -/

noncomputable section

namespace Erdos387

open IntermediateField Polynomial

open scoped BigOperators

namespace RationalWeil

theorem mappedSimplePolePhase_map_ringHom
    {p : ℕ} [NeZero p]
    {E S : Type*} [Field E] [Field S]
    [Algebra (ZMod p) E] [Algebra (ZMod p) S]
    (f : E →+* S)
    (hcomm : ∀ a : ZMod p,
      f (algebraMap (ZMod p) E a) = algebraMap (ZMod p) S a)
    (coeff : ZMod p → ZMod p) (x : E) :
    f (mappedSimplePolePhase coeff x) =
      mappedSimplePolePhase coeff (f x) := by
  classical
  rw [mappedSimplePolePhase, mappedSimplePolePhase, map_sum]
  apply Finset.sum_congr rfl
  intro r hr
  simp only [map_mul, map_inv₀, map_sub]
  rw [hcomm, hcomm]

theorem mappedSimplePolePhase_map
    {p : ℕ} [NeZero p]
    {E S : Type*} [Field E] [Field S]
    [Algebra (ZMod p) E] [Algebra (ZMod p) S]
    (f : E →ₐ[ZMod p] S) (coeff : ZMod p → ZMod p) (x : E) :
    f (mappedSimplePolePhase coeff x) =
      mappedSimplePolePhase coeff (f x) :=
  mappedSimplePolePhase_map_ringHom f.toRingHom f.commutes coeff x

theorem avoidsPoleSupport_minpoly_of_ne_poles
    {p : ℕ} [NeZero p] [Fact p.Prime]
    {L : Type*} [Field L] [Algebra (ZMod p) L]
    (coeff : ZMod p → ZMod p) (x : L) (hx : IsIntegral (ZMod p) x)
    (hnonpole : ∀ r ∈ InverseRational.poleSupport coeff,
      x ≠ algebraMap (ZMod p) L r) :
    AvoidsPoleSupport coeff (minpoly (ZMod p) x) := by
  intro r hr heval
  have hroot : Polynomial.aeval (algebraMap (ZMod p) L r)
      (minpoly (ZMod p) x) = 0 := by
    rw [aeval_algebraMap_apply_eq_algebraMap_eval, heval, map_zero]
  have heq' :
      minpoly (ZMod p) x =
        minpoly (ZMod p) (algebraMap (ZMod p) L r) :=
    minpoly.eq_of_irreducible_of_monic
      (x := algebraMap (ZMod p) L r) (p := minpoly (ZMod p) x)
      (minpoly.irreducible hx) hroot (minpoly.monic hx)
  have heq := heq'.symm
  rw [minpoly.eq_X_sub_C] at heq
  have hxroot := minpoly.aeval (ZMod p) x
  rw [← heq] at hxroot
  have hxr : x = algebraMap (ZMod p) L r := by
    simpa only [aeval_sub, aeval_X, aeval_C, sub_eq_zero] using hxroot
  exact hnonpole r hr hxr

theorem logarithmicDerivativePhase_minpoly_eq_trace_adjoin
    {p : ℕ} [NeZero p] [Fact p.Prime]
    {L : Type*} [Field L] [Algebra (ZMod p) L]
    (coeff : ZMod p → ZMod p) (x : L)
    (hx : IsIntegral (ZMod p) x) (hsep : IsSeparable (ZMod p) x)
    (hnonpole : ∀ r ∈ InverseRational.poleSupport coeff,
      x ≠ algebraMap (ZMod p) L r) :
    logarithmicDerivativePhase coeff (minpoly (ZMod p) x) =
      Algebra.trace (ZMod p) (ZMod p)⟮x⟯
        (mappedSimplePolePhase coeff
          (IntermediateField.AdjoinSimple.gen (ZMod p) x)) := by
  classical
  let E := AlgebraicClosure L
  let : FiniteDimensional (ZMod p) (ZMod p)⟮x⟯ :=
    IntermediateField.adjoin.finiteDimensional hx
  let : Algebra.IsSeparable (ZMod p) (ZMod p)⟮x⟯ :=
    (IntermediateField.isSeparable_adjoin_simple_iff_isSeparable
      (ZMod p) L).2 hsep
  have havoid : AvoidsPoleSupport coeff (minpoly (ZMod p) x) :=
    avoidsPoleSupport_minpoly_of_ne_poles coeff x hx hnonpole
  apply (algebraMap (ZMod p) E).injective
  rw [map_logarithmicDerivativePhase_eq_sum_roots coeff havoid
      (IsAlgClosed.splits _),
    trace_eq_sum_embeddings E]
  have hemb :
      (∑ σ : (ZMod p)⟮x⟯ →ₐ[ZMod p] E,
        σ (mappedSimplePolePhase coeff
          (IntermediateField.AdjoinSimple.gen (ZMod p) x))) =
        ∑ y : {y // y ∈ (minpoly (ZMod p) x).aroots E},
          mappedSimplePolePhase coeff (y : E) := by
    let e := IntermediateField.algHomAdjoinIntegralEquiv
      (ZMod p) (K := E) hx
    apply Fintype.sum_equiv e
    intro σ
    have heval : (e σ : E) =
        σ (IntermediateField.AdjoinSimple.gen (ZMod p) x) := by
      symm
      simpa [e] using
        IntermediateField.algHomAdjoinIntegralEquiv_symm_apply_gen
          (ZMod p) hx (e σ)
    rw [mappedSimplePolePhase_map σ coeff]
    rw [heval]
  rw [hemb]
  rw [Finset.sum_mem_multiset, Finset.sum_eq_multiset_sum,
    Multiset.toFinset_val,
    Multiset.dedup_eq_self.mpr
      (nodup_roots ((Polynomial.separable_map _).mpr hsep))]
  intro y
  rfl

theorem polynomialWeight_minpoly_eq_character_trace_adjoin
    {p : ℕ} [NeZero p] [Fact p.Prime]
    {L : Type*} [Field L] [Algebra (ZMod p) L]
    (coeff : ZMod p → ZMod p) (x : L)
    (hx : IsIntegral (ZMod p) x) (hsep : IsSeparable (ZMod p) x)
    (hnonpole : ∀ r ∈ InverseRational.poleSupport coeff,
      x ≠ algebraMap (ZMod p) L r) :
    polynomialWeight coeff (minpoly (ZMod p) x) =
      ZMod.stdAddChar
        (Algebra.trace (ZMod p) (ZMod p)⟮x⟯
          (mappedSimplePolePhase coeff
            (IntermediateField.AdjoinSimple.gen (ZMod p) x))) := by
  rw [polynomialWeight,
    if_pos (avoidsPoleSupport_minpoly_of_ne_poles coeff x hx hnonpole),
    logarithmicDerivativePhase_minpoly_eq_trace_adjoin
      coeff x hx hsep hnonpole]

theorem character_trace_mappedSimplePolePhase_eq_polynomialWeight_pow
    {p : ℕ} [NeZero p] [Fact p.Prime]
    {L : Type*} [Field L] [Algebra (ZMod p) L]
    [FiniteDimensional (ZMod p) L]
    (coeff : ZMod p → ZMod p) (x : L)
    (hsep : IsSeparable (ZMod p) x)
    (hnonpole : ∀ r ∈ InverseRational.poleSupport coeff,
      x ≠ algebraMap (ZMod p) L r) :
    ZMod.stdAddChar
        (Algebra.trace (ZMod p) L (mappedSimplePolePhase coeff x)) =
      polynomialWeight coeff (minpoly (ZMod p) x) ^
        Module.finrank (ZMod p)⟮x⟯ L := by
  let y : (ZMod p)⟮x⟯ :=
    mappedSimplePolePhase coeff
      (IntermediateField.AdjoinSimple.gen (ZMod p) x)
  have hpoint : algebraMap (ZMod p)⟮x⟯ L y =
      mappedSimplePolePhase coeff x := by
    dsimp only [y]
    rw [mappedSimplePolePhase_map_ringHom
      (algebraMap (ZMod p)⟮x⟯ L)
      (fun a => IsScalarTower.algebraMap_apply (ZMod p) (ZMod p)⟮x⟯ L a)
      coeff]
    congr 1
  have htrace :
      Algebra.trace (ZMod p) L (algebraMap (ZMod p)⟮x⟯ L y) =
        Module.finrank (ZMod p)⟮x⟯ L •
          Algebra.trace (ZMod p) (ZMod p)⟮x⟯ y := by
    calc
      Algebra.trace (ZMod p) L (algebraMap (ZMod p)⟮x⟯ L y) =
          Algebra.trace (ZMod p) (ZMod p)⟮x⟯
            (Algebra.trace (ZMod p)⟮x⟯ L
              (algebraMap (ZMod p)⟮x⟯ L y)) := by
        rw [Algebra.trace_trace]
      _ = Algebra.trace (ZMod p) (ZMod p)⟮x⟯
          (Module.finrank (ZMod p)⟮x⟯ L • y) := by
        rw [Algebra.trace_algebraMap]
      _ = Module.finrank (ZMod p)⟮x⟯ L •
          Algebra.trace (ZMod p) (ZMod p)⟮x⟯ y := by
        exact map_nsmul (Algebra.trace (ZMod p) (ZMod p)⟮x⟯) _ _
  rw [← hpoint, htrace, AddChar.map_nsmul_eq_pow,
    ← polynomialWeight_minpoly_eq_character_trace_adjoin
      coeff x hsep.isIntegral hsep hnonpole]

theorem character_trace_mappedSimplePolePhase_eq_polynomialWeight_pow_div
    {p : ℕ} [NeZero p] [Fact p.Prime]
    {L : Type*} [Field L] [Algebra (ZMod p) L]
    [FiniteDimensional (ZMod p) L]
    (coeff : ZMod p → ZMod p) (x : L)
    (hsep : IsSeparable (ZMod p) x)
    (hnonpole : ∀ r ∈ InverseRational.poleSupport coeff,
      x ≠ algebraMap (ZMod p) L r) :
    ZMod.stdAddChar
        (Algebra.trace (ZMod p) L (mappedSimplePolePhase coeff x)) =
      polynomialWeight coeff (minpoly (ZMod p) x) ^
        (Module.finrank (ZMod p) L /
          (minpoly (ZMod p) x).natDegree) := by
  have hrelative :
      Module.finrank (ZMod p)⟮x⟯ L =
        Module.finrank (ZMod p) L /
          (minpoly (ZMod p) x).natDegree := by
    rw [← IntermediateField.adjoin.finrank hsep.isIntegral,
      ← Module.finrank_mul_finrank (ZMod p) (ZMod p)⟮x⟯ L,
      Nat.mul_div_cancel_left _ Module.finrank_pos]
  rw [← hrelative]
  exact character_trace_mappedSimplePolePhase_eq_polynomialWeight_pow
    coeff x hsep hnonpole

noncomputable def extensionPointWeight
    {p : ℕ} [NeZero p] [Fact p.Prime]
    {L : Type*} [Field L] [Algebra (ZMod p) L]
    [FiniteDimensional (ZMod p) L]
    (coeff : ZMod p → ZMod p) (x : L) : ℂ :=
  polynomialWeight coeff (minpoly (ZMod p) x) ^
    (Module.finrank (ZMod p) L / (minpoly (ZMod p) x).natDegree)

theorem extensionPointWeight_eq_character_trace_of_ne_poles
    {p : ℕ} [NeZero p] [Fact p.Prime]
    {L : Type*} [Field L] [Algebra (ZMod p) L]
    [FiniteDimensional (ZMod p) L]
    (coeff : ZMod p → ZMod p) (x : L)
    (hsep : IsSeparable (ZMod p) x)
    (hnonpole : ∀ r ∈ InverseRational.poleSupport coeff,
      x ≠ algebraMap (ZMod p) L r) :
    extensionPointWeight coeff x =
      ZMod.stdAddChar
        (Algebra.trace (ZMod p) L (mappedSimplePolePhase coeff x)) := by
  exact (character_trace_mappedSimplePolePhase_eq_polynomialWeight_pow_div
    coeff x hsep hnonpole).symm

def IsMappedPole
    {p : ℕ} [NeZero p]
    {L : Type*} [Field L] [Algebra (ZMod p) L]
    (coeff : ZMod p → ZMod p) (x : L) : Prop :=
  ∃ r ∈ InverseRational.poleSupport coeff,
    x = algebraMap (ZMod p) L r

noncomputable def zeroExtendedTraceWeight
    {p : ℕ} [NeZero p] [Fact p.Prime]
    {L : Type*} [Field L] [Algebra (ZMod p) L]
    [FiniteDimensional (ZMod p) L]
    (coeff : ZMod p → ZMod p) (x : L) : ℂ := by
  classical
  exact if IsMappedPole coeff x then 0 else
    ZMod.stdAddChar
      (Algebra.trace (ZMod p) L (mappedSimplePolePhase coeff x))

theorem extensionPointWeight_eq_zero_of_mappedPole
    {p : ℕ} [NeZero p] [Fact p.Prime]
    {L : Type*} [Field L] [Algebra (ZMod p) L]
    [FiniteDimensional (ZMod p) L]
    (coeff : ZMod p → ZMod p) {x : L}
    (hx : IsMappedPole coeff x) :
    extensionPointWeight coeff x = 0 := by
  obtain ⟨r, hr, rfl⟩ := hx
  rw [extensionPointWeight, minpoly.eq_X_sub_C,
    polynomialWeight_X_sub_C_of_mem coeff hr]
  have hfinrank : 0 < Module.finrank (ZMod p) L := Module.finrank_pos
  rw [natDegree_X_sub_C, Nat.div_one, zero_pow hfinrank.ne']

theorem extensionPointWeight_eq_zeroExtendedTraceWeight
    {p : ℕ} [NeZero p] [Fact p.Prime]
    {L : Type*} [Field L] [Algebra (ZMod p) L]
    [Finite L] [FiniteDimensional (ZMod p) L]
    (coeff : ZMod p → ZMod p) (x : L) :
    extensionPointWeight coeff x = zeroExtendedTraceWeight coeff x := by
  classical
  by_cases hx : IsMappedPole coeff x
  · rw [zeroExtendedTraceWeight, if_pos hx,
      extensionPointWeight_eq_zero_of_mappedPole coeff hx]
  · rw [zeroExtendedTraceWeight, if_neg hx]
    apply extensionPointWeight_eq_character_trace_of_ne_poles
      coeff x (Algebra.IsSeparable.isSeparable (ZMod p) x)
    intro r hr hxr
    apply hx
    exact ⟨r, hr, hxr⟩

end RationalWeil

end Erdos387

end

/-! ## ErdosProblems.Erdos387.RationalClosedPoints -/

noncomputable section

namespace Erdos387

open Polynomial

open scoped BigOperators

namespace RationalWeil

def ExtensionClosedPoint (K : Type*) [Field K] (n : Nat) :=
  {P : MonicIrreducibleLE K n // P.poly.natDegree ∣ n}

namespace ExtensionClosedPoint

variable {K : Type*} [Field K] {n : Nat}

def poly (P : ExtensionClosedPoint K n) : K[X] := P.1.poly

theorem monic (P : ExtensionClosedPoint K n) : P.poly.Monic := P.1.monic

theorem irreducible (P : ExtensionClosedPoint K n) : Irreducible P.poly :=
  P.1.irreducible

theorem natDegree_dvd (P : ExtensionClosedPoint K n) : P.poly.natDegree ∣ n :=
  P.2

end ExtensionClosedPoint

variable (K : Type*) [Field K] [Fintype K]

variable (p n : Nat) [Fact p.Prime] [CharP K p] [NeZero n]

noncomputable local instance : Fintype (FiniteField.Extension K p n) :=
  Fintype.ofFinite _

private noncomputable def RationalClosedPoints_conjugacyClassClosedPoint
    (c : ConjRootClass K (FiniteField.Extension K p n)) :
    ExtensionClosedPoint K n := by
  let P : K[X] := c.minpoly
  have hdiv : P.natDegree ∣ n := by
    rw [← FiniteField.finrank_extension K p n]
    exact c.irreducible_minpoly.natDegree_dvd_finrank c.splits_minpoly
  exact
    ⟨{ poly := P
       irreducible := c.irreducible_minpoly
       monic := c.monic_minpoly
       natDegree_le := Nat.le_of_dvd (NeZero.pos n) hdiv }, hdiv⟩

private theorem RationalClosedPoints_conjugacyClassClosedPoint_injective :
    Function.Injective (RationalClosedPoints_conjugacyClassClosedPoint K p n) := by
  intro c d h
  apply ConjRootClass.minpoly_injective
  exact congrArg (fun P : ExtensionClosedPoint K n ↦ P.poly) h

omit [Fintype K] in

private theorem RationalClosedPoints_exists_minpoly_eq_closedPoint [Finite K]
    (P : ExtensionClosedPoint K n) :
    ∃ x : FiniteField.Extension K p n, minpoly K x = P.poly := by
  let : Fact (Irreducible P.poly) := ⟨P.irreducible⟩
  have hfinrank : Module.finrank K (AdjoinRoot P.poly) = P.poly.natDegree := by
    rw [(AdjoinRoot.powerBasis P.irreducible.ne_zero).finrank,
      AdjoinRoot.powerBasis_dim]
  have hdvd : Module.finrank K (AdjoinRoot P.poly) ∣
      Module.finrank K (FiniteField.Extension K p n) := by
    rw [hfinrank, FiniteField.finrank_extension K p n]
    exact P.natDegree_dvd
  let f : AdjoinRoot P.poly →ₐ[K] FiniteField.Extension K p n :=
    (FiniteField.nonempty_algHom_of_finrank_dvd hdvd).some
  let x : FiniteField.Extension K p n := f (AdjoinRoot.root P.poly)
  refine ⟨x, ?_⟩
  have hroot : aeval (AdjoinRoot.root P.poly) P.poly = 0 := by
    rw [Polynomial.aeval_def]
    exact AdjoinRoot.eval₂_root P.poly
  have hminpoly : minpoly K (AdjoinRoot.root P.poly) = P.poly := by
    have h := minpoly.eq_of_irreducible P.irreducible hroot
    simpa [P.monic.leadingCoeff] using h.symm
  calc
    minpoly K x = minpoly K (AdjoinRoot.root P.poly) :=
      minpoly.algHom_eq f f.injective _
    _ = P.poly := hminpoly

private theorem RationalClosedPoints_conjugacyClassClosedPoint_surjective :
    Function.Surjective (RationalClosedPoints_conjugacyClassClosedPoint K p n) := by
  intro P
  obtain ⟨x, hx⟩ := RationalClosedPoints_exists_minpoly_eq_closedPoint K p n P
  refine ⟨ConjRootClass.mk K x, ?_⟩
  apply Subtype.ext
  apply MonicIrreducibleLE.poly_injective
  exact hx

noncomputable def conjugacyClassEquivClosedPoint :
    ConjRootClass K (FiniteField.Extension K p n) ≃ ExtensionClosedPoint K n :=
  Equiv.ofBijective (RationalClosedPoints_conjugacyClassClosedPoint K p n)
    ⟨RationalClosedPoints_conjugacyClassClosedPoint_injective K p n,
      RationalClosedPoints_conjugacyClassClosedPoint_surjective K p n⟩

noncomputable local instance : Fintype (ExtensionClosedPoint K n) := by
  unfold ExtensionClosedPoint
  infer_instance

noncomputable local instance :
    Fintype (ConjRootClass K (FiniteField.Extension K p n)) :=
  Fintype.ofEquiv (ExtensionClosedPoint K n)
    (conjugacyClassEquivClosedPoint K p n).symm

noncomputable local instance
    (c : ConjRootClass K (FiniteField.Extension K p n)) : Fintype c.carrier :=
  Fintype.ofFinite _

section ArbitraryExtension

variable (L : Type*) [Field L] [Finite L] [Algebra K L]

variable [FiniteDimensional K L]

noncomputable local instance : Fintype L := Fintype.ofFinite _

private noncomputable def RationalClosedPoints_finiteConjugacyClassClosedPoint
    (hfin : Module.finrank K L = n)
    (c : ConjRootClass K L) : ExtensionClosedPoint K n := by
  let P : K[X] := c.minpoly
  have hdiv : P.natDegree ∣ n := by
    rw [← hfin]
    exact c.irreducible_minpoly.natDegree_dvd_finrank c.splits_minpoly
  exact
    ⟨{ poly := P
       irreducible := c.irreducible_minpoly
       monic := c.monic_minpoly
       natDegree_le := Nat.le_of_dvd (NeZero.pos n) hdiv }, hdiv⟩

omit [Fintype K] [FiniteDimensional K L] in

private theorem RationalClosedPoints_finiteConjugacyClassClosedPoint_injective
    (hfin : Module.finrank K L = n) :
    Function.Injective (RationalClosedPoints_finiteConjugacyClassClosedPoint K n L hfin) := by
  intro c d h
  apply ConjRootClass.minpoly_injective
  exact congrArg (fun P : ExtensionClosedPoint K n ↦ P.poly) h

omit [Fintype K] [NeZero n] [FiniteDimensional K L] in

private theorem RationalClosedPoints_exists_minpoly_eq_closedPoint_in_finiteExtension
    (hfin : Module.finrank K L = n)
    (P : ExtensionClosedPoint K n) :
    ∃ x : L, minpoly K x = P.poly := by
  let : Fact (Irreducible P.poly) := ⟨P.irreducible⟩
  have hrootFinrank :
      Module.finrank K (AdjoinRoot P.poly) = P.poly.natDegree := by
    rw [(AdjoinRoot.powerBasis P.irreducible.ne_zero).finrank,
      AdjoinRoot.powerBasis_dim]
  have hdvd : Module.finrank K (AdjoinRoot P.poly) ∣
      Module.finrank K L := by
    rw [hrootFinrank, hfin]
    exact P.natDegree_dvd
  let f : AdjoinRoot P.poly →ₐ[K] L :=
    (FiniteField.nonempty_algHom_of_finrank_dvd hdvd).some
  let x : L := f (AdjoinRoot.root P.poly)
  refine ⟨x, ?_⟩
  have hroot : aeval (AdjoinRoot.root P.poly) P.poly = 0 := by
    rw [Polynomial.aeval_def]
    exact AdjoinRoot.eval₂_root P.poly
  have hminpoly : minpoly K (AdjoinRoot.root P.poly) = P.poly := by
    have h := minpoly.eq_of_irreducible P.irreducible hroot
    simpa [P.monic.leadingCoeff] using h.symm
  calc
    minpoly K x = minpoly K (AdjoinRoot.root P.poly) :=
      minpoly.algHom_eq f f.injective _
    _ = P.poly := hminpoly

omit [Fintype K] [FiniteDimensional K L] in

private theorem RationalClosedPoints_finiteConjugacyClassClosedPoint_surjective
    (hfin : Module.finrank K L = n) :
    Function.Surjective (RationalClosedPoints_finiteConjugacyClassClosedPoint K n L hfin) := by
  intro P
  obtain ⟨x, hx⟩ :=
    RationalClosedPoints_exists_minpoly_eq_closedPoint_in_finiteExtension K n L hfin P
  refine ⟨ConjRootClass.mk K x, ?_⟩
  apply Subtype.ext
  apply MonicIrreducibleLE.poly_injective
  exact hx

noncomputable def finiteConjugacyClassEquivClosedPoint
    (hfin : Module.finrank K L = n) :
    ConjRootClass K L ≃ ExtensionClosedPoint K n :=
  Equiv.ofBijective (RationalClosedPoints_finiteConjugacyClassClosedPoint K n L hfin)
    ⟨RationalClosedPoints_finiteConjugacyClassClosedPoint_injective K n L hfin,
      RationalClosedPoints_finiteConjugacyClassClosedPoint_surjective K n L hfin⟩

noncomputable local instance : Fintype (ExtensionClosedPoint K n) := by
  unfold ExtensionClosedPoint
  infer_instance

noncomputable local instance
    (c : ConjRootClass K L) : Fintype c.carrier := Fintype.ofFinite _

omit [Fintype K] [FiniteDimensional K L] in

theorem card_finiteConjugacyClass_carrier
    (c : ConjRootClass K L) :
    Fintype.card c.carrier = c.minpoly.natDegree := by
  calc
    Fintype.card c.carrier = Fintype.card (c.minpoly.rootSet L) :=
      Fintype.card_congr
        (Equiv.setCongr c.rootSet_minpoly_eq_carrier).symm
    _ = c.minpoly.natDegree :=
      Polynomial.card_rootSet_eq_natDegree c.separable_minpoly c.splits_minpoly

omit [Fintype K] [NeZero n] in

theorem sum_finiteExtension_eq_sum_conjugacyClasses
    (_hfin : Module.finrank K L = n)
    [Fintype (ConjRootClass K L)]
    {A : Type*} [AddCommMonoid A] (f : K[X] → A) :
    (∑ x : L, f (minpoly K x)) =
      ∑ c : ConjRootClass K L,
        c.minpoly.natDegree • f c.minpoly := by
  classical
  rw [← Fintype.sum_fiberwise (ConjRootClass.mk K)
    (fun x : L ↦ f (minpoly K x))]
  apply Finset.sum_congr rfl
  intro c hc
  calc
    (∑ x : {x : L // ConjRootClass.mk K x = c},
        f (minpoly K x.1)) =
        ∑ _x : {x : L // ConjRootClass.mk K x = c}, f c.minpoly := by
      apply Fintype.sum_congr
      intro x
      rw [← ConjRootClass.minpoly_mk (K := K) x.1, x.2]
    _ = Fintype.card {x : L // ConjRootClass.mk K x = c} •
        f c.minpoly := by
      simp
    _ = Fintype.card c.carrier • f c.minpoly := by
      congr 1
      apply Fintype.card_congr
      exact
        { toFun := fun x ↦ ⟨x.1, x.2⟩
          invFun := fun x ↦ ⟨x.1, x.2⟩
          left_inv := fun _ ↦ rfl
          right_inv := fun _ ↦ rfl }
    _ = c.minpoly.natDegree • f c.minpoly := by
      rw [card_finiteConjugacyClass_carrier K L c]

theorem sum_finiteExtension_eq_irreducibleSum
    (hfin : Module.finrank K L = n)
    {A : Type*} [AddCommMonoid A] (f : K[X] → A) :
    (∑ x : L, f (minpoly K x)) =
      ∑ P : MonicIrreducibleLE K n,
        if P.poly.natDegree ∣ n then P.poly.natDegree • f P.poly else 0 := by
  classical
  let : Fintype (ConjRootClass K L) :=
    Fintype.ofEquiv (ExtensionClosedPoint K n)
      (finiteConjugacyClassEquivClosedPoint K n L hfin).symm
  rw [sum_finiteExtension_eq_sum_conjugacyClasses K n L hfin]
  calc
    (∑ c : ConjRootClass K L,
        c.minpoly.natDegree • f c.minpoly) =
        ∑ P : ExtensionClosedPoint K n, P.poly.natDegree • f P.poly := by
      exact (finiteConjugacyClassEquivClosedPoint K n L hfin).sum_comp
        (fun P ↦ P.poly.natDegree • f P.poly)
    _ = ∑ P ∈ (Finset.univ : Finset (MonicIrreducibleLE K n)).filter
          (fun P ↦ P.poly.natDegree ∣ n), P.poly.natDegree • f P.poly := by
      symm
      apply Finset.sum_subtype
      intro P
      simp
    _ = ∑ P : MonicIrreducibleLE K n,
          if P.poly.natDegree ∣ n then P.poly.natDegree • f P.poly else 0 := by
      exact Finset.sum_filter _ _

end ArbitraryExtension

theorem sum_extension_extensionPointWeight_eq_irreducibleSum
    (p n : ℕ) [NeZero p] [Fact p.Prime] [NeZero n]
    (coeff : ZMod p → ZMod p) :
    (∑ x : FiniteField.Extension (ZMod p) p n,
      extensionPointWeight coeff x) =
      ∑ P : MonicIrreducibleLE (ZMod p) n,
        if P.poly.natDegree ∣ n then
          (P.poly.natDegree : ℂ) *
            polynomialWeight coeff P.poly ^ (n / P.poly.natDegree)
        else 0 := by
  classical
  have hfinrank :
      Module.finrank (ZMod p)
        (FiniteField.Extension (ZMod p) p n) = n := by
    rw [FiniteField.finrank_zmod_extension]
    simp
  have hcore := sum_finiteExtension_eq_irreducibleSum
    (ZMod p) n (FiniteField.Extension (ZMod p) p n) hfinrank
    (fun P : (ZMod p)[X] ↦
      polynomialWeight coeff P ^ (n / P.natDegree))
  calc
    (∑ x : FiniteField.Extension (ZMod p) p n,
        extensionPointWeight coeff x) =
        ∑ x : FiniteField.Extension (ZMod p) p n,
          polynomialWeight coeff (minpoly (ZMod p) x) ^
            (n / (minpoly (ZMod p) x).natDegree) := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [extensionPointWeight]
      rw [hfinrank]
    _ = _ := by
      simpa only [nsmul_eq_mul] using hcore

theorem extensionTraceSum_eq_irreducibleSum
    (p n : ℕ) [NeZero p] [Fact p.Prime] [NeZero n]
    (coeff : ZMod p → ZMod p) :
    (∑ x : FiniteField.Extension (ZMod p) p n,
      zeroExtendedTraceWeight coeff x) =
      ∑ P : MonicIrreducibleLE (ZMod p) n,
        if P.poly.natDegree ∣ n then
          (P.poly.natDegree : ℂ) *
            polynomialWeight coeff P.poly ^ (n / P.poly.natDegree)
        else 0 := by
  classical
  calc
    (∑ x : FiniteField.Extension (ZMod p) p n,
        zeroExtendedTraceWeight coeff x) =
        ∑ x : FiniteField.Extension (ZMod p) p n,
          extensionPointWeight coeff x := by
      apply Finset.sum_congr rfl
      intro x hx
      exact (extensionPointWeight_eq_zeroExtendedTraceWeight coeff x).symm
    _ = _ := sum_extension_extensionPointWeight_eq_irreducibleSum p n coeff

theorem extensionTraceSum_eq_neg_artinRootPowerSum
    (p n : ℕ) [NeZero p] [Fact p.Prime] [NeZero n]
    (coeff : ZMod p → ZMod p)
    (hne : (InverseRational.poleSupport coeff).Nonempty) :
    (∑ x : FiniteField.Extension (ZMod p) p n,
      zeroExtendedTraceWeight coeff x) =
      -((artinLPolynomial coeff).reverse.roots.map
        (fun a ↦ a ^ n)).sum := by
  rw [extensionTraceSum_eq_irreducibleSum p n coeff]
  exact irreducible_sum_eq_neg_artinRootPowerSum
    coeff hne le_rfl (NeZero.ne n)

end RationalWeil

end Erdos387

end

/-! ## Waring.Analytic.BoundedPowerSums -/

noncomputable section

namespace Waring.Analytic

open scoped BigOperators

namespace Weil

theorem norm_le_one_of_bounded_weighted_powerSums {N : Nat}
    (z w : Fin N → Complex) (hz : Function.Injective z)
    (hw : ∀ i, w i ≠ 0) (C : Real) (n0 : Nat)
    (hbound : ∀ n, n0 ≤ n →
      norm (∑ i, w i * z i ^ n) ≤ C) :
    ∀ i, norm (z i) ≤ 1 := by
  let V : Matrix (Fin N) (Fin N) Complex := Matrix.vandermonde z
  have hdet : V.det ≠ 0 := by
    exact Matrix.det_vandermonde_ne_zero_iff.mpr hz
  intro i
  have hC : 0 ≤ C :=
    (norm_nonneg (∑ k, w k * z k ^ n0)).trans (hbound n0 le_rfl)
  let D : Real := ∑ j : Fin N, C * norm (V.adjugate j i)
  have hwindow (n : Nat) :
      (fun j : Fin N => ∑ k, w k * z k ^ (n + (j : Nat))) =
        Matrix.vecMul (fun k => w k * z k ^ n) V := by
    funext j
    simp only [Matrix.vecMul_apply_eq_sum, V, Matrix.vandermonde_apply]
    apply Finset.sum_congr rfl
    intro k _
    rw [pow_add]
    ring
  have hisolate (n : Nat) :
      Matrix.vecMul
          (fun j : Fin N => ∑ k, w k * z k ^ (n + (j : Nat)))
          V.adjugate i = V.det * (w i * z i ^ n) := by
    rw [hwindow, Matrix.vecMul_vecMul, Matrix.mul_adjugate]
    rw [Matrix.vecMul_smul, Matrix.vecMul_one]
    rfl
  have hlinear (n : Nat) :
      V.det * (w i * z i ^ n) =
        ∑ j : Fin N,
          (∑ k, w k * z k ^ (n + (j : Nat))) * V.adjugate j i := by
    rw [← hisolate n]
    rfl
  have hfinite (n : Nat) (hn : n0 ≤ n) :
      norm (V.det * (w i * z i ^ n)) ≤ D := by
    rw [hlinear]
    calc
      norm (∑ j : Fin N,
          (∑ k, w k * z k ^ (n + (j : Nat))) * V.adjugate j i) ≤
          ∑ j : Fin N,
            norm ((∑ k, w k * z k ^ (n + (j : Nat))) *
              V.adjugate j i) := norm_sum_le _ _
      _ = ∑ j : Fin N,
          norm (∑ k, w k * z k ^ (n + (j : Nat))) *
            norm (V.adjugate j i) := by
        apply Finset.sum_congr rfl
        intro j _
        rw [norm_mul]
      _ ≤ ∑ j : Fin N, C * norm (V.adjugate j i) := by
        apply Finset.sum_le_sum
        intro j _
        exact mul_le_mul_of_nonneg_right
          (hbound (n + (j : Nat)) (by omega)) (norm_nonneg _)
      _ = D := rfl
  by_contra hi
  have hiOne : 1 < norm (z i) := lt_of_not_ge hi
  have hdetNorm : 0 < norm V.det := norm_pos_iff.mpr hdet
  have hwNorm : 0 < norm (w i) := norm_pos_iff.mpr (hw i)
  have hscale : 0 < norm V.det * norm (w i) := mul_pos hdetNorm hwNorm
  have hD : 0 ≤ D := by
    dsimp [D]
    positivity
  obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt
    (D / (norm V.det * norm (w i))) hiOne
  let n := m + n0
  have hm_le_n : m ≤ n := by omega
  have hn0_le_n : n0 ≤ n := by omega
  have hpow : norm (z i) ^ m ≤ norm (z i) ^ n :=
    pow_le_pow_right₀ hiOne.le hm_le_n
  have hgrowth : D < (norm V.det * norm (w i)) * norm (z i) ^ n := by
    have hm' : D < norm (z i) ^ m * (norm V.det * norm (w i)) :=
      (div_lt_iff₀ hscale).mp hm
    nlinarith
  have hupper := hfinite n hn0_le_n
  rw [norm_mul, norm_mul, norm_pow] at hupper
  nlinarith

theorem norm_le_one_of_bounded_weighted_powerSums_fintype
    {ι : Type*} [Fintype ι] (z w : ι → Complex)
    (hz : Function.Injective z) (hw : ∀ i, w i ≠ 0)
    (C : Real) (n0 : Nat)
    (hbound : ∀ n, n0 ≤ n → norm (∑ i, w i * z i ^ n) ≤ C) :
    ∀ i, norm (z i) ≤ 1 := by
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  let z' : Fin (Fintype.card ι) → Complex := fun j => z (e.symm j)
  let w' : Fin (Fintype.card ι) → Complex := fun j => w (e.symm j)
  have hz' : Function.Injective z' := by
    intro a b hab
    exact e.symm.injective (hz hab)
  have hw' : ∀ j, w' j ≠ 0 := fun j => hw (e.symm j)
  have hbound' : ∀ n, n0 ≤ n →
      norm (∑ j, w' j * z' j ^ n) ≤ C := by
    intro n hn
    have hsum := e.sum_comp (fun j => w' j * z' j ^ n)
    rw [← hsum]
    simpa [z', w'] using hbound n hn
  have hcore := norm_le_one_of_bounded_weighted_powerSums
    z' w' hz' hw' C n0 hbound'
  intro i
  simpa [z'] using hcore (e i)

theorem norm_le_one_of_bounded_multisetPowerSums
    (s : Multiset Complex) (C : Real) (n0 : Nat)
    (hbound : ∀ n, n0 ≤ n →
      norm ((s.map fun z => z ^ n).sum) ≤ C) :
    ∀ z ∈ s, norm z ≤ 1 := by
  classical
  let t := s.toFinset
  let w : t → Complex := fun z => (s.count (z : Complex) : Complex)
  have hw : ∀ z : t, w z ≠ 0 := by
    intro z
    dsimp [w]
    exact Nat.cast_ne_zero.mpr
      (Multiset.count_pos.mpr (Multiset.mem_toFinset.mp z.property)).ne'
  have hbound' : ∀ n, n0 ≤ n →
      norm (∑ z : t, w z * (z : Complex) ^ n) ≤ C := by
    intro n hn
    have hgroup :
        (∑ z ∈ s.toFinset, (s.count z : Complex) * z ^ n) =
          (s.map fun z => z ^ n).sum := by
      simpa [nsmul_eq_mul] using
        (Finset.sum_multiset_map_count s (fun z : Complex => z ^ n)).symm
    rw [show (∑ z : t, w z * (z : Complex) ^ n) =
        ∑ z ∈ s.toFinset, (s.count z : Complex) * z ^ n by
      simpa [t, w] using
        (s.toFinset.sum_attach
          (fun z => (s.count z : Complex) * z ^ n))]
    rw [hgroup]
    exact hbound n hn
  have hcore := norm_le_one_of_bounded_weighted_powerSums_fintype
    (fun z : t => (z : Complex)) w Subtype.val_injective hw C n0 hbound'
  intro z hz
  exact hcore ⟨z, Multiset.mem_toFinset.mpr hz⟩

theorem norm_le_sqrt_of_bounded_even_multisetPowerSums
    (s : Multiset Complex) {q C : Real} (hq : 0 < q) (n0 : Nat)
    (hbound : ∀ m, n0 ≤ m →
      norm ((s.map fun z => z ^ (2 * m)).sum) ≤ C * q ^ m) :
    ∀ z ∈ s, norm z ≤ Real.sqrt q := by
  let u : Multiset Complex := s.map fun z => z ^ 2 / (q : Complex)
  have huBound : ∀ m, n0 ≤ m →
      norm ((u.map fun z => z ^ m).sum) ≤ C := by
    intro m hm
    have hpower :
        (u.map fun z => z ^ m).sum =
          (s.map fun z => z ^ (2 * m)).sum / (q : Complex) ^ m := by
      dsimp [u]
      rw [Multiset.map_map]
      rw [show ((fun z : Complex => z ^ m) ∘
          fun z => z ^ 2 / (q : Complex)) =
          fun z => z ^ (2 * m) / (q : Complex) ^ m by
        funext z
        rw [Function.comp_apply, div_pow, ← pow_mul]]
      exact Multiset.sum_map_div s (fun z => z ^ (2 * m)) ((q : Complex) ^ m)
    rw [hpower, norm_div, norm_pow, Complex.norm_real,
      Real.norm_of_nonneg hq.le]
    rw [div_le_iff₀ (pow_pos hq m)]
    simpa [mul_comm] using hbound m hm
  have hu := norm_le_one_of_bounded_multisetPowerSums u C n0 huBound
  intro z hz
  have hzMem : z ^ 2 / (q : Complex) ∈ u := by
    exact Multiset.mem_map.mpr ⟨z, hz, rfl⟩
  have hzNorm := hu _ hzMem
  rw [norm_div, norm_pow, Complex.norm_real,
    Real.norm_of_nonneg hq.le] at hzNorm
  exact Real.le_sqrt_of_sq_le ((div_le_one₀ hq).mp hzNorm)

end Weil

end Waring.Analytic

end

/-! ## ErdosProblems.Erdos387.RationalRootRadius -/

noncomputable section

namespace Erdos387

open Polynomial

open scoped BigOperators

namespace RationalWeil

def HasEvenExtensionSquareRootBound
    {p : ℕ} [NeZero p] [Fact p.Prime]
    (coeff : ZMod p → ZMod p) : Prop :=
  ∃ C : ℝ, ∀ (m : ℕ) (hm : 3 ≤ m),
    letI : NeZero (2 * m) := ⟨by omega⟩
    let E := FiniteField.Extension (ZMod p) p (2 * m)
    letI : Fintype E := Fintype.ofFinite E
    ‖∑ x : E, zeroExtendedTraceWeight coeff x‖ ≤
      C * (p : ℝ) ^ m

theorem norm_reverse_artinLPolynomial_root_le_sqrt_of_evenExtensionBound
    {p : ℕ} [NeZero p] [Fact p.Prime]
    (coeff : ZMod p → ZMod p)
    (hne : (InverseRational.poleSupport coeff).Nonempty)
    (hbound : HasEvenExtensionSquareRootBound coeff) :
    ∀ z ∈ (artinLPolynomial coeff).reverse.roots,
      ‖z‖ ≤ Real.sqrt (p : ℝ) := by
  obtain ⟨C, hC⟩ := hbound
  let roots := (artinLPolynomial coeff).reverse.roots
  have hpReal : (0 : ℝ) < p := by
    exact_mod_cast (Fact.out : p.Prime).pos
  have hpowers : ∀ m, 3 ≤ m →
      ‖(roots.map fun z ↦ z ^ (2 * m)).sum‖ ≤
        C * (p : ℝ) ^ m := by
    intro m hm
    let : NeZero (2 * m) := ⟨by omega⟩
    let E := FiniteField.Extension (ZMod p) p (2 * m)
    let : Fintype E := Fintype.ofFinite E
    have hexact := extensionTraceSum_eq_neg_artinRootPowerSum
      p (2 * m) coeff hne
    have hsum := hC m hm
    dsimp only at hsum
    calc
      ‖(roots.map fun z ↦ z ^ (2 * m)).sum‖ =
          ‖-((roots.map fun z ↦ z ^ (2 * m)).sum)‖ :=
        (norm_neg _).symm
      _ = ‖∑ x : E, zeroExtendedTraceWeight coeff x‖ := by
        exact congrArg norm hexact.symm
      _ ≤ C * (p : ℝ) ^ m := hsum
  have hradius :=
    Waring.Analytic.Weil.norm_le_sqrt_of_bounded_even_multisetPowerSums
      roots hpReal 3 hpowers
  exact hradius

theorem finiteExtensionTraceSum_eq_neg_artinRootPowerSum
    (p n : ℕ) [NeZero p] [Fact p.Prime] [NeZero n]
    (L : Type*) [Field L] [Finite L] [Algebra (ZMod p) L]
    [FiniteDimensional (ZMod p) L]
    (hfin : Module.finrank (ZMod p) L = n)
    (coeff : ZMod p → ZMod p)
    (hne : (InverseRational.poleSupport coeff).Nonempty) :
    letI : Fintype L := Fintype.ofFinite L
    (∑ x : L, zeroExtendedTraceWeight coeff x) =
      -((artinLPolynomial coeff).reverse.roots.map
        (fun a ↦ a ^ n)).sum := by
  classical
  let : Fintype L := Fintype.ofFinite L
  calc
    (∑ x : L, zeroExtendedTraceWeight coeff x) =
        ∑ x : L, polynomialWeight coeff (minpoly (ZMod p) x) ^
          (n / (minpoly (ZMod p) x).natDegree) := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [← extensionPointWeight_eq_zeroExtendedTraceWeight coeff x]
      simp only [extensionPointWeight, hfin]
    _ = ∑ P : MonicIrreducibleLE (ZMod p) n,
        if P.poly.natDegree ∣ n then
          (P.poly.natDegree : ℂ) *
            polynomialWeight coeff P.poly ^ (n / P.poly.natDegree)
        else 0 := by
      simpa only [nsmul_eq_mul] using
        (sum_finiteExtension_eq_irreducibleSum
          (ZMod p) n L hfin
          (fun P : (ZMod p)[X] ↦
            polynomialWeight coeff P ^ (n / P.natDegree)))
    _ = -((artinLPolynomial coeff).reverse.roots.map
          (fun a ↦ a ^ n)).sum :=
      irreducible_sum_eq_neg_artinRootPowerSum
        coeff hne le_rfl (NeZero.ne n)

theorem mappedSimplePolePhase_self
    {p : ℕ} [NeZero p] [Fact p.Prime]
    (coeff : ZMod p → ZMod p) (x : ZMod p) :
    mappedSimplePolePhase coeff x =
      InverseRational.simplePolePhase coeff x := by
  rw [InverseRational.simplePolePhase_eq_sum_poleSupport]
  simp [mappedSimplePolePhase]

theorem isMappedPole_self_iff
    {p : ℕ} [NeZero p] [Fact p.Prime]
    (coeff : ZMod p → ZMod p) (x : ZMod p) :
    IsMappedPole coeff x ↔ x ∈ InverseRational.poleSupport coeff := by
  constructor
  · rintro ⟨r, hr, hxr⟩
    have hxr' : x = r := by simpa using hxr
    simpa [hxr'] using hr
  · intro hx
    exact ⟨x, hx, by simp⟩

theorem zeroExtendedTraceWeight_self
    {p : ℕ} [NeZero p] [Fact p.Prime]
    (coeff : ZMod p → ZMod p) (x : ZMod p) :
    zeroExtendedTraceWeight coeff x =
      if x ∈ InverseRational.poleSupport coeff then 0
      else ZMod.stdAddChar (InverseRational.simplePolePhase coeff x) := by
  rw [zeroExtendedTraceWeight]
  by_cases hx : x ∈ InverseRational.poleSupport coeff
  · rw [if_pos ((isMappedPole_self_iff coeff x).2 hx), if_pos hx]
  · rw [if_neg (fun h ↦ hx ((isMappedPole_self_iff coeff x).1 h)),
      if_neg hx, Algebra.trace_self_apply, mappedSimplePolePhase_self]

theorem baseTraceSum_eq_neg_artinRootSum
    {p : ℕ} [NeZero p] [Fact p.Prime]
    (coeff : ZMod p → ZMod p)
    (hne : (InverseRational.poleSupport coeff).Nonempty) :
    (∑ x : ZMod p, zeroExtendedTraceWeight coeff x) =
      -(artinLPolynomial coeff).reverse.roots.sum := by
  have h := finiteExtensionTraceSum_eq_neg_artinRootPowerSum
    p 1 (ZMod p) (by simp) coeff hne
  let finiteFintype : Fintype (ZMod p) := Fintype.ofFinite (ZMod p)
  have h' :
      (@Finset.univ (ZMod p) finiteFintype).sum
          (fun x ↦ zeroExtendedTraceWeight coeff x) =
        -(artinLPolynomial coeff).reverse.roots.sum := by
    simpa only [pow_one, Multiset.map_id'] using h
  let standardUniv : Finset (ZMod p) :=
    @Finset.univ (ZMod p) (ZMod.fintype p)
  let finiteUniv : Finset (ZMod p) :=
    @Finset.univ (ZMod p) finiteFintype
  have huniv :
      standardUniv = finiteUniv := by
    dsimp only [standardUniv, finiteUniv]
    ext x
    simp only [Finset.mem_univ]
  change standardUniv.sum (fun x ↦ zeroExtendedTraceWeight coeff x) = _
  rw [huniv]
  exact h'

theorem norm_baseTraceSum_le_of_evenExtensionBound
    {p : ℕ} [NeZero p] [Fact p.Prime]
    (coeff : ZMod p → ZMod p)
    (hne : (InverseRational.poleSupport coeff).Nonempty)
    (hbound : HasEvenExtensionSquareRootBound coeff) :
    ‖∑ x : ZMod p, zeroExtendedTraceWeight coeff x‖ ≤
      ((2 * (InverseRational.poleSupport coeff).card - 1 : ℕ) : ℝ) *
        Real.sqrt (p : ℝ) := by
  let roots := (artinLPolynomial coeff).reverse.roots
  have hradius : ∀ z ∈ roots, ‖z‖ ≤ Real.sqrt (p : ℝ) :=
    norm_reverse_artinLPolynomial_root_le_sqrt_of_evenExtensionBound
      coeff hne hbound
  have hcardLt : roots.card <
      2 * (InverseRational.poleSupport coeff).card := by
    simpa only [roots] using
      card_roots_reverse_artinLPolynomial_lt coeff hne
  have hcard : roots.card ≤
      2 * (InverseRational.poleSupport coeff).card - 1 := by omega
  have hsumNorm :
      (roots.map fun z ↦ ‖z‖).sum ≤
        roots.card • Real.sqrt (p : ℝ) := by
    have hmapped := Multiset.sum_le_card_nsmul
      (roots.map fun z ↦ ‖z‖) (Real.sqrt (p : ℝ)) (by
        intro r hr
        obtain ⟨z, hz, rfl⟩ := Multiset.mem_map.mp hr
        exact hradius z hz)
    simpa only [Multiset.card_map] using hmapped
  have hidentity := baseTraceSum_eq_neg_artinRootSum coeff hne
  rw [hidentity, norm_neg]
  calc
    ‖roots.sum‖ ≤ (roots.map fun z ↦ ‖z‖).sum :=
      norm_multiset_sum_le roots
    _ ≤ roots.card • Real.sqrt (p : ℝ) := hsumNorm
    _ = (roots.card : ℝ) * Real.sqrt (p : ℝ) := by
      rw [nsmul_eq_mul]
    _ ≤ ((2 * (InverseRational.poleSupport coeff).card - 1 : ℕ) : ℝ) *
        Real.sqrt (p : ℝ) := by
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard)
        (Real.sqrt_nonneg _)

theorem norm_zeroExtendedSimplePolePhase_sum_le_of_evenExtensionBound
    {p : ℕ} [NeZero p] [Fact p.Prime]
    (coeff : ZMod p → ZMod p)
    (hne : (InverseRational.poleSupport coeff).Nonempty)
    (hbound : HasEvenExtensionSquareRootBound coeff) :
    ‖∑ x : ZMod p,
        if x ∈ InverseRational.poleSupport coeff then 0
        else ZMod.stdAddChar (InverseRational.simplePolePhase coeff x)‖ ≤
      ((2 * (InverseRational.poleSupport coeff).card - 1 : ℕ) : ℝ) *
        Real.sqrt (p : ℝ) := by
  have h := norm_baseTraceSum_le_of_evenExtensionBound coeff hne hbound
  simpa only [zeroExtendedTraceWeight_self] using h

end RationalWeil

end Erdos387

end

/-! ## ErdosProblems.Erdos387.RationalTracePolynomials -/

noncomputable section

namespace Erdos387

open Polynomial

open scoped BigOperators

namespace RationalStepanov

noncomputable def mappedSimplePoleDenominatorPolynomial
    {p : ℕ} [NeZero p] {E : Type*} [Field E]
    [Algebra (ZMod p) E] (coeff : ZMod p → ZMod p) : E[X] :=
  ∏ r ∈ InverseRational.poleSupport coeff,
    (X - C (algebraMap (ZMod p) E r))

noncomputable def mappedSimplePoleNumeratorPolynomial
    {p : ℕ} [NeZero p] {E : Type*} [Field E]
    [Algebra (ZMod p) E] (coeff : ZMod p → ZMod p) : E[X] :=
  ∑ r ∈ InverseRational.poleSupport coeff,
    C (algebraMap (ZMod p) E (coeff r)) *
      ∏ s ∈ (InverseRational.poleSupport coeff).erase r,
        (X - C (algebraMap (ZMod p) E s))

noncomputable def lowRationalDenominator
    {E : Type*} [CommRing E] (p m : ℕ) (B : E[X]) : E[X] :=
  ∏ t ∈ Finset.range m, expand E (p ^ t) B

noncomputable def lowRationalNumerator
    {E : Type*} [CommRing E] (p m : ℕ) (A B : E[X]) : E[X] :=
  ∑ t ∈ Finset.range m,
    expand E (p ^ t) A *
      ∏ u ∈ (Finset.range m).erase t, expand E (p ^ u) B

noncomputable def highRationalNumerator
    {E : Type*} [CommRing E] (p m : ℕ) (A B : E[X]) : E[X] :=
  expand E (p ^ m) (lowRationalNumerator p m A B)

noncomputable def highRationalDenominator
    {E : Type*} [CommRing E] (p m : ℕ) (B : E[X]) : E[X] :=
  expand E (p ^ m) (lowRationalDenominator p m B)

noncomputable def fullRationalNumerator
    {E : Type*} [CommRing E] (p m : ℕ) (A B : E[X]) : E[X] :=
  lowRationalNumerator p m A B * highRationalDenominator p m B +
    highRationalNumerator p m A B * lowRationalDenominator p m B

noncomputable def fullRationalDenominator
    {E : Type*} [CommRing E] (p m : ℕ) (B : E[X]) : E[X] :=
  lowRationalDenominator p m B * highRationalDenominator p m B

theorem eval_lowRationalDenominator
    {E : Type*} [CommRing E] (p m : ℕ) (B : E[X]) (x : E) :
    (lowRationalDenominator p m B).eval x =
      ∏ t ∈ Finset.range m, B.eval (x ^ (p ^ t)) := by
  rw [lowRationalDenominator, eval_prod]
  apply Finset.prod_congr rfl
  intro t ht
  exact expand_eval (p ^ t) B x

theorem eval_lowRationalNumerator
    {E : Type*} [CommRing E] (p m : ℕ) (A B : E[X]) (x : E) :
    (lowRationalNumerator p m A B).eval x =
      ∑ t ∈ Finset.range m,
        A.eval (x ^ (p ^ t)) *
          ∏ u ∈ (Finset.range m).erase t,
            B.eval (x ^ (p ^ u)) := by
  rw [lowRationalNumerator, eval_finsetSum]
  apply Finset.sum_congr rfl
  intro t ht
  rw [eval_mul, expand_eval, eval_prod]
  apply congrArg (A.eval (x ^ (p ^ t)) * ·)
  apply Finset.prod_congr rfl
  intro u hu
  exact expand_eval (p ^ u) B x

theorem sum_mul_prod_erase_mul_inv_prod
    {E : Type*} [Field E] {I : Type*} [DecidableEq I]
    (s : Finset I) (a b : I → E)
    (hb : ∀ i ∈ s, b i ≠ 0) :
    (∑ i ∈ s, a i * ∏ j ∈ s.erase i, b j) *
        (∏ j ∈ s, b j)⁻¹ =
      ∑ i ∈ s, a i * (b i)⁻¹ := by
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  have hfactor :
      b i * (∏ j ∈ s.erase i, b j) = ∏ j ∈ s, b j := by
    exact Finset.mul_prod_erase s b hi
  have hrest : (∏ j ∈ s.erase i, b j) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro j hj
    exact hb j (Finset.mem_of_mem_erase hj)
  rw [← hfactor]
  field_simp [hb i hi, hrest]

theorem mappedSimplePolePhase_eq_numerator_mul_inv_denominator
    {p : ℕ} [NeZero p] [Fact p.Prime]
    {E : Type*} [Field E] [Algebra (ZMod p) E]
    (coeff : ZMod p → ZMod p) {x : E}
    (hx : ∀ r ∈ InverseRational.poleSupport coeff,
      x ≠ algebraMap (ZMod p) E r) :
    RationalWeil.mappedSimplePolePhase coeff x =
      (mappedSimplePoleNumeratorPolynomial coeff).eval x *
        ((mappedSimplePoleDenominatorPolynomial coeff).eval x)⁻¹ := by
  rw [RationalWeil.mappedSimplePolePhase,
    mappedSimplePoleNumeratorPolynomial, eval_finsetSum,
    mappedSimplePoleDenominatorPolynomial, eval_prod]
  simp only [eval_mul, eval_C, eval_prod, eval_sub, eval_X]
  exact (sum_mul_prod_erase_mul_inv_prod
    (InverseRational.poleSupport coeff)
    (fun r ↦ algebraMap (ZMod p) E (coeff r))
    (fun r ↦ x - algebraMap (ZMod p) E r) (by
      intro r hr
      exact sub_ne_zero.mpr (hx r hr))).symm

theorem eval_mappedSimplePoleDenominatorPolynomial_ne_zero
    {p : ℕ} [NeZero p] [Fact p.Prime]
    {E : Type*} [Field E] [Algebra (ZMod p) E]
    (coeff : ZMod p → ZMod p) {x : E}
    (hx : ∀ r ∈ InverseRational.poleSupport coeff,
      x ≠ algebraMap (ZMod p) E r) :
    (mappedSimplePoleDenominatorPolynomial coeff).eval x ≠ 0 := by
  rw [mappedSimplePoleDenominatorPolynomial, eval_prod,
    Finset.prod_ne_zero_iff]
  intro r hr
  simpa only [eval_sub, eval_X, eval_C, sub_ne_zero] using hx r hr

theorem mappedSimplePolePhase_pow_char_pow
    {p : ℕ} [NeZero p] [Fact p.Prime]
    {E : Type*} [Field E] [CharP E p] [Algebra (ZMod p) E]
    (coeff : ZMod p → ZMod p) (x : E) (t : ℕ) :
    RationalWeil.mappedSimplePolePhase coeff x ^ (p ^ t) =
      RationalWeil.mappedSimplePolePhase coeff (x ^ (p ^ t)) := by
  rw [RationalWeil.mappedSimplePolePhase,
    RationalWeil.mappedSimplePolePhase]
  calc
    (∑ r ∈ InverseRational.poleSupport coeff,
        algebraMap (ZMod p) E (coeff r) *
          (x - algebraMap (ZMod p) E r)⁻¹) ^ (p ^ t) =
        ∑ r ∈ InverseRational.poleSupport coeff,
          (algebraMap (ZMod p) E (coeff r) *
            (x - algebraMap (ZMod p) E r)⁻¹) ^ (p ^ t) := by
      simpa using sum_pow_char_pow p t
        (InverseRational.poleSupport coeff)
        (fun r ↦ algebraMap (ZMod p) E (coeff r) *
          (x - algebraMap (ZMod p) E r)⁻¹)
    _ = ∑ r ∈ InverseRational.poleSupport coeff,
        algebraMap (ZMod p) E (coeff r) *
          (x ^ (p ^ t) - algebraMap (ZMod p) E r)⁻¹ := by
      apply Finset.sum_congr rfl
      intro r hr
      rw [mul_pow, inv_pow, sub_pow_expChar_pow,
        ← map_pow, ← map_pow, ZMod.pow_card_pow, ZMod.pow_card_pow]

theorem frobenius_pow_ne_mappedPole
    {p : ℕ} [NeZero p] [Fact p.Prime]
    {E : Type*} [Field E] [CharP E p] [PerfectRing E p]
    [Algebra (ZMod p) E]
    {x : E} (coeff : ZMod p → ZMod p)
    (hx : ∀ r ∈ InverseRational.poleSupport coeff,
      x ≠ algebraMap (ZMod p) E r) (t : ℕ) :
    ∀ r ∈ InverseRational.poleSupport coeff,
      x ^ (p ^ t) ≠ algebraMap (ZMod p) E r := by
  intro r hr hpow
  apply hx r hr
  apply (iterateFrobeniusEquiv E p t).injective
  rw [iterateFrobeniusEquiv_def, iterateFrobeniusEquiv_def,
    hpow, ← map_pow, ZMod.pow_card_pow]

theorem eval_lowRationalNumerator_mul_inv_denominator
    {E : Type*} [Field E] (p m : ℕ) (A B : E[X]) (x : E)
    (hB : ∀ t < m, B.eval (x ^ (p ^ t)) ≠ 0) :
    (lowRationalNumerator p m A B).eval x *
        ((lowRationalDenominator p m B).eval x)⁻¹ =
      ∑ t ∈ Finset.range m,
        A.eval (x ^ (p ^ t)) * (B.eval (x ^ (p ^ t)))⁻¹ := by
  rw [eval_lowRationalNumerator, eval_lowRationalDenominator]
  exact sum_mul_prod_erase_mul_inv_prod (Finset.range m)
    (fun t ↦ A.eval (x ^ (p ^ t)))
    (fun t ↦ B.eval (x ^ (p ^ t))) (by
      intro t ht
      exact hB t (Finset.mem_range.mp ht))

theorem eval_highRationalNumerator
    {E : Type*} [CommRing E] (p m : ℕ) (A B : E[X]) (x : E) :
    (highRationalNumerator p m A B).eval x =
      (lowRationalNumerator p m A B).eval (x ^ (p ^ m)) := by
  exact expand_eval (p ^ m) (lowRationalNumerator p m A B) x

theorem eval_highRationalDenominator
    {E : Type*} [CommRing E] (p m : ℕ) (B : E[X]) (x : E) :
    (highRationalDenominator p m B).eval x =
      (lowRationalDenominator p m B).eval (x ^ (p ^ m)) := by
  exact expand_eval (p ^ m) (lowRationalDenominator p m B) x

theorem eval_fullRationalNumerator
    {E : Type*} [CommRing E] (p m : ℕ) (A B : E[X]) (x : E) :
    (fullRationalNumerator p m A B).eval x =
      (lowRationalNumerator p m A B).eval x *
          (lowRationalDenominator p m B).eval (x ^ (p ^ m)) +
        (lowRationalNumerator p m A B).eval (x ^ (p ^ m)) *
          (lowRationalDenominator p m B).eval x := by
  rw [fullRationalNumerator, eval_add, eval_mul, eval_mul,
    eval_highRationalNumerator, eval_highRationalDenominator]

theorem eval_fullRationalDenominator
    {E : Type*} [CommRing E] (p m : ℕ) (B : E[X]) (x : E) :
    (fullRationalDenominator p m B).eval x =
      (lowRationalDenominator p m B).eval x *
        (lowRationalDenominator p m B).eval (x ^ (p ^ m)) := by
  rw [fullRationalDenominator, eval_mul, eval_highRationalDenominator]

theorem eval_fullRationalNumerator_mul_inv_denominator
    {E : Type*} [Field E] (p m : ℕ) (A B : E[X]) (x : E)
    (hB : ∀ t < 2 * m, B.eval (x ^ (p ^ t)) ≠ 0) :
    (fullRationalNumerator p m A B).eval x *
        ((fullRationalDenominator p m B).eval x)⁻¹ =
      ∑ t ∈ Finset.range (2 * m),
        A.eval (x ^ (p ^ t)) * (B.eval (x ^ (p ^ t)))⁻¹ := by
  have hlowOrbit : ∀ t < m, B.eval (x ^ (p ^ t)) ≠ 0 := by
    intro t ht
    exact hB t (by omega)
  have hhighOrbit : ∀ t < m,
      B.eval ((x ^ (p ^ m)) ^ (p ^ t)) ≠ 0 := by
    intro t ht
    rw [← pow_mul, ← pow_add]
    exact hB (m + t) (by omega)
  have hlowDen : (lowRationalDenominator p m B).eval x ≠ 0 := by
    rw [eval_lowRationalDenominator]
    apply Finset.prod_ne_zero_iff.mpr
    intro t ht
    exact hlowOrbit t (Finset.mem_range.mp ht)
  have hhighDen :
      (lowRationalDenominator p m B).eval (x ^ (p ^ m)) ≠ 0 := by
    rw [eval_lowRationalDenominator]
    apply Finset.prod_ne_zero_iff.mpr
    intro t ht
    exact hhighOrbit t (Finset.mem_range.mp ht)
  rw [eval_fullRationalNumerator, eval_fullRationalDenominator]
  have hadd :
      ((lowRationalNumerator p m A B).eval x *
            (lowRationalDenominator p m B).eval (x ^ (p ^ m)) +
          (lowRationalNumerator p m A B).eval (x ^ (p ^ m)) *
            (lowRationalDenominator p m B).eval x) *
          ((lowRationalDenominator p m B).eval x *
            (lowRationalDenominator p m B).eval (x ^ (p ^ m)))⁻¹ =
        (lowRationalNumerator p m A B).eval x *
            ((lowRationalDenominator p m B).eval x)⁻¹ +
          (lowRationalNumerator p m A B).eval (x ^ (p ^ m)) *
            ((lowRationalDenominator p m B).eval (x ^ (p ^ m)))⁻¹ := by
    field_simp [hlowDen, hhighDen]
  rw [hadd,
    eval_lowRationalNumerator_mul_inv_denominator p m A B x hlowOrbit,
    eval_lowRationalNumerator_mul_inv_denominator
      p m A B (x ^ (p ^ m)) hhighOrbit]
  rw [show 2 * m = m + m by omega, Finset.sum_range_add]
  congr 1
  apply Finset.sum_congr rfl
  intro t ht
  rw [← pow_mul, ← pow_add]

theorem eval_fullRationalTrace_eq_algebraMap_trace
    {p m : ℕ} [NeZero p] [Fact p.Prime]
    {E : Type*} [Field E] [Finite E] [Algebra (ZMod p) E]
    [CharP E p] [FiniteDimensional (ZMod p) E]
    (hfin : Module.finrank (ZMod p) E = 2 * m)
    (coeff : ZMod p → ZMod p) (x : E)
    (hx : ∀ r ∈ InverseRational.poleSupport coeff,
      x ≠ algebraMap (ZMod p) E r) :
    (fullRationalNumerator p m
        (mappedSimplePoleNumeratorPolynomial coeff)
        (mappedSimplePoleDenominatorPolynomial coeff)).eval x *
      ((fullRationalDenominator p m
        (mappedSimplePoleDenominatorPolynomial coeff)).eval x)⁻¹ =
      algebraMap (ZMod p) E
        (Algebra.trace (ZMod p) E
          (RationalWeil.mappedSimplePolePhase coeff x)) := by
  let A : E[X] := mappedSimplePoleNumeratorPolynomial coeff
  let B : E[X] := mappedSimplePoleDenominatorPolynomial coeff
  have hOrbit (t : ℕ) :
      ∀ r ∈ InverseRational.poleSupport coeff,
        x ^ (p ^ t) ≠ algebraMap (ZMod p) E r :=
    frobenius_pow_ne_mappedPole coeff hx t
  have hB : ∀ t < 2 * m, B.eval (x ^ (p ^ t)) ≠ 0 := by
    intro t ht
    exact eval_mappedSimplePoleDenominatorPolynomial_ne_zero
      coeff (hOrbit t)
  calc
    (fullRationalNumerator p m A B).eval x *
        ((fullRationalDenominator p m B).eval x)⁻¹ =
        ∑ t ∈ Finset.range (2 * m),
          A.eval (x ^ (p ^ t)) * (B.eval (x ^ (p ^ t)))⁻¹ :=
      eval_fullRationalNumerator_mul_inv_denominator p m A B x hB
    _ = ∑ t ∈ Finset.range (2 * m),
        RationalWeil.mappedSimplePolePhase coeff (x ^ (p ^ t)) := by
      apply Finset.sum_congr rfl
      intro t ht
      exact (mappedSimplePolePhase_eq_numerator_mul_inv_denominator
        coeff (hOrbit t)).symm
    _ = ∑ t ∈ Finset.range (2 * m),
        RationalWeil.mappedSimplePolePhase coeff x ^ (p ^ t) := by
      apply Finset.sum_congr rfl
      intro t ht
      exact (mappedSimplePolePhase_pow_char_pow coeff x t).symm
    _ = algebraMap (ZMod p) E
        (Algebra.trace (ZMod p) E
          (RationalWeil.mappedSimplePolePhase coeff x)) := by
      rw [FiniteField.algebraMap_trace_eq_sum_pow, hfin, Nat.card_zmod]

theorem natDegree_mappedSimplePoleDenominatorPolynomial
    {p : ℕ} [NeZero p] [Fact p.Prime]
    {E : Type*} [Field E] [Algebra (ZMod p) E]
    (coeff : ZMod p → ZMod p) :
    (mappedSimplePoleDenominatorPolynomial (E := E) coeff).natDegree =
      (InverseRational.poleSupport coeff).card := by
  exact natDegree_finsetProd_X_sub_C_eq_card
    (InverseRational.poleSupport coeff)
    (fun r : ZMod p ↦ algebraMap (ZMod p) E r)

theorem natDegree_mappedSimplePoleNumeratorPolynomial_le
    {p : ℕ} [NeZero p] [Fact p.Prime]
    {E : Type*} [Field E] [Algebra (ZMod p) E]
    (coeff : ZMod p → ZMod p) :
    (mappedSimplePoleNumeratorPolynomial (E := E) coeff).natDegree ≤
      (InverseRational.poleSupport coeff).card - 1 := by
  rw [mappedSimplePoleNumeratorPolynomial]
  apply natDegree_sum_le_of_forall_le
  intro r hr
  calc
    (C (algebraMap (ZMod p) E (coeff r)) *
        ∏ s ∈ (InverseRational.poleSupport coeff).erase r,
          (X - C (algebraMap (ZMod p) E s))).natDegree ≤
        (∏ s ∈ (InverseRational.poleSupport coeff).erase r,
          (X - C (algebraMap (ZMod p) E s))).natDegree :=
      natDegree_C_mul_le _ _
    _ = ((InverseRational.poleSupport coeff).erase r).card :=
      natDegree_finsetProd_X_sub_C_eq_card
        ((InverseRational.poleSupport coeff).erase r)
        (fun s : ZMod p ↦ algebraMap (ZMod p) E s)
    _ = (InverseRational.poleSupport coeff).card - 1 :=
      Finset.card_erase_of_mem hr

theorem natDegree_lowRationalDenominator_le
    {E : Type*} [CommRing E] {p m d : ℕ} {B : E[X]}
    (hB : B.natDegree ≤ d) :
    (lowRationalDenominator p m B).natDegree ≤
      d * ∑ t ∈ Finset.range m, p ^ t := by
  calc
    (lowRationalDenominator p m B).natDegree ≤
        ∑ t ∈ Finset.range m,
          (expand E (p ^ t) B).natDegree := by
      exact natDegree_prod_le _ _
    _ ≤ ∑ t ∈ Finset.range m, d * p ^ t := by
      apply Finset.sum_le_sum
      intro t ht
      rw [natDegree_expand]
      exact Nat.mul_le_mul_right _ hB
    _ = d * ∑ t ∈ Finset.range m, p ^ t := by
      rw [Finset.mul_sum]

theorem natDegree_lowRationalNumerator_le
    {E : Type*} [CommRing E] {p m d : ℕ} {A B : E[X]}
    (hA : A.natDegree ≤ d) (hB : B.natDegree ≤ d) :
    (lowRationalNumerator p m A B).natDegree ≤
      d * ∑ t ∈ Finset.range m, p ^ t := by
  rw [lowRationalNumerator]
  apply natDegree_sum_le_of_forall_le
  intro t ht
  have htMem : t ∈ Finset.range m := ht
  have hprod :
      (∏ u ∈ (Finset.range m).erase t,
        expand E (p ^ u) B).natDegree ≤
        ∑ u ∈ (Finset.range m).erase t, d * p ^ u := by
    calc
      (∏ u ∈ (Finset.range m).erase t,
          expand E (p ^ u) B).natDegree ≤
          ∑ u ∈ (Finset.range m).erase t,
            (expand E (p ^ u) B).natDegree :=
        natDegree_prod_le _ _
      _ ≤ ∑ u ∈ (Finset.range m).erase t, d * p ^ u := by
        apply Finset.sum_le_sum
        intro u hu
        rw [natDegree_expand]
        exact Nat.mul_le_mul_right _ hB
  have hterm :
      (expand E (p ^ t) A *
        ∏ u ∈ (Finset.range m).erase t,
          expand E (p ^ u) B).natDegree ≤
        d * p ^ t +
          ∑ u ∈ (Finset.range m).erase t, d * p ^ u := by
    exact natDegree_mul_le.trans
      (Nat.add_le_add (by
        rw [natDegree_expand]
        exact Nat.mul_le_mul_right _ hA) hprod)
  calc
    (expand E (p ^ t) A *
        ∏ u ∈ (Finset.range m).erase t,
          expand E (p ^ u) B).natDegree ≤
        d * p ^ t +
          ∑ u ∈ (Finset.range m).erase t, d * p ^ u := hterm
    _ = ∑ u ∈ Finset.range m, d * p ^ u := by
      exact Finset.add_sum_erase (Finset.range m)
        (fun u : ℕ ↦ d * p ^ u) htMem
    _ = d * ∑ u ∈ Finset.range m, p ^ u := by
      rw [Finset.mul_sum]

end RationalStepanov

end Erdos387

end

/-! ## ErdosProblems.Erdos387.RationalPoleOrders -/

noncomputable section

namespace Erdos387

open Polynomial

open scoped BigOperators

namespace RationalStepanov

def frobeniusOrderSum (p m : ℕ) : ℕ :=
  ∑ t ∈ Finset.range m, p ^ t

theorem frobeniusOrderSum_succ (p m : ℕ) :
    frobeniusOrderSum p (m + 1) =
      frobeniusOrderSum p m + p ^ m := by
  simp [frobeniusOrderSum, Finset.sum_range_succ]

theorem mappedSimplePoleDenominatorPolynomial_eq_map
    {p : ℕ} [NeZero p] [Fact p.Prime]
    {E : Type*} [Field E] [Algebra (ZMod p) E]
    (coeff : ZMod p → ZMod p) :
    mappedSimplePoleDenominatorPolynomial (E := E) coeff =
      (InverseRational.simplePoleDenominatorPolynomial coeff).map
        (algebraMap (ZMod p) E) := by
  rw [mappedSimplePoleDenominatorPolynomial,
    InverseRational.simplePoleDenominatorPolynomial]
  change (∏ r ∈ InverseRational.poleSupport coeff,
      (X - C (algebraMap (ZMod p) E r))) =
    (mapRingHom (algebraMap (ZMod p) E))
      (∏ r ∈ InverseRational.poleSupport coeff, (X - C r))
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro r hr
  simp

theorem mappedSimplePoleNumeratorPolynomial_eq_map
    {p : ℕ} [NeZero p] [Fact p.Prime]
    {E : Type*} [Field E] [Algebra (ZMod p) E]
    (coeff : ZMod p → ZMod p) :
    mappedSimplePoleNumeratorPolynomial (E := E) coeff =
      (InverseRational.simplePoleNumeratorPolynomial coeff).map
        (algebraMap (ZMod p) E) := by
  rw [mappedSimplePoleNumeratorPolynomial,
    InverseRational.simplePoleNumeratorPolynomial]
  change (∑ r ∈ InverseRational.poleSupport coeff,
      C (algebraMap (ZMod p) E (coeff r)) *
        ∏ s ∈ (InverseRational.poleSupport coeff).erase r,
          (X - C (algebraMap (ZMod p) E s))) =
    (mapRingHom (algebraMap (ZMod p) E))
      (∑ r ∈ InverseRational.poleSupport coeff,
        C (coeff r) *
          ∏ s ∈ (InverseRational.poleSupport coeff).erase r, (X - C s))
  simp only [coe_mapRingHom, map_sum, map_mul, map_C, map_prod, map_sub, map_X]

theorem iterateFrobenius_algebraMap_zmod
    {p : ℕ} [NeZero p] [Fact p.Prime]
    {E : Type*} [Field E] [CharP E p] [Algebra (ZMod p) E]
    (t : ℕ) (x : ZMod p) :
    iterateFrobenius E p t (algebraMap (ZMod p) E x) =
      algebraMap (ZMod p) E x := by
  rw [iterateFrobenius_def, ← map_pow, ZMod.pow_card_pow]

theorem expand_map_zmod_eq_pow
    {p : ℕ} [NeZero p] [Fact p.Prime]
    {E : Type*} [Field E] [CharP E p] [Algebra (ZMod p) E]
    (t : ℕ) (f : (ZMod p)[X]) :
    expand E (p ^ t) (f.map (algebraMap (ZMod p) E)) =
      (f.map (algebraMap (ZMod p) E)) ^ (p ^ t) := by
  have hzmod : expand (ZMod p) (p ^ t) f = f ^ (p ^ t) := by
    induction t generalizing f with
    | zero => simp
    | succ t ih =>
        rw [pow_succ, expand_mul, ih, ZMod.expand_card]
        simp only [← pow_mul, Nat.mul_comm]
  rw [← map_expand, hzmod, Polynomial.map_pow]

theorem rootMultiplicity_add_eq_left_of_lt
    {K : Type*} [Field K] {P Q : K[X]} {r : K}
    (hP : P ≠ 0) (hQ : Q ≠ 0)
    (hlt : P.rootMultiplicity r < Q.rootMultiplicity r) :
    (P + Q).rootMultiplicity r = P.rootMultiplicity r := by
  let TP := taylor r P
  let TQ := taylor r Q
  have hTP : TP ≠ 0 := by
    intro h
    apply hP
    apply taylor_injective r
    simpa only [TP, map_zero] using h
  have hTQ : TQ ≠ 0 := by
    intro h
    apply hQ
    apply taylor_injective r
    simpa only [TQ, map_zero] using h
  have horders :
      TP.natTrailingDegree < TQ.natTrailingDegree := by
    simpa only [TP, TQ, taylor_apply, ← rootMultiplicity_eq_natTrailingDegree]
      using hlt
  have hcoeffP : TP.coeff TP.natTrailingDegree ≠ 0 :=
    coeff_natTrailingDegree_ne_zero.mpr hTP
  have hcoeffQ : TQ.coeff TP.natTrailingDegree = 0 :=
    coeff_eq_zero_of_lt_natTrailingDegree horders
  have hcoeffAdd :
      (TP + TQ).coeff TP.natTrailingDegree ≠ 0 := by
    simpa [coeff_add, hcoeffQ] using hcoeffP
  have hsum : TP + TQ ≠ 0 := by
    intro h
    rw [h, coeff_zero] at hcoeffAdd
    exact hcoeffAdd rfl
  have hlower : ∀ j < TP.natTrailingDegree,
      (TP + TQ).coeff j = 0 := by
    intro j hj
    rw [coeff_add, coeff_eq_zero_of_lt_natTrailingDegree hj,
      coeff_eq_zero_of_lt_natTrailingDegree (hj.trans horders), zero_add]
  have heq : (TP + TQ).natTrailingDegree = TP.natTrailingDegree := by
    apply le_antisymm
    · exact natTrailingDegree_le_of_ne_zero hcoeffAdd
    · exact le_natTrailingDegree hsum hlower
  rw [rootMultiplicity_eq_natTrailingDegree,
    rootMultiplicity_eq_natTrailingDegree, add_comp]
  simpa only [TP, TQ, taylor_apply] using heq

theorem rootMultiplicity_add_eq_right_of_lt
    {K : Type*} [Field K] {P Q : K[X]} {r : K}
    (hP : P ≠ 0) (hQ : Q ≠ 0)
    (hlt : Q.rootMultiplicity r < P.rootMultiplicity r) :
    (P + Q).rootMultiplicity r = Q.rootMultiplicity r := by
  rw [add_comm]
  exact rootMultiplicity_add_eq_left_of_lt hQ hP hlt

theorem lowRationalDenominator_succ
    {E : Type*} [CommRing E] (p m : ℕ) (B : E[X]) :
    lowRationalDenominator p (m + 1) B =
      lowRationalDenominator p m B * expand E (p ^ m) B := by
  simp [lowRationalDenominator, Finset.prod_range_succ]

theorem lowRationalNumerator_succ
    {E : Type*} [CommRing E] (p m : ℕ) (A B : E[X]) :
    lowRationalNumerator p (m + 1) A B =
      lowRationalNumerator p m A B * expand E (p ^ m) B +
        expand E (p ^ m) A * lowRationalDenominator p m B := by
  rw [lowRationalNumerator, Finset.sum_range_succ,
    lowRationalNumerator, lowRationalDenominator]
  congr 1
  · rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro t ht
    have htlt : t < m := Finset.mem_range.mp ht
    rw [mul_assoc]
    apply congrArg ((expand E (p ^ t) A) * ·)
    rw [Finset.range_add_one, Finset.erase_insert_of_ne (by omega),
      Finset.prod_insert]
    · ring
    · intro hm
      exact Finset.notMem_range_self (Finset.mem_of_mem_erase hm)
  · rw [Finset.range_add_one,
      Finset.erase_insert (s := Finset.range m) (a := m)
        Finset.notMem_range_self]

theorem eval_mappedSimplePoleNumeratorPolynomial_ne_zero
    {p : ℕ} [NeZero p] [Fact p.Prime]
    {E : Type*} [Field E] [Algebra (ZMod p) E]
    (coeff : ZMod p → ZMod p) {r : ZMod p}
    (hr : r ∈ InverseRational.poleSupport coeff) :
    (mappedSimplePoleNumeratorPolynomial (E := E) coeff).eval
        (algebraMap (ZMod p) E r) ≠ 0 := by
  rw [mappedSimplePoleNumeratorPolynomial_eq_map, eval_map_apply]
  intro h
  apply InverseRational.eval_simplePoleNumeratorPolynomial_ne_zero coeff hr
  exact (algebraMap (ZMod p) E).injective (by simpa using h)

theorem rootMultiplicity_mappedSimplePoleNumeratorPolynomial
    {p : ℕ} [NeZero p] [Fact p.Prime]
    {E : Type*} [Field E] [Algebra (ZMod p) E]
    (coeff : ZMod p → ZMod p) {r : ZMod p}
    (hr : r ∈ InverseRational.poleSupport coeff) :
    (mappedSimplePoleNumeratorPolynomial (E := E) coeff).rootMultiplicity
        (algebraMap (ZMod p) E r) = 0 := by
  apply rootMultiplicity_eq_zero
  simpa only [IsRoot] using
    eval_mappedSimplePoleNumeratorPolynomial_ne_zero (E := E) coeff hr

theorem rootMultiplicity_mappedSimplePoleDenominatorPolynomial
    {p : ℕ} [NeZero p] [Fact p.Prime]
    {E : Type*} [Field E] [Algebra (ZMod p) E]
    (coeff : ZMod p → ZMod p) {r : ZMod p}
    (hr : r ∈ InverseRational.poleSupport coeff) :
    (mappedSimplePoleDenominatorPolynomial (E := E) coeff).rootMultiplicity
        (algebraMap (ZMod p) E r) = 1 := by
  rw [mappedSimplePoleDenominatorPolynomial_eq_map,
    ← eq_rootMultiplicity_map (algebraMap (ZMod p) E).injective r,
    InverseRational.simplePoleDenominatorPolynomial_eq_mul_erase coeff hr]
  have hcomp :
      (∏ s ∈ (InverseRational.poleSupport coeff).erase r,
        (X - C s : (ZMod p)[X])) ≠ 0 := by
    intro h
    have heval := congrArg (eval r) h
    exact (InverseRational.eval_simplePoleComplement_ne_zero coeff hr)
      (by simpa using heval)
  rw [rootMultiplicity_mul (mul_ne_zero (X_sub_C_ne_zero r) hcomp),
    rootMultiplicity_X_sub_C_self,
    rootMultiplicity_eq_zero (by
      simpa only [IsRoot] using
        InverseRational.eval_simplePoleComplement_ne_zero coeff hr)]

theorem lowRationalPoleOrders
    {p : ℕ} [NeZero p] [Fact p.Prime]
    {E : Type*} [Field E] [CharP E p] [Algebra (ZMod p) E]
    (coeff : ZMod p → ZMod p) {r : ZMod p}
    (hr : r ∈ InverseRational.poleSupport coeff)
    (m : ℕ) (hm : 0 < m) :
    let A := mappedSimplePoleNumeratorPolynomial (E := E) coeff
    let B := mappedSimplePoleDenominatorPolynomial (E := E) coeff
    lowRationalDenominator p m B ≠ 0 ∧
      (lowRationalDenominator p m B).rootMultiplicity
        (algebraMap (ZMod p) E r) = frobeniusOrderSum p m ∧
      lowRationalNumerator p m A B ≠ 0 ∧
      (lowRationalNumerator p m A B).rootMultiplicity
        (algebraMap (ZMod p) E r) = frobeniusOrderSum p (m - 1) := by
  dsimp only
  let A := mappedSimplePoleNumeratorPolynomial (E := E) coeff
  let B := mappedSimplePoleDenominatorPolynomial (E := E) coeff
  have hA : A ≠ 0 := by
    intro h
    have he := congrArg (eval (algebraMap (ZMod p) E r)) h
    exact (eval_mappedSimplePoleNumeratorPolynomial_ne_zero
      (E := E) coeff hr) (by simpa [A] using he)
  have hB : B ≠ 0 := by
    intro h
    have hmultiplicity :=
      rootMultiplicity_mappedSimplePoleDenominatorPolynomial
        (E := E) coeff hr
    change B.rootMultiplicity (algebraMap (ZMod p) E r) = 1 at hmultiplicity
    rw [h, rootMultiplicity_zero] at hmultiplicity
    omega
  have hAr : A.rootMultiplicity (algebraMap (ZMod p) E r) = 0 :=
    rootMultiplicity_mappedSimplePoleNumeratorPolynomial (E := E) coeff hr
  have hBr : B.rootMultiplicity (algebraMap (ZMod p) E r) = 1 :=
    rootMultiplicity_mappedSimplePoleDenominatorPolynomial (E := E) coeff hr
  induction m using Nat.twoStepInduction with
  | zero => omega
  | one =>
      simp [lowRationalDenominator, lowRationalNumerator,
        frobeniusOrderSum, A, B, hA, hB, hAr, hBr]
  | more m ih0 ih1 =>
      have hm1 : 0 < m + 1 := by omega
      obtain ⟨hLD, hLDord, hLN, hLNord⟩ := ih1 hm1
      have hEA : expand E (p ^ (m + 1)) A ≠ 0 := by
        change expand E (p ^ (m + 1))
          (mappedSimplePoleNumeratorPolynomial (E := E) coeff) ≠ 0
        rw [mappedSimplePoleNumeratorPolynomial_eq_map,
          expand_map_zmod_eq_pow]
        exact pow_ne_zero _ (by
          simpa [A, mappedSimplePoleNumeratorPolynomial_eq_map] using hA)
      have hEB : expand E (p ^ (m + 1)) B ≠ 0 := by
        change expand E (p ^ (m + 1))
          (mappedSimplePoleDenominatorPolynomial (E := E) coeff) ≠ 0
        rw [mappedSimplePoleDenominatorPolynomial_eq_map,
          expand_map_zmod_eq_pow]
        exact pow_ne_zero _ (by
          simpa [B, mappedSimplePoleDenominatorPolynomial_eq_map] using hB)
      have hEAord :
          (expand E (p ^ (m + 1)) A).rootMultiplicity
              (algebraMap (ZMod p) E r) = 0 := by
        rw [rootMultiplicity_expand_pow, ← iterateFrobenius_def,
          iterateFrobenius_algebraMap_zmod, hAr, mul_zero]
      have hEBord :
          (expand E (p ^ (m + 1)) B).rootMultiplicity
              (algebraMap (ZMod p) E r) = p ^ (m + 1) := by
        rw [rootMultiplicity_expand_pow, ← iterateFrobenius_def,
          iterateFrobenius_algebraMap_zmod, hBr, mul_one]
      let P := lowRationalNumerator p (m + 1) A B *
        expand E (p ^ (m + 1)) B
      let Q := expand E (p ^ (m + 1)) A *
        lowRationalDenominator p (m + 1) B
      have hP : P ≠ 0 := mul_ne_zero hLN hEB
      have hQ : Q ≠ 0 := mul_ne_zero hEA hLD
      have hPord : P.rootMultiplicity (algebraMap (ZMod p) E r) =
          frobeniusOrderSum p m + p ^ (m + 1) := by
        dsimp only [P]
        rw [rootMultiplicity_mul hP, hLNord, hEBord]
        simp only [show m + 1 - 1 = m by omega]
      have hQord : Q.rootMultiplicity (algebraMap (ZMod p) E r) =
          frobeniusOrderSum p (m + 1) := by
        dsimp only [Q]
        rw [rootMultiplicity_mul hQ, hEAord, hLDord, zero_add]
      have hlt : Q.rootMultiplicity (algebraMap (ZMod p) E r) <
          P.rootMultiplicity (algebraMap (ZMod p) E r) := by
        rw [hQord, hPord, frobeniusOrderSum_succ]
        have hp : 1 < p := (Fact.out : p.Prime).one_lt
        have hpow : p ^ m < p ^ (m + 1) :=
          Nat.pow_lt_pow_right hp (by omega)
        omega
      have hsum : P + Q ≠ 0 := by
        intro hzero
        have hord := rootMultiplicity_add_eq_right_of_lt hP hQ hlt
        rw [hzero, rootMultiplicity_zero, hQord] at hord
        have hpos : 0 < frobeniusOrderSum p (m + 1) := by
          rw [frobeniusOrderSum_succ]
          exact Nat.add_pos_right _ (Nat.pow_pos (Fact.out : p.Prime).pos)
        omega
      change lowRationalDenominator p (m + 2) B ≠ 0 ∧ _
      rw [show m + 2 = (m + 1) + 1 by omega,
        lowRationalDenominator_succ, lowRationalNumerator_succ]
      refine ⟨mul_ne_zero hLD hEB, ?_, hsum, ?_⟩
      · rw [rootMultiplicity_mul (mul_ne_zero hLD hEB), hLDord,
          hEBord, frobeniusOrderSum_succ p (m + 1),
          frobeniusOrderSum_succ p m]
      · change (P + Q).rootMultiplicity (algebraMap (ZMod p) E r) = _
        rw [rootMultiplicity_add_eq_right_of_lt hP hQ hlt, hQord]
        congr 2

end RationalStepanov

end Erdos387

end

/-! ## Waring.Analytic.StepanovHasseFrobenius -/

noncomputable section

namespace Waring.Analytic

open Polynomial

namespace Stepanov

private theorem StepanovHasseFrobenius_coeff_mul_eq_mul_coeff_zero_of_right_low_coeff_eq_zero
    {R : Type*} [CommSemiring R] {F G : R[X]} {r : Nat}
    (hG : ∀ j, 0 < j → j ≤ r → G.coeff j = 0) :
    (F * G).coeff r = F.coeff r * G.coeff 0 := by
  classical
  rw [coeff_mul, Finset.sum_eq_single (r, 0)]
  · intro ij hij hne
    have hijsum : ij.1 + ij.2 = r := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
    have hjle : ij.2 ≤ r := by omega
    have hjpos : 0 < ij.2 := by
      by_contra hj
      have hjzero : ij.2 = 0 := Nat.eq_zero_of_not_pos hj
      have hizero : ij.1 = r := by omega
      exact hne (Prod.ext hizero hjzero)
    rw [hG ij.2 hjpos hjle, mul_zero]
  · simp

theorem taylor_expand_pow
    {E : Type*} [CommRing E] {p n : Nat} [Fact p.Prime]
    [CharP E p] (x : E) (g : E[X]) :
  taylor x (expand E (p ^ n) g) =
      expand E (p ^ n) (taylor (x ^ (p ^ n)) g) := by
  simp only [taylor_apply, expand_eq_comp_X_pow, comp_assoc, X_pow_comp,
    add_comp, X_comp, C_comp]
  rw [add_pow_char_pow]
  rw [← map_pow]

theorem coeff_taylor_expand_pow_eq_zero
    {E : Type*} [CommRing E] {p n r : Nat} [Fact p.Prime]
    [CharP E p] (hp : 0 < p) (x : E) (g : E[X])
    (hrpos : 0 < r) (hr : r < p ^ n) :
    (taylor x (expand E (p ^ n) g)).coeff r = 0 := by
  rw [taylor_expand_pow x g, coeff_expand (Nat.pow_pos hp),
    if_neg (Nat.not_dvd_of_pos_of_lt hrpos hr)]

theorem coeff_zero_taylor_expand_pow
    {E : Type*} [CommRing E] {p n : Nat} [Fact p.Prime]
    [CharP E p] (hp : 0 < p) (x : E) (g : E[X]) :
    (taylor x (expand E (p ^ n) g)).coeff 0 =
      g.eval (x ^ (p ^ n)) := by
  rw [taylor_expand_pow x g, coeff_expand (Nat.pow_pos hp),
    if_pos (dvd_zero (p ^ n))]
  simp

theorem eval_hasseDeriv_mul_expand_pow
    {E : Type*} [CommRing E] {p n r : Nat} [Fact p.Prime]
    [CharP E p] (hp : 0 < p) (x : E) (e g : E[X])
    (hr : r < p ^ n) :
    (hasseDeriv r (e * expand E (p ^ n) g)).eval x =
      (hasseDeriv r e).eval x * g.eval (x ^ (p ^ n)) := by
  rw [← taylor_coeff, taylor_mul]
  calc
    (taylor x e * taylor x (expand E (p ^ n) g)).coeff r =
        (taylor x e).coeff r *
          (taylor x (expand E (p ^ n) g)).coeff 0 := by
      apply StepanovHasseFrobenius_coeff_mul_eq_mul_coeff_zero_of_right_low_coeff_eq_zero
      intro j hjpos hjr
      exact coeff_taylor_expand_pow_eq_zero hp x g hjpos
        (hjr.trans_lt hr)
    _ = (taylor x e).coeff r * g.eval (x ^ (p ^ n)) := by
      rw [coeff_zero_taylor_expand_pow hp x g]
    _ = (hasseDeriv r e).eval x * g.eval (x ^ (p ^ n)) := by
      rw [taylor_coeff]

end Stepanov

end Waring.Analytic

end

/-! ## Waring.Analytic.StepanovParameters -/

noncomputable section

namespace Waring.Analytic

namespace Stepanov

def S (p h : Nat) : Nat :=
  p ^ (2 * h + 4)

def K (p h : Nat) : Nat :=
  p ^ h

def R (p h : Nat) : Nat :=
  p ^ (h + 1)

def A (p h d : Nat) : Nat :=
  d * (p - 1) * p ^ (h + 2)

def D (p h d : Nat) : Nat :=
  S p h + A p h d + K p h

theorem S_eq_K_mul_pow (p h : Nat) :
    S p h = K p h * p ^ (h + 4) := by
  simp only [S, K, ← pow_add]
  congr 1
  omega

theorem R_mul_pow_eq_p_mul_S (p h : Nat) :
    R p h * p ^ (h + 4) = p * S p h := by
  simp only [R, S]
  calc
    p ^ (h + 1) * p ^ (h + 4) = p ^ ((h + 1) + (h + 4)) :=
      (pow_add _ _ _).symm
    _ = p ^ (1 + (2 * h + 4)) := by congr 1; omega
    _ = p ^ 1 * p ^ (2 * h + 4) := pow_add _ _ _
    _ = p * p ^ (2 * h + 4) := by rw [pow_one]

theorem R_lt_pow {p h : Nat} (hp : 1 < p) :
    R p h < p ^ (h + 3) := by
  rw [R]
  exact Nat.pow_lt_pow_right hp (by omega)

end Stepanov

end Waring.Analytic

end

/-! ## Waring.Analytic.StepanovAuxiliaryLinear -/

noncomputable section

namespace Waring.Analytic

open Polynomial

open scoped BigOperators

namespace Stepanov

abbrev AuxiliaryCoefficients (E : Type*) (p h : Nat) :=
  Fin p -> Fin (K p h + 1) -> Fin (S p h) -> E

noncomputable def auxiliaryCoefficientPolynomial
    {E : Type*} [Field E] {p h : Nat}
    (a : AuxiliaryCoefficients E p h) (i : Fin p)
    (k : Fin (K p h + 1)) : E[X] :=
  ((degreeLTEquiv E (S p h)).symm (a i k)).1

theorem natDegree_auxiliaryCoefficientPolynomial_lt
    {E : Type*} [Field E] {p h : Nat}
    (hp : 0 < p)
    (a : AuxiliaryCoefficients E p h) (i : Fin p)
    (k : Fin (K p h + 1)) :
    (auxiliaryCoefficientPolynomial a i k).natDegree < S p h := by
  let q := (degreeLTEquiv E (S p h)).symm (a i k)
  by_cases hq : (q.1 : E[X]) = 0
  · change q.1.natDegree < S p h
    rw [hq, natDegree_zero]
    exact Nat.pow_pos hp
  have hmem := q.2
  rw [mem_degreeLT, degree_eq_natDegree hq, Nat.cast_lt] at hmem
  exact hmem

end Stepanov

end Waring.Analytic

end

/-! ## ErdosProblems.Erdos387.RationalStepanovParameters -/

noncomputable section

namespace Erdos387

open Waring.Analytic.Stepanov

namespace RationalStepanov

def rationalPhaseAllowance (p h s : ℕ) : ℕ :=
  (p - 1) * s * frobeniusOrderSum p (h + 3)

def rationalConditionDegree (p h s : ℕ) : ℕ :=
  S p h + rationalPhaseAllowance p h s + K p h

theorem pred_mul_frobeniusOrderSum_add_one
    {p m : ℕ} (hp : 0 < p) :
    (p - 1) * frobeniusOrderSum p m + 1 = p ^ m := by
  induction m with
  | zero => simp [frobeniusOrderSum]
  | succ m ih =>
      rw [show m + 1 = m + 1 by rfl, frobeniusOrderSum_succ,
        Nat.mul_add, pow_succ]
      calc
        (p - 1) * frobeniusOrderSum p m + (p - 1) * p ^ m + 1 =
            ((p - 1) * frobeniusOrderSum p m + 1) +
              (p - 1) * p ^ m := by ring
        _ = p ^ m + (p - 1) * p ^ m := by rw [ih]
        p ^ m + (p - 1) * p ^ m = (1 + (p - 1)) * p ^ m := by ring
        _ = p * p ^ m := by rw [Nat.add_sub_of_le hp]
        _ = p ^ m * p := Nat.mul_comm _ _

theorem rationalPhaseAllowance_add_K_lt_pow
    {p h s : ℕ} (hp : 1 < p) (hs : s < p) :
    rationalPhaseAllowance p h s + K p h < p ^ (h + 4) := by
  have hp0 : 0 < p := hp.trans_le' (Nat.zero_le _)
  have hsle : s ≤ p - 1 := by omega
  have hgeom := pred_mul_frobeniusOrderSum_add_one
    (p := p) (m := h + 3) hp0
  have hK : K p h ≤ p ^ (h + 3) := by
    unfold K
    exact Nat.pow_le_pow_right hp0 (by omega)
  have hA : rationalPhaseAllowance p h s ≤
      (p - 1) * (p ^ (h + 3) - 1) := by
    unfold rationalPhaseAllowance
    have hrewrite :
        (p - 1) * frobeniusOrderSum p (h + 3) =
          p ^ (h + 3) - 1 := by omega
    calc
      (p - 1) * s * frobeniusOrderSum p (h + 3) =
          s * ((p - 1) * frobeniusOrderSum p (h + 3)) := by ring
      _ = s * (p ^ (h + 3) - 1) := by rw [hrewrite]
      _ ≤ (p - 1) * (p ^ (h + 3) - 1) :=
        Nat.mul_le_mul_right _ hsle
  have hpowpos : 0 < p ^ (h + 3) := Nat.pow_pos hp0
  have hpredpos : 0 < p - 1 := Nat.sub_pos_of_lt hp
  have hsub : p ^ (h + 3) - 1 < p ^ (h + 3) :=
    Nat.sub_lt hpowpos zero_lt_one
  have hcore :
      (p - 1) * (p ^ (h + 3) - 1) + p ^ (h + 3) <
        p * p ^ (h + 3) := by
    calc
      (p - 1) * (p ^ (h + 3) - 1) + p ^ (h + 3) <
          (p - 1) * p ^ (h + 3) + p ^ (h + 3) :=
        Nat.add_lt_add_right (Nat.mul_lt_mul_of_pos_left hsub hpredpos) _
      _ = ((p - 1) + 1) * p ^ (h + 3) := by ring
      _ = p * p ^ (h + 3) := by rw [Nat.sub_add_cancel hp.le]
  calc
    rationalPhaseAllowance p h s + K p h ≤
        (p - 1) * (p ^ (h + 3) - 1) + p ^ (h + 3) :=
      Nat.add_le_add hA hK
    _ < p * p ^ (h + 3) := hcore
    _ = p ^ (h + 4) := by
      calc
        p * p ^ (h + 3) = p ^ 1 * p ^ (h + 3) := by rw [pow_one]
        _ = p ^ (1 + (h + 3)) := (pow_add p 1 (h + 3)).symm
        _ = p ^ (h + 4) := by congr 1; omega

theorem rationalConstraints_lt_coefficients
    {p h s : ℕ} (hp : 1 < p) (hs : s < p) :
    R p h * rationalConditionDegree p h s <
      p * S p h * (K p h + 1) := by
  have hp0 : 0 < p := by omega
  have hinside :
      S p h + (rationalPhaseAllowance p h s + K p h) <
        S p h + p ^ (h + 4) :=
    Nat.add_lt_add_left (rationalPhaseAllowance_add_K_lt_pow hp hs) _
  have hRpos : 0 < R p h := Nat.pow_pos hp0
  have hmul := Nat.mul_lt_mul_of_pos_left hinside hRpos
  rw [← add_assoc] at hmul
  change R p h * rationalConditionDegree p h s <
      R p h * (S p h + p ^ (h + 4)) at hmul
  calc
    R p h * rationalConditionDegree p h s <
        R p h * (S p h + p ^ (h + 4)) := hmul
    _ = R p h * (p ^ (h + 4) * K p h + p ^ (h + 4)) := by
      rw [S_eq_K_mul_pow]
      ring
    _ = (R p h * p ^ (h + 4)) * (K p h + 1) := by ring
    _ = (p * S p h) * (K p h + 1) := by
      rw [R_mul_pow_eq_p_mul_S]
    _ = p * S p h * (K p h + 1) := rfl

end RationalStepanov

end Erdos387

end

/-! ## ErdosProblems.Erdos387.RationalStepanovLinear -/

noncomputable section

namespace Erdos387

open Polynomial

open scoped BigOperators

open Waring.Analytic.Stepanov

namespace RationalStepanov

noncomputable def rationalReducedTerm
    {E : Type*} [CommRing E] (p _h : ℕ) (c pole : E)
    (r i k : ℕ) (e lowN lowD : E[X]) : E[X] :=
  ((hasseDeriv r e * (C c * lowD - lowN) ^ i) *
      lowD ^ (p - 1 - i)) * (X - C pole) ^ k

theorem natDegree_rationalReducedTerm_lt
    {E : Type*} [CommRing E] {p h s r i k : ℕ}
    (hp : 0 < p) (c pole : E) {e lowN lowD : E[X]}
    (he : e.natDegree < S p h)
    (hN : lowN.natDegree ≤ s * frobeniusOrderSum p (h + 3))
    (hD : lowD.natDegree ≤ s * frobeniusOrderSum p (h + 3))
    (hi : i < p) (hk : k ≤ K p h) :
    (rationalReducedTerm p h c pole r i k e lowN lowD).natDegree <
      rationalConditionDegree p h s := by
  let L := s * frobeniusOrderSum p (h + 3)
  have hW : (C c * lowD - lowN).natDegree ≤ L := by
    exact (natDegree_sub_le _ _).trans <| by
      apply max_le
      · exact (natDegree_C_mul_le _ _).trans hD
      · exact hN
  have hderiv : (hasseDeriv r e).natDegree ≤ e.natDegree :=
    (natDegree_hasseDeriv_le e r).trans (Nat.sub_le _ _)
  have hWi : ((C c * lowD - lowN) ^ i).natDegree ≤ i * L :=
    natDegree_pow_le_of_le i hW
  have hDp : (lowD ^ (p - 1 - i)).natDegree ≤ (p - 1 - i) * L :=
    natDegree_pow_le_of_le _ hD
  have hcenter : ((X - C pole) ^ k : E[X]).natDegree ≤ k := by
    calc
      ((X - C pole) ^ k : E[X]).natDegree ≤
          k * (X - C pole : E[X]).natDegree := natDegree_pow_le
      _ ≤ k * 1 := Nat.mul_le_mul_left k (natDegree_X_sub_C_le pole)
      _ = k := Nat.mul_one k
  have hdegree :
      (rationalReducedTerm p h c pole r i k e lowN lowD).natDegree ≤
        e.natDegree + i * L + (p - 1 - i) * L + k := by
    unfold rationalReducedTerm
    calc
      (((hasseDeriv r e * (C c * lowD - lowN) ^ i) *
          lowD ^ (p - 1 - i)) * (X - C pole) ^ k).natDegree ≤
          ((hasseDeriv r e).natDegree +
            ((C c * lowD - lowN) ^ i).natDegree) +
              (lowD ^ (p - 1 - i)).natDegree +
                ((X - C pole) ^ k).natDegree := by
        have hmul1 :
            (hasseDeriv r e * (C c * lowD - lowN) ^ i).natDegree ≤
              (hasseDeriv r e).natDegree +
                ((C c * lowD - lowN) ^ i).natDegree := natDegree_mul_le
        have hmul2 :
            ((hasseDeriv r e * (C c * lowD - lowN) ^ i) *
              lowD ^ (p - 1 - i)).natDegree ≤
              (hasseDeriv r e * (C c * lowD - lowN) ^ i).natDegree +
                (lowD ^ (p - 1 - i)).natDegree := natDegree_mul_le
        have hmul3 :
            (((hasseDeriv r e * (C c * lowD - lowN) ^ i) *
              lowD ^ (p - 1 - i)) * (X - C pole) ^ k).natDegree ≤
              ((hasseDeriv r e * (C c * lowD - lowN) ^ i) *
                lowD ^ (p - 1 - i)).natDegree +
                  ((X - C pole) ^ k).natDegree := natDegree_mul_le
        omega
      _ ≤ e.natDegree + i * L + (p - 1 - i) * L + k := by
        omega
  have hi' : i ≤ p - 1 := by omega
  have hphase :
      i * L + (p - 1 - i) * L = rationalPhaseAllowance p h s := by
    unfold rationalPhaseAllowance L
    rw [← Nat.add_mul, Nat.add_sub_of_le hi']
    ring
  unfold rationalConditionDegree
  rw [← hphase]
  omega

abbrev RationalAuxiliaryConditions (E : Type*) (p h s : ℕ) :=
  Fin (R p h) → Fin (rationalConditionDegree p h s) → E

noncomputable def rationalReducedConditionPolynomial
    {E : Type*} [Field E] (p h : ℕ) (c pole : E) (r : ℕ)
    (lowN lowD : E[X]) (a : AuxiliaryCoefficients E p h) : E[X] :=
  ∑ i : Fin p, ∑ k : Fin (K p h + 1),
    rationalReducedTerm p h c pole r i k
      (auxiliaryCoefficientPolynomial a i k) lowN lowD

private theorem RationalStepanovLinear_auxiliaryCoefficientPolynomial_add
    {E : Type*} [Field E] {p h : ℕ}
    (a b : AuxiliaryCoefficients E p h) (i : Fin p)
    (k : Fin (K p h + 1)) :
    auxiliaryCoefficientPolynomial (a + b) i k =
      auxiliaryCoefficientPolynomial a i k +
        auxiliaryCoefficientPolynomial b i k := by
  simp [auxiliaryCoefficientPolynomial]

private theorem RationalStepanovLinear_auxiliaryCoefficientPolynomial_smul
    {E : Type*} [Field E] {p h : ℕ} (z : E)
    (a : AuxiliaryCoefficients E p h) (i : Fin p)
    (k : Fin (K p h + 1)) :
    auxiliaryCoefficientPolynomial (z • a) i k =
      z • auxiliaryCoefficientPolynomial a i k := by
  simp [auxiliaryCoefficientPolynomial]

private theorem RationalStepanovLinear_rationalReducedConditionPolynomial_add
    {E : Type*} [Field E] (p h : ℕ) (c pole : E) (r : ℕ)
    (lowN lowD : E[X]) (a b : AuxiliaryCoefficients E p h) :
    rationalReducedConditionPolynomial p h c pole r lowN lowD (a + b) =
      rationalReducedConditionPolynomial p h c pole r lowN lowD a +
        rationalReducedConditionPolynomial p h c pole r lowN lowD b := by
  simp only [rationalReducedConditionPolynomial,
    RationalStepanovLinear_auxiliaryCoefficientPolynomial_add, rationalReducedTerm, map_add,
    add_mul, Finset.sum_add_distrib]

private theorem RationalStepanovLinear_rationalReducedConditionPolynomial_smul
    {E : Type*} [Field E] (p h : ℕ) (c pole : E) (r : ℕ)
    (lowN lowD : E[X]) (z : E) (a : AuxiliaryCoefficients E p h) :
    rationalReducedConditionPolynomial p h c pole r lowN lowD (z • a) =
      z • rationalReducedConditionPolynomial p h c pole r lowN lowD a := by
  simp only [rationalReducedConditionPolynomial,
    RationalStepanovLinear_auxiliaryCoefficientPolynomial_smul, rationalReducedTerm,
    LinearMap.map_smul_of_tower, smul_mul_assoc, Finset.smul_sum]

noncomputable def rationalReducedConditionLinear
    {E : Type*} [Field E] (p h s : ℕ) (c pole : E)
    (lowN lowD : E[X]) :
    AuxiliaryCoefficients E p h →ₗ[E] RationalAuxiliaryConditions E p h s where
  toFun a r j :=
    (rationalReducedConditionPolynomial p h c pole r lowN lowD a).coeff j
  map_add' a b := by
    funext r j
    rw [RationalStepanovLinear_rationalReducedConditionPolynomial_add, coeff_add]
    rfl
  map_smul' z a := by
    funext r j
    rw [RationalStepanovLinear_rationalReducedConditionPolynomial_smul, coeff_smul]
    rfl

private theorem RationalStepanovLinear_finrank_auxiliaryCoefficients
    {E : Type*} [Field E] (p h : ℕ) :
    Module.finrank E (AuxiliaryCoefficients E p h) =
      p * S p h * (K p h + 1) := by
  simp [AuxiliaryCoefficients, Module.finrank_pi_fintype]
  ring

private theorem RationalStepanovLinear_finrank_rationalAuxiliaryConditions
    {E : Type*} [Field E] (p h s : ℕ) :
    Module.finrank E (RationalAuxiliaryConditions E p h s) =
      R p h * rationalConditionDegree p h s := by
  simp [RationalAuxiliaryConditions, Module.finrank_pi_fintype]

theorem exists_nonzero_rationalAuxiliaryCoefficients
    {E : Type*} [Field E] {p h s : ℕ}
    (hp : 1 < p) (hs : s < p) (c pole : E) (lowN lowD : E[X]) :
    ∃ a : AuxiliaryCoefficients E p h,
      a ≠ 0 ∧
        rationalReducedConditionLinear p h s c pole lowN lowD a = 0 := by
  let T := rationalReducedConditionLinear p h s c pole lowN lowD
  have hker : LinearMap.ker T ≠ ⊥ := by
    intro hbot
    have hinj : Function.Injective T := LinearMap.ker_eq_bot.mp hbot
    have hle := T.finrank_le_finrank_of_injective hinj
    rw [RationalStepanovLinear_finrank_auxiliaryCoefficients p h,
      RationalStepanovLinear_finrank_rationalAuxiliaryConditions p h s] at hle
    exact (not_le_of_gt (rationalConstraints_lt_coefficients hp hs)) hle
  obtain ⟨a, ha, hane⟩ := (LinearMap.ker T).ne_bot_iff.mp hker
  exact ⟨a, hane, ha⟩

theorem rationalReducedConditionPolynomial_eq_zero_of_linear_eq_zero
    {E : Type*} [Field E] {p h s : ℕ} (hp : 0 < p)
    (c pole : E) {lowN lowD : E[X]}
    (hN : lowN.natDegree ≤ s * frobeniusOrderSum p (h + 3))
    (hD : lowD.natDegree ≤ s * frobeniusOrderSum p (h + 3))
    {a : AuxiliaryCoefficients E p h}
    (ha : rationalReducedConditionLinear p h s c pole lowN lowD a = 0)
    {r : ℕ} (hr : r < R p h) :
    rationalReducedConditionPolynomial p h c pole r lowN lowD a = 0 := by
  let F := rationalReducedConditionPolynomial p h c pole r lowN lowD a
  have hdegree : F.natDegree < rationalConditionDegree p h s := by
    have hboundPos : 0 < rationalConditionDegree p h s := by
      exact Nat.add_pos_left (Nat.add_pos_left (Nat.pow_pos hp) _) _
    refine (natDegree_sum_le_of_forall_le _ _ ?_).trans_lt
      (Nat.pred_lt hboundPos.ne')
    intro i hi
    apply natDegree_sum_le_of_forall_le
    intro k hk
    exact Nat.le_pred_of_lt <|
      natDegree_rationalReducedTerm_lt hp c pole
        (natDegree_auxiliaryCoefficientPolynomial_lt hp a i k)
        hN hD i.isLt (by omega)
  ext j
  by_cases hj : j < rationalConditionDegree p h s
  · have hcoeff := congrFun (congrFun ha ⟨r, hr⟩) ⟨j, hj⟩
    change (rationalReducedConditionPolynomial
      p h c pole r lowN lowD a).coeff j = 0 at hcoeff
    exact hcoeff
  · rw [coeff_eq_zero_of_natDegree_lt
      (hdegree.trans_le (Nat.le_of_not_gt hj)), coeff_zero]

end RationalStepanov

end Erdos387

end

/-! ## ErdosProblems.Erdos387.RationalStepanovAuxiliary -/

noncomputable section

namespace Erdos387

open Polynomial

open scoped BigOperators

open Waring.Analytic.Stepanov

namespace RationalStepanov

noncomputable def rationalAuxiliaryTerm
    {E : Type*} [Field E] (p h : ℕ) (pole : E) (i k : ℕ)
    (e lowN lowD : E[X]) : E[X] :=
  e * expand E (p ^ (h + 3))
    (lowN ^ i * lowD ^ (p - 1 - i) *
      expand E (p ^ (h + 3)) ((X - C pole) ^ k))

noncomputable def rationalAuxiliaryPolynomial
    {E : Type*} [Field E] (p h : ℕ) (pole : E)
    (lowN lowD : E[X]) (a : AuxiliaryCoefficients E p h) : E[X] :=
  ∑ i : Fin p, ∑ k : Fin (K p h + 1),
    rationalAuxiliaryTerm p h pole i k
      (auxiliaryCoefficientPolynomial a i k) lowN lowD

theorem eval_hasseDeriv_rationalAuxiliaryTerm
    {E : Type*} [Field E] {p h r i k : ℕ} [Fact p.Prime]
    [CharP E p] (hp : 1 < p) (x pole : E) (e lowN lowD : E[X])
    (hr : r < p ^ (h + 3))
    (hxpow : x ^ (p ^ (2 * (h + 3))) = x) :
    (hasseDeriv r
      (rationalAuxiliaryTerm p h pole i k e lowN lowD)).eval x =
      (hasseDeriv r e).eval x *
        (lowN.eval (x ^ (p ^ (h + 3))) ^ i *
          lowD.eval (x ^ (p ^ (h + 3))) ^ (p - 1 - i) *
            (x - pole) ^ k) := by
  unfold rationalAuxiliaryTerm
  rw [Waring.Analytic.Stepanov.eval_hasseDeriv_mul_expand_pow
    hp.pos x e _ hr]
  simp only [eval_mul, eval_pow, expand_eval, eval_sub, eval_X, eval_C]
  have hpow : (x ^ (p ^ (h + 3))) ^ (p ^ (h + 3)) = x := by
    rw [← pow_mul, ← pow_add]
    simpa only [show (h + 3) + (h + 3) = 2 * (h + 3) by omega]
      using hxpow
  rw [hpow]

theorem eval_highRationalNumerator_eq
    {E : Type*} [CommRing E] (p m : ℕ) (A B : E[X]) (x : E) :
    (highRationalNumerator p m A B).eval x =
      (lowRationalNumerator p m A B).eval (x ^ (p ^ m)) :=
  eval_highRationalNumerator p m A B x

theorem eval_high_mul_low_eq_of_fullRationalTrace
    {E : Type*} [Field E] (p m : ℕ) (A B : E[X])
    (x c : E)
    (hlow : (lowRationalDenominator p m B).eval x ≠ 0)
    (hhigh : (highRationalDenominator p m B).eval x ≠ 0)
    (htrace :
      (fullRationalNumerator p m A B).eval x *
          ((fullRationalDenominator p m B).eval x)⁻¹ = c) :
    (highRationalNumerator p m A B).eval x *
        (lowRationalDenominator p m B).eval x =
      (c * (lowRationalDenominator p m B).eval x -
          (lowRationalNumerator p m A B).eval x) *
        (highRationalDenominator p m B).eval x := by
  rw [eval_fullRationalNumerator, eval_fullRationalDenominator,
    ← eval_highRationalNumerator_eq,
    ← eval_highRationalDenominator] at htrace
  field_simp [hlow, hhigh] at htrace
  calc
    (highRationalNumerator p m A B).eval x *
          (lowRationalDenominator p m B).eval x =
        ((lowRationalNumerator p m A B).eval x *
            (highRationalDenominator p m B).eval x +
          (highRationalNumerator p m A B).eval x *
            (lowRationalDenominator p m B).eval x) -
          (lowRationalNumerator p m A B).eval x *
            (highRationalDenominator p m B).eval x := by ring
    _ = ((highRationalDenominator p m B).eval x *
            (lowRationalDenominator p m B).eval x * c) -
          (lowRationalNumerator p m A B).eval x *
            (highRationalDenominator p m B).eval x := by rw [htrace]
    _ = (c * (lowRationalDenominator p m B).eval x -
          (lowRationalNumerator p m A B).eval x) *
        (highRationalDenominator p m B).eval x := by ring

theorem homogeneous_high_term_mul_low_pow
    {E : Type*} [Field E] {p i : ℕ} (hi : i < p)
    (de hn hd low w center : E) (hrel : hn * low = w * hd) :
    (de * (hn ^ i * hd ^ (p - 1 - i) * center)) * low ^ (p - 1) =
      hd ^ (p - 1) *
        (de * (w ^ i * low ^ (p - 1 - i) * center)) := by
  have hi' : i ≤ p - 1 := by omega
  have hsplit : p - 1 = i + (p - 1 - i) := by omega
  have hpowers : hn ^ i * low ^ i = w ^ i * hd ^ i := by
    rw [← mul_pow, hrel, mul_pow]
  have hlowPow : low ^ (p - 1) = low ^ i * low ^ (p - 1 - i) := by
    exact (congrArg (fun n : ℕ => low ^ n) hsplit).trans (pow_add low _ _)
  have hhighPow : hd ^ (p - 1) = hd ^ i * hd ^ (p - 1 - i) := by
    exact (congrArg (fun n : ℕ => hd ^ n) hsplit).trans (pow_add hd _ _)
  rw [hlowPow, hhighPow]
  calc
    (de * (hn ^ i * hd ^ (p - 1 - i) * center)) *
          (low ^ i * low ^ (p - 1 - i)) =
        de * (hn ^ i * low ^ i) * hd ^ (p - 1 - i) *
          low ^ (p - 1 - i) * center := by ring
    _ = de * (w ^ i * hd ^ i) * hd ^ (p - 1 - i) *
          low ^ (p - 1 - i) * center := by rw [hpowers]
    _ = (hd ^ i * hd ^ (p - 1 - i)) *
        (de * (w ^ i * low ^ (p - 1 - i) * center)) := by ring

theorem eval_hasseDeriv_rationalAuxiliaryPolynomial_mul_lowDen
    {E : Type*} [Field E] {p h r : ℕ} [Fact p.Prime]
    [CharP E p] (hp : 1 < p) (x c pole : E)
    (lowN lowD highN highD : E[X])
    (a : AuxiliaryCoefficients E p h)
    (hr : r < p ^ (h + 3))
    (hxpow : x ^ (p ^ (2 * (h + 3))) = x)
    (hhighN : highN.eval x = lowN.eval (x ^ (p ^ (h + 3))))
    (hhighD : highD.eval x = lowD.eval (x ^ (p ^ (h + 3))))
    (hrel : highN.eval x * lowD.eval x =
      (c * lowD.eval x - lowN.eval x) * highD.eval x) :
    (hasseDeriv r
      (rationalAuxiliaryPolynomial p h pole lowN lowD a)).eval x *
        (lowD.eval x) ^ (p - 1) =
      (highD.eval x) ^ (p - 1) *
        (rationalReducedConditionPolynomial
          p h c pole r lowN lowD a).eval x := by
  change (evalRingHom x)
      (hasseDeriv r
        (rationalAuxiliaryPolynomial p h pole lowN lowD a)) *
          lowD.eval x ^ (p - 1) = _
  simp only [rationalAuxiliaryPolynomial,
    rationalReducedConditionPolynomial, map_sum,
    eval_finsetSum, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hiMem
  apply Finset.sum_congr rfl
  intro k hkMem
  change (hasseDeriv r
      (rationalAuxiliaryTerm p h pole (i : ℕ) (k : ℕ)
        (auxiliaryCoefficientPolynomial a i k) lowN lowD)).eval x *
        lowD.eval x ^ (p - 1) = _
  rw [eval_hasseDeriv_rationalAuxiliaryTerm hp x pole
    (auxiliaryCoefficientPolynomial a i k) lowN lowD hr hxpow,
    rationalReducedTerm, eval_mul, eval_mul, eval_mul, eval_pow,
    eval_sub, eval_mul, eval_C, eval_pow, eval_pow, eval_sub, eval_X,
    eval_C, ← hhighN, ← hhighD]
  simpa only [mul_assoc] using
    (homogeneous_high_term_mul_low_pow i.isLt
      (eval x (hasseDeriv r (auxiliaryCoefficientPolynomial a i k)))
      (highN.eval x) (highD.eval x) (lowD.eval x)
      (c * lowD.eval x - lowN.eval x) ((x - pole) ^ (k : ℕ)) hrel)

theorem hasseDeriv_rationalAuxiliaryPolynomial_eval_eq_zero
    {E : Type*} [Field E] {p h s : ℕ} [Fact p.Prime]
    [CharP E p] (hp : 1 < p) (c pole : E)
    {lowN lowD highN highD : E[X]}
    (hN : lowN.natDegree ≤ s * frobeniusOrderSum p (h + 3))
    (hD : lowD.natDegree ≤ s * frobeniusOrderSum p (h + 3))
    {a : AuxiliaryCoefficients E p h}
    (ha : rationalReducedConditionLinear
      p h s c pole lowN lowD a = 0)
    {x : E} (hxpow : x ^ (p ^ (2 * (h + 3))) = x)
    (hlow : lowD.eval x ≠ 0)
    (hhighN : highN.eval x = lowN.eval (x ^ (p ^ (h + 3))))
    (hhighD : highD.eval x = lowD.eval (x ^ (p ^ (h + 3))))
    (hrel : highN.eval x * lowD.eval x =
      (c * lowD.eval x - lowN.eval x) * highD.eval x)
    {r : ℕ} (hr : r < R p h) :
    (hasseDeriv r
      (rationalAuxiliaryPolynomial p h pole lowN lowD a)).eval x = 0 := by
  have hrpow : r < p ^ (h + 3) := hr.trans (R_lt_pow hp)
  have hred := rationalReducedConditionPolynomial_eq_zero_of_linear_eq_zero
    hp.pos c pole hN hD ha hr
  have hidentity := eval_hasseDeriv_rationalAuxiliaryPolynomial_mul_lowDen
    hp x c pole lowN lowD highN highD a hrpow hxpow hhighN hhighD hrel
  rw [hred, eval_zero, mul_zero] at hidentity
  exact (mul_eq_zero.mp hidentity).resolve_right (pow_ne_zero _ hlow)

end RationalStepanov

end Erdos387

end

/-! ## ErdosProblems.Erdos387.RationalStepanovDegree -/

noncomputable section

namespace Erdos387

open Polynomial

open Waring.Analytic.Stepanov

namespace RationalStepanov

def rationalAuxiliaryDegreeBound (p h s : ℕ) : ℕ :=
  S p h + p ^ (h + 3) *
    (rationalPhaseAllowance p h s + p ^ (h + 3) * K p h)

def rationalTraceFiberBound (p h s : ℕ) : ℕ :=
  p ^ (2 * (h + 3) - 1) + p ^ (h + 3) +
    p ^ 2 * rationalPhaseAllowance p h s

theorem rationalAuxiliaryDegreeBound_eq_R_mul
    (p h s : ℕ) :
    rationalAuxiliaryDegreeBound p h s =
      R p h * rationalTraceFiberBound p h s := by
  unfold rationalAuxiliaryDegreeBound rationalTraceFiberBound
  unfold S K R
  simp only [Nat.mul_add]
  have hS : p ^ (2 * h + 4) = p ^ (h + 1) * p ^ (h + 3) := by
    rw [← pow_add]
    exact congrArg (fun n : ℕ => p ^ n) (by omega)
  have hA : p ^ (h + 3) * rationalPhaseAllowance p h s =
      p ^ (h + 1) * (p ^ 2 * rationalPhaseAllowance p h s) := by
    rw [show h + 3 = (h + 1) + 2 by omega, pow_add]
    ring
  have hK : p ^ (h + 3) * (p ^ (h + 3) * p ^ h) =
      p ^ (h + 1) * p ^ (2 * (h + 3) - 1) := by
    calc
      p ^ (h + 3) * (p ^ (h + 3) * p ^ h) =
          p ^ (h + 3) * p ^ ((h + 3) + h) := by
            exact congrArg (p ^ (h + 3) * ·) (pow_add p (h + 3) h).symm
      _ = p ^ (h + 3 + (h + 3 + h)) := (pow_add _ _ _).symm
      _ = p ^ ((h + 1) + (2 * (h + 3) - 1)) :=
        congrArg (fun n : ℕ => p ^ n) (by omega)
      _ = p ^ (h + 1) * p ^ (2 * (h + 3) - 1) := pow_add _ _ _
  rw [hS, hA, hK]
  ring_nf

theorem natDegree_rationalAuxiliaryTerm_lt
    {E : Type*} [Field E] {p h s i k : ℕ}
    (hp : 0 < p) {e lowN lowD : E[X]}
    (he : e.natDegree < S p h)
    (hN : lowN.natDegree ≤ s * frobeniusOrderSum p (h + 3))
    (hD : lowD.natDegree ≤ s * frobeniusOrderSum p (h + 3))
    (hi : i < p) (hk : k ≤ K p h) (pole : E) :
    (rationalAuxiliaryTerm p h pole i k e lowN lowD).natDegree <
      rationalAuxiliaryDegreeBound p h s := by
  let L := s * frobeniusOrderSum p (h + 3)
  have hi' : i ≤ p - 1 := by omega
  have hlow :
      (lowN ^ i * lowD ^ (p - 1 - i) *
        expand E (p ^ (h + 3)) ((X - C pole) ^ k)).natDegree ≤
        rationalPhaseAllowance p h s + p ^ (h + 3) * k := by
    have hNi : (lowN ^ i).natDegree ≤ i * L :=
      natDegree_pow_le_of_le i hN
    have hDi : (lowD ^ (p - 1 - i)).natDegree ≤
        (p - 1 - i) * L :=
      natDegree_pow_le_of_le _ hD
    have hcenter : ((X - C pole) ^ k : E[X]).natDegree ≤ k := by
      calc
        ((X - C pole) ^ k : E[X]).natDegree ≤
            k * (X - C pole : E[X]).natDegree := natDegree_pow_le
        _ ≤ k * 1 := Nat.mul_le_mul_left k (natDegree_X_sub_C_le pole)
        _ = k := Nat.mul_one k
    have hexpand :
        (expand E (p ^ (h + 3)) ((X - C pole) ^ k)).natDegree ≤
          p ^ (h + 3) * k := by
      rw [natDegree_expand]
      calc
        ((X - C pole) ^ k : E[X]).natDegree * p ^ (h + 3) ≤
            k * p ^ (h + 3) := Nat.mul_le_mul_right _ hcenter
        _ = p ^ (h + 3) * k := Nat.mul_comm _ _
    have hsum :
        i * L + (p - 1 - i) * L = rationalPhaseAllowance p h s := by
      unfold rationalPhaseAllowance L
      rw [← Nat.add_mul, Nat.add_sub_of_le hi']
      ring
    calc
      (lowN ^ i * lowD ^ (p - 1 - i) *
          expand E (p ^ (h + 3)) ((X - C pole) ^ k)).natDegree ≤
          (lowN ^ i).natDegree + (lowD ^ (p - 1 - i)).natDegree +
            (expand E (p ^ (h + 3)) ((X - C pole) ^ k)).natDegree := by
        exact (natDegree_mul_le.trans
          (Nat.add_le_add_right natDegree_mul_le _))
      _ ≤ i * L + (p - 1 - i) * L + p ^ (h + 3) * k := by omega
      _ = rationalPhaseAllowance p h s + p ^ (h + 3) * k := by rw [hsum]
  unfold rationalAuxiliaryTerm rationalAuxiliaryDegreeBound
  have houter :
      (expand E (p ^ (h + 3))
        (lowN ^ i * lowD ^ (p - 1 - i) *
          expand E (p ^ (h + 3)) ((X - C pole) ^ k))).natDegree ≤
        p ^ (h + 3) *
          (rationalPhaseAllowance p h s + p ^ (h + 3) * k) := by
    rw [natDegree_expand]
    calc
      (lowN ^ i * lowD ^ (p - 1 - i) *
          expand E (p ^ (h + 3)) ((X - C pole) ^ k)).natDegree *
            p ^ (h + 3) ≤
          (rationalPhaseAllowance p h s + p ^ (h + 3) * k) *
            p ^ (h + 3) := Nat.mul_le_mul_right _ hlow
      _ = p ^ (h + 3) *
          (rationalPhaseAllowance p h s + p ^ (h + 3) * k) :=
        Nat.mul_comm _ _
  have hk' : p ^ (h + 3) * k ≤ p ^ (h + 3) * K p h :=
    Nat.mul_le_mul_left _ hk
  calc
    (e * expand E (p ^ (h + 3))
      (lowN ^ i * lowD ^ (p - 1 - i) *
        expand E (p ^ (h + 3)) ((X - C pole) ^ k))).natDegree ≤
        e.natDegree +
          (expand E (p ^ (h + 3))
            (lowN ^ i * lowD ^ (p - 1 - i) *
              expand E (p ^ (h + 3)) ((X - C pole) ^ k))).natDegree :=
      natDegree_mul_le
    _ ≤ e.natDegree + p ^ (h + 3) *
        (rationalPhaseAllowance p h s + p ^ (h + 3) * k) :=
      Nat.add_le_add_left houter _
    _ < S p h + p ^ (h + 3) *
        (rationalPhaseAllowance p h s + p ^ (h + 3) * K p h) := by
      have := Nat.mul_le_mul_left (p ^ (h + 3))
        (Nat.add_le_add_left hk' (rationalPhaseAllowance p h s))
      omega

theorem natDegree_rationalAuxiliaryPolynomial_lt
    {E : Type*} [Field E] {p h s : ℕ} (hp : 0 < p)
    {lowN lowD : E[X]}
    (hN : lowN.natDegree ≤ s * frobeniusOrderSum p (h + 3))
    (hD : lowD.natDegree ≤ s * frobeniusOrderSum p (h + 3))
    (pole : E) (a : AuxiliaryCoefficients E p h) :
    (rationalAuxiliaryPolynomial p h pole lowN lowD a).natDegree <
      rationalAuxiliaryDegreeBound p h s := by
  have hboundPos : 0 < rationalAuxiliaryDegreeBound p h s := by
    unfold rationalAuxiliaryDegreeBound S
    exact Nat.add_pos_left (Nat.pow_pos hp) _
  refine (natDegree_sum_le_of_forall_le _ _ ?_).trans_lt
    (Nat.pred_lt hboundPos.ne')
  intro i hiMem
  apply natDegree_sum_le_of_forall_le
  intro k hkMem
  exact Nat.le_pred_of_lt <|
    natDegree_rationalAuxiliaryTerm_lt hp
      (natDegree_auxiliaryCoefficientPolynomial_lt hp a i k)
      hN hD i.isLt (by omega) pole

end RationalStepanov

end Erdos387

end

/-! ## ErdosProblems.Erdos387.RationalStepanovNonvanishing -/

noncomputable section

namespace Erdos387

open Polynomial

open scoped BigOperators

open Waring.Analytic.Stepanov

namespace RationalStepanov

theorem rootMultiplicity_pow_of_ne_zero
    {E : Type*} [Field E] {P : E[X]} (hP : P ≠ 0) (r : E) (n : ℕ) :
    (P ^ n).rootMultiplicity r = n * P.rootMultiplicity r := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, rootMultiplicity_mul (mul_ne_zero (pow_ne_zero _ hP) hP),
        ih]
      ring

theorem rootMultiplicity_rationalAuxiliaryTerm
    {E : Type*} [Field E] {p h i k : ℕ} [Fact p.Prime]
    [CharP E p] (hp : 0 < p) (pole : E) (e lowN lowD : E[X])
    (he : e ≠ 0) (hN : lowN ≠ 0) (hD : lowD ≠ 0)
    (hfixed : pole ^ (p ^ (h + 3)) = pole) :
    (rationalAuxiliaryTerm p h pole i k e lowN lowD).rootMultiplicity pole =
      e.rootMultiplicity pole + p ^ (h + 3) *
        (i * lowN.rootMultiplicity pole +
          (p - 1 - i) * lowD.rootMultiplicity pole + p ^ (h + 3) * k) := by
  rw [rationalAuxiliaryTerm]
  have hcenter : ((X - C pole) ^ k : E[X]) ≠ 0 :=
    pow_ne_zero _ (X_sub_C_ne_zero pole)
  have hcenterExpand : expand E (p ^ (h + 3)) ((X - C pole) ^ k) ≠ 0 :=
    (expand_ne_zero (Nat.pow_pos hp)).mpr hcenter
  have hlowPowers : lowN ^ i * lowD ^ (p - 1 - i) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ hN) (pow_ne_zero _ hD)
  have hinner :
      lowN ^ i * lowD ^ (p - 1 - i) *
        expand E (p ^ (h + 3)) ((X - C pole) ^ k) ≠ 0 :=
    mul_ne_zero hlowPowers hcenterExpand
  have houter : expand E (p ^ (h + 3))
      (lowN ^ i * lowD ^ (p - 1 - i) *
        expand E (p ^ (h + 3)) ((X - C pole) ^ k)) ≠ 0 :=
    (expand_ne_zero (Nat.pow_pos hp)).mpr hinner
  rw [rootMultiplicity_mul (mul_ne_zero he houter),
    rootMultiplicity_expand_pow, hfixed,
    rootMultiplicity_mul hinner,
    rootMultiplicity_mul hlowPowers,
    rootMultiplicity_pow_of_ne_zero hN,
    rootMultiplicity_pow_of_ne_zero hD,
    rootMultiplicity_expand_pow, hfixed,
    rootMultiplicity_X_sub_C_pow]

def rationalPoleOrderLabel (p h eOrder i k : ℕ) : ℕ :=
  p ^ (h + 3) * ((p - 1) * frobeniusOrderSum p (h + 2)) + eOrder +
    p ^ (2 * (h + 3) - 1) * ((p - 1 - i) + p * k)

theorem rootMultiplicity_rationalAuxiliaryTerm_eq_label
    {p h i k : ℕ} [NeZero p] [Fact p.Prime]
    {E : Type*} [Field E] [CharP E p] [Algebra (ZMod p) E]
    (coeff : ZMod p → ZMod p) {r : ZMod p}
    (hr : r ∈ InverseRational.poleSupport coeff)
    (hiIndex : i < p) (e : E[X]) (he : e ≠ 0) :
    let pole := algebraMap (ZMod p) E r
    let lowN := lowRationalNumerator p (h + 3)
      (mappedSimplePoleNumeratorPolynomial (E := E) coeff)
      (mappedSimplePoleDenominatorPolynomial (E := E) coeff)
    let lowD := lowRationalDenominator p (h + 3)
      (mappedSimplePoleDenominatorPolynomial (E := E) coeff)
    (rationalAuxiliaryTerm p h pole i k e lowN lowD).rootMultiplicity pole =
      rationalPoleOrderLabel p h (e.rootMultiplicity pole) i k := by
  dsimp only
  let pole := algebraMap (ZMod p) E r
  let A := mappedSimplePoleNumeratorPolynomial (E := E) coeff
  let B := mappedSimplePoleDenominatorPolynomial (E := E) coeff
  let lowN := lowRationalNumerator p (h + 3) A B
  let lowD := lowRationalDenominator p (h + 3) B
  have hm : 0 < h + 3 := by omega
  obtain ⟨hD, hDord, hN, hNord⟩ :=
    lowRationalPoleOrders (E := E) coeff hr (h + 3) hm
  change lowD ≠ 0 at hD
  change lowD.rootMultiplicity pole = frobeniusOrderSum p (h + 3) at hDord
  change lowN ≠ 0 at hN
  change lowN.rootMultiplicity pole = frobeniusOrderSum p (h + 2) at hNord
  have hfixed : pole ^ (p ^ (h + 3)) = pole := by
    change iterateFrobenius E p (h + 3) pole = pole
    exact iterateFrobenius_algebraMap_zmod (h + 3) r
  have hraw := rootMultiplicity_rationalAuxiliaryTerm
    (p := p) (h := h) (i := i) (k := k)
    (Fact.out : p.Prime).pos pole e lowN lowD he hN hD hfixed
  rw [hraw, hNord, hDord]
  unfold rationalPoleOrderLabel
  rw [frobeniusOrderSum_succ p (h + 2)]
  have hi : p ^ (h + 3) * p ^ (h + 2) = p ^ (2 * (h + 3) - 1) := by
    rw [← pow_add]
    congr 1
    omega
  have hJ :
      p ^ (h + 3) * ((p - 1 - i) * p ^ (h + 2)) =
        p ^ (2 * (h + 3) - 1) * (p - 1 - i) := by
    calc
      p ^ (h + 3) * ((p - 1 - i) * p ^ (h + 2)) =
          (p ^ (h + 3) * p ^ (h + 2)) * (p - 1 - i) := by ring
      _ = p ^ (2 * (h + 3) - 1) * (p - 1 - i) := by rw [hi]
  have hq :
      p ^ (h + 3) * p ^ (h + 3) =
        p ^ (2 * (h + 3) - 1) * p := by
    calc
      p ^ (h + 3) * p ^ (h + 3) = p ^ ((h + 3) + (h + 3)) :=
        (pow_add _ _ _).symm
      _ = p ^ ((2 * (h + 3) - 1) + 1) :=
        congrArg (fun n : ℕ => p ^ n) (by omega)
      _ = p ^ (2 * (h + 3) - 1) * p := by rw [pow_add, pow_one]
  have hK :
      p ^ (h + 3) * (p ^ (h + 3) * k) =
        p ^ (2 * (h + 3) - 1) * (p * k) := by
    calc
      p ^ (h + 3) * (p ^ (h + 3) * k) =
          (p ^ (h + 3) * p ^ (h + 3)) * k := by ring
      _ = (p ^ (2 * (h + 3) - 1) * p) * k := by rw [hq]
      _ = p ^ (2 * (h + 3) - 1) * (p * k) := by ring
  have hi' : i ≤ p - 1 := by omega
  have hij : i + (p - 1 - i) = p - 1 := Nat.add_sub_of_le hi'
  have hphase :
      i * frobeniusOrderSum p (h + 2) +
          (p - 1 - i) *
            (frobeniusOrderSum p (h + 2) + p ^ (h + 2)) =
        (p - 1) * frobeniusOrderSum p (h + 2) +
          (p - 1 - i) * p ^ (h + 2) := by
    rw [Nat.mul_add]
    calc
      i * frobeniusOrderSum p (h + 2) +
          ((p - 1 - i) * frobeniusOrderSum p (h + 2) +
            (p - 1 - i) * p ^ (h + 2)) =
          (i + (p - 1 - i)) * frobeniusOrderSum p (h + 2) +
            (p - 1 - i) * p ^ (h + 2) := by ring
      _ = (p - 1) * frobeniusOrderSum p (h + 2) +
          (p - 1 - i) * p ^ (h + 2) := by rw [hij]
  have harith :
      e.rootMultiplicity pole + p ^ (h + 3) *
          (i * frobeniusOrderSum p (h + 2) +
            (p - 1 - i) *
              (frobeniusOrderSum p (h + 2) + p ^ (h + 2)) +
            p ^ (h + 3) * k) =
        p ^ (h + 3) * ((p - 1) * frobeniusOrderSum p (h + 2)) +
          e.rootMultiplicity pole +
          p ^ (2 * (h + 3) - 1) * ((p - 1 - i) + p * k) := by
    rw [hphase, Nat.mul_add, Nat.mul_add, hJ, hK]
    ring
  exact harith

theorem exists_rationalAuxiliaryCoefficientPolynomial_ne_zero
    {E : Type*} [Field E] {p h : ℕ}
    {a : AuxiliaryCoefficients E p h} (ha : a ≠ 0) :
    ∃ i : Fin p, ∃ k : Fin (K p h + 1),
      auxiliaryCoefficientPolynomial a i k ≠ 0 := by
  by_contra hall
  push Not at hall
  apply ha
  funext i k
  change a i k = 0
  apply (degreeLTEquiv E (S p h)).symm.injective
  rw [map_zero]
  apply Subtype.ext
  exact hall i k

theorem rootMultiplicity_le_natDegree_of_ne_zero
    {E : Type*} [Field E] {P : E[X]} (_hP : P ≠ 0) (r : E) :
    P.rootMultiplicity r ≤ P.natDegree := by
  rw [rootMultiplicity_eq_natTrailingDegree]
  calc
    (taylor r P).natTrailingDegree ≤ (taylor r P).natDegree :=
      natTrailingDegree_le_natDegree _
    _ = P.natDegree := natDegree_taylor P r

theorem polynomial_sum_ne_zero_of_rootMultiplicity_injOn
    {E : Type*} [Field E] {I : Type*}
    (r : E) (u : Finset I) (F : I → E[X])
    (hu : u.Nonempty) (hF : ∀ z ∈ u, F z ≠ 0)
    (hinj : Set.InjOn (fun z => (F z).rootMultiplicity r) (u : Set I)) :
    ∑ z ∈ u, F z ≠ 0 := by
  classical
  obtain ⟨z, hz, hmin⟩ := u.exists_min_image
    (fun w => (F w).rootMultiplicity r) hu
  let n := (F z).rootMultiplicity r
  have hdiv : (X - C r) ^ (n + 1) ∣ ∑ w ∈ u.erase z, F w := by
    apply Finset.dvd_sum
    intro w hw
    have hwu : w ∈ u := Finset.mem_of_mem_erase hw
    have hle : n ≤ (F w).rootMultiplicity r := hmin w hwu
    have hne : (F w).rootMultiplicity r ≠ n := by
      intro heq
      have hwz : w = z := hinj hwu hz (by simpa only [n] using heq)
      exact (Finset.ne_of_mem_erase hw) hwz
    apply (le_rootMultiplicity_iff (hF w hwu)).mp
    omega
  intro hsum
  have hdecomp := Finset.sum_erase_add u F hz
  rw [hsum] at hdecomp
  have hzEq : F z = -(∑ w ∈ u.erase z, F w) :=
    eq_neg_of_add_eq_zero_right hdecomp
  have hdvz : (X - C r) ^ (n + 1) ∣ F z := by
    rw [hzEq]
    exact dvd_neg.mpr hdiv
  exact (pow_rootMultiplicity_not_dvd (hF z hz) r) (by
    simpa only [n] using hdvz)

theorem rationalPoleOrderLabel_injective
    {p h e₁ e₂ i₁ i₂ k₁ k₂ : ℕ} (hp : 1 < p)
    (he₁ : e₁ < S p h) (he₂ : e₂ < S p h)
    (hi₁ : i₁ < p) (hi₂ : i₂ < p)
    (heq : rationalPoleOrderLabel p h e₁ i₁ k₁ =
      rationalPoleOrderLabel p h e₂ i₂ k₂) :
    e₁ = e₂ ∧ i₁ = i₂ ∧ k₁ = k₂ := by
  let base := p ^ (2 * (h + 3) - 1)
  have hbasePos : 0 < base := Nat.pow_pos (by omega)
  have hSbase : S p h < base := by
    unfold S base
    exact Nat.pow_lt_pow_right hp (by omega)
  have he₁base : e₁ < base := he₁.trans hSbase
  have he₂base : e₂ < base := he₂.trans hSbase
  have hcore :
      e₁ + base * ((p - 1 - i₁) + p * k₁) =
        e₂ + base * ((p - 1 - i₂) + p * k₂) := by
    unfold rationalPoleOrderLabel at heq
    change
      p ^ (h + 3) * ((p - 1) * frobeniusOrderSum p (h + 2)) + e₁ +
          base * ((p - 1 - i₁) + p * k₁) =
        p ^ (h + 3) * ((p - 1) * frobeniusOrderSum p (h + 2)) + e₂ +
          base * ((p - 1 - i₂) + p * k₂) at heq
    omega
  have hemod := congrArg (fun n : ℕ => n % base) hcore
  have he : e₁ = e₂ := by
    simpa [Nat.add_mod, Nat.mul_mod, Nat.mod_eq_of_lt he₁base,
      Nat.mod_eq_of_lt he₂base] using hemod
  have hmul :
      base * ((p - 1 - i₁) + p * k₁) =
        base * ((p - 1 - i₂) + p * k₂) := by
    omega
  have hdigit : (p - 1 - i₁) + p * k₁ =
      (p - 1 - i₂) + p * k₂ :=
    Nat.mul_left_cancel hbasePos hmul
  have hj₁ : p - 1 - i₁ < p := by omega
  have hj₂ : p - 1 - i₂ < p := by omega
  have himod := congrArg (fun n : ℕ => n % p) hdigit
  have hj : p - 1 - i₁ = p - 1 - i₂ := by
    simpa [Nat.add_mod, Nat.mul_mod, Nat.mod_eq_of_lt hj₁,
      Nat.mod_eq_of_lt hj₂] using himod
  have hi : i₁ = i₂ := by omega
  have hkMul : p * k₁ = p * k₂ := by omega
  exact ⟨he, hi, Nat.mul_left_cancel (by omega) hkMul⟩

theorem rationalAuxiliaryTerm_ne_zero
    {E : Type*} [Field E] {p h i k : ℕ} (hp : 0 < p)
    (pole : E) {e lowN lowD : E[X]}
    (he : e ≠ 0) (hN : lowN ≠ 0) (hD : lowD ≠ 0) :
    rationalAuxiliaryTerm p h pole i k e lowN lowD ≠ 0 := by
  unfold rationalAuxiliaryTerm
  apply mul_ne_zero he
  apply (expand_ne_zero (Nat.pow_pos hp)).mpr
  apply mul_ne_zero
  · exact mul_ne_zero (pow_ne_zero _ hN) (pow_ne_zero _ hD)
  · apply (expand_ne_zero (Nat.pow_pos hp)).mpr
    exact pow_ne_zero _ (X_sub_C_ne_zero pole)

theorem rationalAuxiliaryPolynomial_ne_zero
    {p h : ℕ} [NeZero p] [Fact p.Prime]
    {E : Type*} [Field E] [CharP E p] [Algebra (ZMod p) E]
    (coeff : ZMod p → ZMod p) {r : ZMod p}
    (hr : r ∈ InverseRational.poleSupport coeff)
    {a : AuxiliaryCoefficients E p h} (ha : a ≠ 0) :
    let pole := algebraMap (ZMod p) E r
    let lowN := lowRationalNumerator p (h + 3)
      (mappedSimplePoleNumeratorPolynomial (E := E) coeff)
      (mappedSimplePoleDenominatorPolynomial (E := E) coeff)
    let lowD := lowRationalDenominator p (h + 3)
      (mappedSimplePoleDenominatorPolynomial (E := E) coeff)
    rationalAuxiliaryPolynomial p h pole lowN lowD a ≠ 0 := by
  classical
  dsimp only
  let pole := algebraMap (ZMod p) E r
  let A := mappedSimplePoleNumeratorPolynomial (E := E) coeff
  let B := mappedSimplePoleDenominatorPolynomial (E := E) coeff
  let lowN := lowRationalNumerator p (h + 3) A B
  let lowD := lowRationalDenominator p (h + 3) B
  let I := Fin p × Fin (K p h + 1)
  let term : I → E[X] := fun z =>
    rationalAuxiliaryTerm p h pole z.1 z.2
      (auxiliaryCoefficientPolynomial a z.1 z.2) lowN lowD
  let u : Finset I := Finset.univ.filter fun z =>
    auxiliaryCoefficientPolynomial a z.1 z.2 ≠ 0
  have hm : 0 < h + 3 := by omega
  obtain ⟨hD, hDord, hN, hNord⟩ :=
    lowRationalPoleOrders (E := E) coeff hr (h + 3) hm
  change lowD ≠ 0 at hD
  change lowN ≠ 0 at hN
  obtain ⟨i, k, hik⟩ := exists_rationalAuxiliaryCoefficientPolynomial_ne_zero ha
  have hu : u.Nonempty := by
    refine Finset.filter_nonempty_iff.mpr ?_
    exact ⟨(i, k), Finset.mem_univ _, hik⟩
  have htermNe : ∀ z ∈ u, term z ≠ 0 := by
    intro z hz
    have he : auxiliaryCoefficientPolynomial a z.1 z.2 ≠ 0 :=
      (Finset.mem_filter.mp hz).2
    exact rationalAuxiliaryTerm_ne_zero (Fact.out : p.Prime).pos
      pole he hN hD
  have horder : ∀ z ∈ u,
      (term z).rootMultiplicity pole =
        rationalPoleOrderLabel p h
          ((auxiliaryCoefficientPolynomial a z.1 z.2).rootMultiplicity pole)
          z.1 z.2 := by
    intro z hz
    have he : auxiliaryCoefficientPolynomial a z.1 z.2 ≠ 0 :=
      (Finset.mem_filter.mp hz).2
    exact rootMultiplicity_rationalAuxiliaryTerm_eq_label
      (E := E) coeff hr z.1.isLt _ he
  have hinj : Set.InjOn
      (fun z : I => (term z).rootMultiplicity pole) (u : Set I) := by
    intro z hz w hw hzw
    have hez : auxiliaryCoefficientPolynomial a z.1 z.2 ≠ 0 :=
      (Finset.mem_filter.mp hz).2
    have hew : auxiliaryCoefficientPolynomial a w.1 w.2 ≠ 0 :=
      (Finset.mem_filter.mp hw).2
    have hezlt :
        (auxiliaryCoefficientPolynomial a z.1 z.2).rootMultiplicity pole <
          S p h :=
      (rootMultiplicity_le_natDegree_of_ne_zero hez pole).trans_lt
        (natDegree_auxiliaryCoefficientPolynomial_lt
          (Fact.out : p.Prime).pos a z.1 z.2)
    have hewlt :
        (auxiliaryCoefficientPolynomial a w.1 w.2).rootMultiplicity pole <
          S p h :=
      (rootMultiplicity_le_natDegree_of_ne_zero hew pole).trans_lt
        (natDegree_auxiliaryCoefficientPolynomial_lt
          (Fact.out : p.Prime).pos a w.1 w.2)
    change (term z).rootMultiplicity pole = (term w).rootMultiplicity pole at hzw
    rw [horder z hz, horder w hw] at hzw
    obtain ⟨heq, hiq, hkq⟩ := rationalPoleOrderLabel_injective
      (Fact.out : p.Prime).one_lt hezlt hewlt z.1.isLt w.1.isLt hzw
    exact Prod.ext (Fin.ext hiq) (Fin.ext hkq)
  have hnonzero : ∑ z ∈ u, term z ≠ 0 :=
    polynomial_sum_ne_zero_of_rootMultiplicity_injOn
      pole u term hu htermNe hinj
  have hsum : (∑ z ∈ u, term z) =
      rationalAuxiliaryPolynomial p h pole lowN lowD a := by
    rw [rationalAuxiliaryPolynomial]
    change (∑ z ∈ u, term z) =
      ∑ i : Fin p, ∑ k : Fin (K p h + 1), term (i, k)
    rw [← Fintype.sum_prod_type]
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro z hzuniv hznot
    have hezero : auxiliaryCoefficientPolynomial a z.1 z.2 = 0 := by
      by_contra he
      exact hznot (Finset.mem_filter.mpr ⟨hzuniv, he⟩)
    simp [term, hezero, rationalAuxiliaryTerm]
  rw [← hsum]
  exact hnonzero

end RationalStepanov

end Erdos387

end

/-! ## Waring.Analytic.StepanovRootCount -/

noncomputable section

namespace Waring.Analytic

open Polynomial

namespace Stepanov

theorem le_rootMultiplicity_of_hasseDeriv_eval_eq_zero
    {K : Type*} [CommRing K] [IsDomain K] {F : K[X]} {x : K} {r : Nat}
    (hF : F ≠ 0)
    (hvanish : (k : Nat) -> k < r -> (hasseDeriv k F).eval x = 0) :
    r <= F.rootMultiplicity x := by
  rw [Polynomial.rootMultiplicity_eq_natTrailingDegree]
  apply Polynomial.le_natTrailingDegree
  · exact (Polynomial.taylor_eq_zero x F).not.mpr hF
  · intro k hk
    change (Polynomial.taylor x F).coeff k = 0
    rw [Polynomial.taylor_coeff]
    exact hvanish k hk

theorem mul_card_le_natDegree_of_hasseDeriv_eval_eq_zero
    {K : Type*} [CommRing K] [IsDomain K] {F : K[X]} {points : Finset K}
    {r : Nat} (hF : F ≠ 0)
    (hvanish : (x : K) -> x ∈ points -> (k : Nat) -> k < r ->
      (hasseDeriv k F).eval x = 0) :
    r * points.card <= F.natDegree := by
  classical
  by_cases hr : r = 0
  · simp [hr]
  have hrpos : 0 < r := Nat.pos_of_ne_zero hr
  have hmult : (x : K) -> x ∈ points -> r <= F.rootMultiplicity x := by
    intro x hx
    exact le_rootMultiplicity_of_hasseDeriv_eval_eq_zero hF
      (hvanish x hx)
  have hsubset : points <= F.roots.toFinset := by
    intro x hx
    rw [Multiset.mem_toFinset, ← Multiset.count_pos]
    rw [Polynomial.count_roots]
    exact hrpos.trans_le (hmult x hx)
  calc
    r * points.card = ∑ x ∈ points, r := by
      simp [Nat.mul_comm]
    _ <= ∑ x ∈ points, F.rootMultiplicity x :=
      Finset.sum_le_sum hmult
    _ = ∑ x ∈ points, F.roots.count x := by
      simp only [Polynomial.count_roots]
    _ <= ∑ x ∈ F.roots.toFinset, F.roots.count x :=
      Finset.sum_le_sum_of_subset hsubset
    _ = F.roots.card := Multiset.toFinset_sum_count_eq F.roots
    _ <= F.natDegree := Polynomial.card_roots' F



end Stepanov

end Waring.Analytic

end

/-! ## ErdosProblems.Erdos387.RationalStepanovFiberCount -/

noncomputable section

namespace Erdos387

open Polynomial

open Waring.Analytic.Stepanov

namespace RationalStepanov

noncomputable def nonpoleTraceFiber
    {p : ℕ} [NeZero p] [Fact p.Prime]
    {E : Type*} [Field E] [Fintype E] [Algebra (ZMod p) E]
    [FiniteDimensional (ZMod p) E]
    (coeff : ZMod p → ZMod p) (c : ZMod p) : Finset E := by
  classical
  exact Finset.univ.filter fun x : E =>
    ¬ RationalWeil.IsMappedPole coeff x ∧
      Algebra.trace (ZMod p) E
        (RationalWeil.mappedSimplePolePhase coeff x) = c

theorem card_le_rationalTraceFiberBound_of_auxiliary
    {E : Type*} [Field E] {p h s : ℕ} (hp : 0 < p)
    {lowN lowD : E[X]}
    (hN : lowN.natDegree ≤ s * frobeniusOrderSum p (h + 3))
    (hD : lowD.natDegree ≤ s * frobeniusOrderSum p (h + 3))
    (pole : E) (a : AuxiliaryCoefficients E p h)
    (ha : rationalAuxiliaryPolynomial p h pole lowN lowD a ≠ 0)
    (points : Finset E)
    (hvanish : ∀ x ∈ points, ∀ r < R p h,
      (hasseDeriv r
        (rationalAuxiliaryPolynomial p h pole lowN lowD a)).eval x = 0) :
    points.card ≤ rationalTraceFiberBound p h s := by
  have hroot : R p h * points.card ≤
      (rationalAuxiliaryPolynomial p h pole lowN lowD a).natDegree :=
    mul_card_le_natDegree_of_hasseDeriv_eval_eq_zero
      (points := points) (r := R p h) ha hvanish
  have hdegree := natDegree_rationalAuxiliaryPolynomial_lt
    hp hN hD pole a
  have hproduct : R p h * points.card <
      R p h * rationalTraceFiberBound p h s := by
    calc
      R p h * points.card ≤
          (rationalAuxiliaryPolynomial p h pole lowN lowD a).natDegree := hroot
      _ < rationalAuxiliaryDegreeBound p h s := hdegree
      _ = R p h * rationalTraceFiberBound p h s :=
        rationalAuxiliaryDegreeBound_eq_R_mul p h s
  exact (Nat.mul_lt_mul_left (Nat.pow_pos hp)).mp hproduct |>.le

theorem card_nonpole_trace_fiber_le
    {p : ℕ} [NeZero p] [Fact p.Prime] (hp : 1 < p)
    (coeff : ZMod p → ZMod p)
    (hne : (InverseRational.poleSupport coeff).Nonempty)
    (hs : (InverseRational.poleSupport coeff).card < p)
    (h : ℕ) (c : ZMod p) :
    let E := FiniteField.Extension (ZMod p) p (2 * (h + 3))
    letI : Fintype E := Fintype.ofFinite E
    (nonpoleTraceFiber (E := E) coeff c).card ≤
      rationalTraceFiberBound p h
        (InverseRational.poleSupport coeff).card := by
  classical
  let E := FiniteField.Extension (ZMod p) p (2 * (h + 3))
  let : CharP E p :=
    (Algebra.charP_iff (ZMod p) E p).mp (ZMod.charP p)
  let : Fintype E := Fintype.ofFinite E
  let A : E[X] := mappedSimplePoleNumeratorPolynomial coeff
  let B : E[X] := mappedSimplePoleDenominatorPolynomial coeff
  let lowN := lowRationalNumerator p (h + 3) A B
  let lowD := lowRationalDenominator p (h + 3) B
  let highN := highRationalNumerator p (h + 3) A B
  let highD := highRationalDenominator p (h + 3) B
  let points : Finset E := nonpoleTraceFiber coeff c
  obtain ⟨poleBase, hpoleBase⟩ := hne
  let pole : E := algebraMap (ZMod p) E poleBase
  have hAdeg : A.natDegree ≤ (InverseRational.poleSupport coeff).card :=
    (natDegree_mappedSimplePoleNumeratorPolynomial_le
      (E := E) coeff).trans (Nat.sub_le _ _)
  have hBdeg : B.natDegree ≤ (InverseRational.poleSupport coeff).card :=
    (natDegree_mappedSimplePoleDenominatorPolynomial (E := E) coeff).le
  have hNdeg : lowN.natDegree ≤
      (InverseRational.poleSupport coeff).card *
        frobeniusOrderSum p (h + 3) := by
    exact natDegree_lowRationalNumerator_le hAdeg hBdeg
  have hDdeg : lowD.natDegree ≤
      (InverseRational.poleSupport coeff).card *
        frobeniusOrderSum p (h + 3) := by
    exact natDegree_lowRationalDenominator_le hBdeg
  obtain ⟨a, hane, hakernel⟩ := exists_nonzero_rationalAuxiliaryCoefficients
    hp hs (algebraMap (ZMod p) E c) pole lowN lowD
  have ha : rationalAuxiliaryPolynomial p h pole lowN lowD a ≠ 0 := by
    exact rationalAuxiliaryPolynomial_ne_zero
      (E := E) coeff hpoleBase hane
  have hfinrank : Module.finrank (ZMod p) E = 2 * (h + 3) := by
    simpa [E] using
      FiniteField.finrank_zmod_extension (ZMod p) p (2 * (h + 3))
  have hcard : Fintype.card E = p ^ (2 * (h + 3)) := by
    rw [Fintype.card_eq_nat_card]
    change Nat.card
      (FiniteField.Extension (ZMod p) p (2 * (h + 3))) = _
    rw [FiniteField.natCard_extension, Nat.card_zmod]
  have hvanish : ∀ x ∈ points, ∀ r < R p h,
      (hasseDeriv r
        (rationalAuxiliaryPolynomial p h pole lowN lowD a)).eval x = 0 := by
    intro x hx r hr
    have hxdata : ¬ RationalWeil.IsMappedPole coeff x ∧
        Algebra.trace (ZMod p) E
          (RationalWeil.mappedSimplePolePhase coeff x) = c := by
      simpa only [points, nonpoleTraceFiber, Finset.mem_filter,
        Finset.mem_univ, true_and] using hx
    have hxnonpole : ∀ y ∈ InverseRational.poleSupport coeff,
        x ≠ algebraMap (ZMod p) E y := by
      intro y hy hxy
      exact hxdata.1 ⟨y, hy, hxy⟩
    have hxpow : x ^ (p ^ (2 * (h + 3))) = x := by
      rw [← hcard]
      exact FiniteField.pow_card x
    have htrace :
        (fullRationalNumerator p (h + 3) A B).eval x *
            ((fullRationalDenominator p (h + 3) B).eval x)⁻¹ =
          algebraMap (ZMod p) E c := by
      rw [eval_fullRationalTrace_eq_algebraMap_trace
        hfinrank coeff x hxnonpole, hxdata.2]
    have horbit (t : ℕ) : ∀ y ∈ InverseRational.poleSupport coeff,
        x ^ (p ^ t) ≠ algebraMap (ZMod p) E y :=
      frobenius_pow_ne_mappedPole coeff hxnonpole t
    have hlow : lowD.eval x ≠ 0 := by
      change (lowRationalDenominator p (h + 3) B).eval x ≠ 0
      rw [eval_lowRationalDenominator]
      apply Finset.prod_ne_zero_iff.mpr
      intro t ht
      exact eval_mappedSimplePoleDenominatorPolynomial_ne_zero
        coeff (horbit t)
    have hhigh : highD.eval x ≠ 0 := by
      change (highRationalDenominator p (h + 3) B).eval x ≠ 0
      rw [eval_highRationalDenominator, eval_lowRationalDenominator]
      apply Finset.prod_ne_zero_iff.mpr
      intro t ht
      rw [← pow_mul, ← pow_add]
      exact eval_mappedSimplePoleDenominatorPolynomial_ne_zero
        coeff (horbit (h + 3 + t))
    have hrel : highN.eval x * lowD.eval x =
        (algebraMap (ZMod p) E c * lowD.eval x - lowN.eval x) *
          highD.eval x := by
      exact eval_high_mul_low_eq_of_fullRationalTrace
        p (h + 3) A B x (algebraMap (ZMod p) E c) hlow hhigh htrace
    apply hasseDeriv_rationalAuxiliaryPolynomial_eval_eq_zero
      hp (algebraMap (ZMod p) E c) pole hNdeg hDdeg hakernel
      hxpow hlow
    · exact eval_highRationalNumerator p (h + 3) A B x
    · exact eval_highRationalDenominator p (h + 3) B x
    · exact hrel
    · exact hr
  change points.card ≤
    rationalTraceFiberBound p h (InverseRational.poleSupport coeff).card
  exact card_le_rationalTraceFiberBound_of_auxiliary
    (Fact.out : p.Prime).pos hNdeg hDdeg pole a ha points hvanish

end RationalStepanov

end Erdos387

end

/-! ## Waring.Analytic.FiniteFiberCharacterBound -/

noncomputable section

namespace Waring.Analytic

open scoped BigOperators

theorem norm_fintype_sum_comp_le_of_card_fiber_le
    {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq Y]
    (g : X → Y) (weight : Y → Complex) (A E : Nat)
    (hfiber : ∀ y : Y,
      (Finset.univ.filter fun x : X ↦ g x = y).card ≤ A + E)
    (hcard : Fintype.card X = Fintype.card Y * A)
    (hmean : ∑ y : Y, weight y = 0)
    (hweight : ∀ y : Y, ‖weight y‖ ≤ 1) :
    ‖∑ x : X, weight (g x)‖ ≤ (Fintype.card Y * E : Nat) := by
  classical
  let N : Y → Nat := fun y ↦
    (Finset.univ.filter fun x : X ↦ g x = y).card
  have hN (y : Y) : N y ≤ A + E := hfiber y
  have hNsum : ∑ y : Y, N y = Fintype.card X := by
    have hpartition := Finset.card_eq_sum_card_fiberwise
      (s := (Finset.univ : Finset X)) (t := (Finset.univ : Finset Y))
      (f := g) (by intro x hx; simp)
    simpa only [Finset.card_univ, N] using hpartition.symm
  have hdefsum : ∑ y : Y, (A + E - N y) = Fintype.card Y * E := by
    rw [Finset.sum_tsub_distrib]
    · have hconst :
          (∑ _y : Y, (A + E)) = Fintype.card Y * (A + E) := by simp
      rw [hconst, hNsum, hcard]
      calc
        Fintype.card Y * (A + E) - Fintype.card Y * A =
            Fintype.card Y * (A + E - A) :=
          (Nat.mul_sub_left_distrib _ _ _).symm
        _ = Fintype.card Y * E := by simp
    · intro y hy
      exact hN y
  have hgroup :
      (∑ x : X, weight (g x)) =
        ∑ y : Y, (N y : Complex) * weight y := by
    rw [← Finset.sum_fiberwise' (Finset.univ : Finset X) g weight]
    apply Finset.sum_congr rfl
    intro y hy
    simp only [Finset.sum_const, nsmul_eq_mul, N]
  have hrecenter :
      (∑ y : Y, (N y : Complex) * weight y) =
        -∑ y : Y, ((A + E - N y : Nat) : Complex) * weight y := by
    calc
      (∑ y : Y, (N y : Complex) * weight y) =
          ∑ y : Y, (
            ((A + E : Nat) : Complex) * weight y -
              ((A + E - N y : Nat) : Complex) * weight y) := by
        apply Finset.sum_congr rfl
        intro y hy
        rw [Nat.cast_sub (hN y)]
        ring
      _ = ((A + E : Nat) : Complex) * (∑ y : Y, weight y) -
          ∑ y : Y,
            ((A + E - N y : Nat) : Complex) * weight y := by
        rw [Finset.sum_sub_distrib, Finset.mul_sum]
      _ = -∑ y : Y,
          ((A + E - N y : Nat) : Complex) * weight y := by
        rw [hmean]
        simp
  rw [hgroup, hrecenter, norm_neg]
  calc
    ‖∑ y : Y, ((A + E - N y : Nat) : Complex) * weight y‖ ≤
        ∑ y : Y,
          ‖((A + E - N y : Nat) : Complex) * weight y‖ :=
      norm_sum_le _ _
    _ ≤ ∑ y : Y, ((A + E - N y : Nat) : Real) := by
      apply Finset.sum_le_sum
      intro y hy
      rw [norm_mul, Complex.norm_natCast]
      simpa using mul_le_mul_of_nonneg_left (hweight y)
        (Nat.cast_nonneg (A + E - N y))
    _ = (Fintype.card Y * E : Nat) := by
      exact_mod_cast hdefsum

end Waring.Analytic

end

/-! ## ErdosProblems.Erdos387.RationalStepanovExtensionSum -/

noncomputable section

namespace Erdos387

open scoped BigOperators

namespace RationalStepanov

theorem isMappedPole_iff_mem_image
    {p : ℕ} [NeZero p]
    {E : Type*} [Field E] [DecidableEq E] [Algebra (ZMod p) E]
    (coeff : ZMod p → ZMod p) (x : E) :
    RationalWeil.IsMappedPole coeff x ↔
      x ∈ (InverseRational.poleSupport coeff).image
        (algebraMap (ZMod p) E) := by
  constructor
  · rintro ⟨r, hr, rfl⟩
    exact Finset.mem_image.mpr ⟨r, hr, rfl⟩
  · intro hx
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hx
    exact ⟨r, hr, rfl⟩

theorem norm_extension_zeroExtendedTraceWeight_le
    {p : ℕ} [NeZero p] [Fact p.Prime] (hp : 1 < p)
    (coeff : ZMod p → ZMod p)
    (hne : (InverseRational.poleSupport coeff).Nonempty)
    (hs : (InverseRational.poleSupport coeff).card < p)
    (h : ℕ) :
    let E := FiniteField.Extension (ZMod p) p (2 * (h + 3))
    letI : Fintype E := Fintype.ofFinite E
    ‖∑ x : E, RationalWeil.zeroExtendedTraceWeight coeff x‖ ≤
      ((p * (p ^ (h + 3) + p ^ 2 *
          rationalPhaseAllowance p h
            (InverseRational.poleSupport coeff).card +
          (InverseRational.poleSupport coeff).card) +
        (InverseRational.poleSupport coeff).card : ℕ) : ℝ) := by
  classical
  let E := FiniteField.Extension (ZMod p) p (2 * (h + 3))
  let : CharP E p :=
    (Algebra.charP_iff (ZMod p) E p).mp (ZMod.charP p)
  let : Fintype E := Fintype.ofFinite E
  let phaseTrace : E → ZMod p := fun x =>
    Algebra.trace (ZMod p) E
      (RationalWeil.mappedSimplePolePhase coeff x)
  let poles : Finset E :=
    (InverseRational.poleSupport coeff).image (algebraMap (ZMod p) E)
  let average : ℕ := p ^ (2 * (h + 3) - 1)
  let error : ℕ := p ^ (h + 3) + p ^ 2 *
      rationalPhaseAllowance p h
        (InverseRational.poleSupport coeff).card +
      (InverseRational.poleSupport coeff).card
  have hpolesCard : poles.card =
      (InverseRational.poleSupport coeff).card := by
    exact Finset.card_image_of_injective _
      (algebraMap (ZMod p) E).injective
  have hfiber (c : ZMod p) :
      (Finset.univ.filter fun x : E => phaseTrace x = c).card ≤
        average + error := by
    let fullFiber : Finset E :=
      Finset.univ.filter fun x : E => phaseTrace x = c
    have hsubset : fullFiber ⊆ nonpoleTraceFiber coeff c ∪ poles := by
      intro x hx
      have hxc : phaseTrace x = c := (Finset.mem_filter.mp hx).2
      by_cases hxpole : RationalWeil.IsMappedPole coeff x
      · exact Finset.mem_union_right _ <|
          (isMappedPole_iff_mem_image coeff x).mp hxpole
      · apply Finset.mem_union_left
        simp only [nonpoleTraceFiber, Finset.mem_filter, Finset.mem_univ,
          true_and]
        exact ⟨hxpole, hxc⟩
    have hnonpole := card_nonpole_trace_fiber_le
      hp coeff hne hs h c
    change fullFiber.card ≤ average + error
    calc
      fullFiber.card ≤ (nonpoleTraceFiber coeff c ∪ poles).card :=
        Finset.card_le_card hsubset
      _ ≤ (nonpoleTraceFiber coeff c).card + poles.card :=
        Finset.card_union_le _ _
      _ ≤ rationalTraceFiberBound p h
          (InverseRational.poleSupport coeff).card + poles.card :=
        Nat.add_le_add_right hnonpole _
      _ = average + error := by
        rw [hpolesCard]
        unfold rationalTraceFiberBound average error
        omega
  have hcardE : Fintype.card E = p ^ (2 * (h + 3)) := by
    rw [Fintype.card_eq_nat_card]
    change Nat.card
      (FiniteField.Extension (ZMod p) p (2 * (h + 3))) = _
    rw [FiniteField.natCard_extension, Nat.card_zmod]
  have hcard : Fintype.card E = Fintype.card (ZMod p) * average := by
    rw [hcardE, ZMod.card]
    unfold average
    calc
      p ^ (2 * (h + 3)) = p ^ ((2 * (h + 3) - 1) + 1) := by
        congr 1
      _ = p ^ (2 * (h + 3) - 1) * p := by rw [pow_add, pow_one]
      _ = p * p ^ (2 * (h + 3) - 1) := Nat.mul_comm _ _
  have hcharNe : (ZMod.stdAddChar : AddChar (ZMod p) ℂ) ≠ 1 := by
    intro htrivial
    have hprimitive := ZMod.isPrimitive_stdAddChar p
    have hshift := hprimitive (a := 1) one_ne_zero
    rw [AddChar.mulShift_one, htrivial] at hshift
    exact hshift rfl
  have hmean : ∑ c : ZMod p, ZMod.stdAddChar c = 0 :=
    AddChar.sum_eq_zero_of_ne_one hcharNe
  have hweight (c : ZMod p) : ‖ZMod.stdAddChar c‖ ≤ 1 := by
    rw [Waring.Analytic.norm_stdAddChar]
  have hfull : ‖∑ x : E, ZMod.stdAddChar (phaseTrace x)‖ ≤
      (p * error : ℕ) := by
    have hcore := Waring.Analytic.norm_fintype_sum_comp_le_of_card_fiber_le
      phaseTrace (fun c : ZMod p => ZMod.stdAddChar c)
      average error hfiber hcard hmean hweight
    simpa only [ZMod.card] using hcore
  have hpoleIff (x : E) :
      RationalWeil.IsMappedPole coeff x ↔ x ∈ poles := by
    exact isMappedPole_iff_mem_image coeff x
  have hidentity :
      (∑ x : E, RationalWeil.zeroExtendedTraceWeight coeff x) =
        (∑ x : E, ZMod.stdAddChar (phaseTrace x)) -
          ∑ x ∈ poles, ZMod.stdAddChar (phaseTrace x) := by
    calc
      (∑ x : E, RationalWeil.zeroExtendedTraceWeight coeff x) =
          ∑ x : E, (ZMod.stdAddChar (phaseTrace x) -
            if x ∈ poles then ZMod.stdAddChar (phaseTrace x) else 0) := by
        apply Finset.sum_congr rfl
        intro x hx
        by_cases hxpole : RationalWeil.IsMappedPole coeff x
        · simp [RationalWeil.zeroExtendedTraceWeight, hxpole,
            (hpoleIff x).mp hxpole]
        · have hxnotmem : x ∉ poles := fun hxmem =>
            hxpole ((hpoleIff x).mpr hxmem)
          simp [RationalWeil.zeroExtendedTraceWeight, hxpole,
            hxnotmem, phaseTrace]
      _ = (∑ x : E, ZMod.stdAddChar (phaseTrace x)) -
          ∑ x : E,
            if x ∈ poles then ZMod.stdAddChar (phaseTrace x) else 0 := by
        rw [Finset.sum_sub_distrib]
      _ = (∑ x : E, ZMod.stdAddChar (phaseTrace x)) -
          ∑ x ∈ poles, ZMod.stdAddChar (phaseTrace x) := by
        congr 1
        simp
  have hpoleSum : ‖∑ x ∈ poles, ZMod.stdAddChar (phaseTrace x)‖ ≤
      ((InverseRational.poleSupport coeff).card : ℕ) := by
    calc
      ‖∑ x ∈ poles, ZMod.stdAddChar (phaseTrace x)‖ ≤
          ∑ x ∈ poles, ‖ZMod.stdAddChar (phaseTrace x)‖ :=
        norm_sum_le _ _
      _ = ∑ _x ∈ poles, (1 : ℝ) := by
        apply Finset.sum_congr rfl
        intro x hx
        rw [Waring.Analytic.norm_stdAddChar]
      _ = poles.card := by simp
      _ = (InverseRational.poleSupport coeff).card := by rw [hpolesCard]
  dsimp only
  rw [hidentity]
  calc
    ‖(∑ x : E, ZMod.stdAddChar (phaseTrace x)) -
        ∑ x ∈ poles, ZMod.stdAddChar (phaseTrace x)‖ ≤
        ‖∑ x : E, ZMod.stdAddChar (phaseTrace x)‖ +
          ‖∑ x ∈ poles, ZMod.stdAddChar (phaseTrace x)‖ :=
      norm_sub_le _ _
    _ ≤ (p * error : ℕ) +
        (InverseRational.poleSupport coeff).card :=
      add_le_add hfull hpoleSum
    _ = ((p * (p ^ (h + 3) + p ^ 2 *
          rationalPhaseAllowance p h
            (InverseRational.poleSupport coeff).card +
          (InverseRational.poleSupport coeff).card) +
        (InverseRational.poleSupport coeff).card : ℕ) : ℝ) := by
      simp [error]

theorem hasEvenExtensionSquareRootBound
    {p : ℕ} [NeZero p] [Fact p.Prime] (hp : 1 < p)
    (coeff : ZMod p → ZMod p)
    (hne : (InverseRational.poleSupport coeff).Nonempty)
    (hs : (InverseRational.poleSupport coeff).card < p) :
    RationalWeil.HasEvenExtensionSquareRootBound coeff := by
  let s := (InverseRational.poleSupport coeff).card
  let Cnat := p * (1 + p ^ 2 * ((p - 1) * s) + s) + s
  refine ⟨(Cnat : ℝ), ?_⟩
  intro m hm
  let : NeZero (2 * m) := ⟨by omega⟩
  let E := FiniteField.Extension (ZMod p) p (2 * m)
  let : Fintype E := Fintype.ofFinite E
  let h := m - 3
  have hh : h + 3 = m := by omega
  have hstep := norm_extension_zeroExtendedTraceWeight_le
    hp coeff hne hs h
  dsimp only at hstep ⊢
  rw [hh] at hstep
  refine hstep.trans ?_
  have hp0 : 0 < p := by omega
  have hpowOne : 1 ≤ p ^ m := one_le_pow₀ (by omega : 1 ≤ p)
  have hgeomIdentity := pred_mul_frobeniusOrderSum_add_one
    (p := p) (m := m) hp0
  have hgeom : frobeniusOrderSum p m ≤ p ^ m := by
    have hpred : 1 ≤ p - 1 := by omega
    calc
      frobeniusOrderSum p m ≤
          (p - 1) * frobeniusOrderSum p m := by
        nlinarith
      _ ≤ (p - 1) * frobeniusOrderSum p m + 1 := Nat.le_add_right _ _
      _ = p ^ m := hgeomIdentity
  have hallow : rationalPhaseAllowance p h s ≤
      ((p - 1) * s) * p ^ m := by
    unfold rationalPhaseAllowance
    rw [hh]
    exact Nat.mul_le_mul_left ((p - 1) * s) hgeom
  have hsPow : s ≤ s * p ^ m := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left s hpowOne
  have hinside :
      p ^ m + p ^ 2 * rationalPhaseAllowance p h s + s ≤
        (1 + p ^ 2 * ((p - 1) * s) + s) * p ^ m := by
    calc
      p ^ m + p ^ 2 * rationalPhaseAllowance p h s + s ≤
          p ^ m + p ^ 2 * (((p - 1) * s) * p ^ m) + s * p ^ m :=
        Nat.add_le_add (Nat.add_le_add_left
          (Nat.mul_le_mul_left (p ^ 2) hallow) _) hsPow
      _ = (1 + p ^ 2 * ((p - 1) * s) + s) * p ^ m := by ring
  have hnat :
      p * (p ^ m + p ^ 2 * rationalPhaseAllowance p h s + s) + s ≤
        Cnat * p ^ m := by
    calc
      p * (p ^ m + p ^ 2 * rationalPhaseAllowance p h s + s) + s ≤
          p * ((1 + p ^ 2 * ((p - 1) * s) + s) * p ^ m) +
            s * p ^ m :=
        Nat.add_le_add (Nat.mul_le_mul_left p hinside) hsPow
      _ = Cnat * p ^ m := by unfold Cnat; ring
  norm_cast

theorem norm_zeroExtendedSimplePolePhase_sum_le
    {p : ℕ} [NeZero p] [Fact p.Prime] (hp : 1 < p)
    (coeff : ZMod p → ZMod p)
    (hne : (InverseRational.poleSupport coeff).Nonempty)
    (hs : (InverseRational.poleSupport coeff).card < p) :
    ‖∑ x : ZMod p,
        if x ∈ InverseRational.poleSupport coeff then 0
        else ZMod.stdAddChar (InverseRational.simplePolePhase coeff x)‖ ≤
      ((2 * (InverseRational.poleSupport coeff).card - 1 : ℕ) : ℝ) *
        Real.sqrt (p : ℝ) := by
  exact RationalWeil.norm_zeroExtendedSimplePolePhase_sum_le_of_evenExtensionBound
    coeff hne (hasEvenExtensionSquareRootBound hp coeff hne hs)

end RationalStepanov

end Erdos387

end

/-! ## ErdosProblems.Erdos387.PrimeKloostermanBound -/

noncomputable section

namespace Erdos387

open scoped BigOperators

namespace Kloosterman

noncomputable def mobiusForward
    {p : ℕ} [NeZero p] (t : ZMod p) : ZMod p :=
  t * (t + 1)⁻¹

noncomputable def mobiusInverse
    {p : ℕ} [NeZero p] (x : ZMod p) : ZMod p :=
  x * (1 - x)⁻¹

theorem mobiusForward_ne_zero
    {p : ℕ} [NeZero p] [Fact p.Prime] {t : ZMod p}
    (ht0 : t ≠ 0) (ht1 : t ≠ -1) :
    mobiusForward t ≠ 0 := by
  unfold mobiusForward
  exact mul_ne_zero ht0 (inv_ne_zero (by
    intro h
    exact ht1 (add_eq_zero_iff_eq_neg.mp h)))

theorem mobiusForward_ne_one
    {p : ℕ} [NeZero p] [Fact p.Prime] {t : ZMod p}
    (ht1 : t ≠ -1) :
    mobiusForward t ≠ 1 := by
  have hden : t + 1 ≠ 0 := by
    intro h
    exact ht1 (add_eq_zero_iff_eq_neg.mp h)
  unfold mobiusForward
  intro h
  field_simp [hden] at h
  have hone : (1 : ZMod p) = 0 := by
    simpa using congrArg (fun z : ZMod p => z - t) h.symm
  exact one_ne_zero hone

theorem mobiusInverse_ne_zero
    {p : ℕ} [NeZero p] [Fact p.Prime] {x : ZMod p}
    (hx0 : x ≠ 0) (hx1 : x ≠ 1) :
    mobiusInverse x ≠ 0 := by
  unfold mobiusInverse
  exact mul_ne_zero hx0 (inv_ne_zero (sub_ne_zero.mpr hx1.symm))

theorem mobiusInverse_ne_neg_one
    {p : ℕ} [NeZero p] [Fact p.Prime] {x : ZMod p}
    (hx1 : x ≠ 1) :
    mobiusInverse x ≠ -1 := by
  have hden : 1 - x ≠ 0 := sub_ne_zero.mpr hx1.symm
  unfold mobiusInverse
  intro h
  field_simp [hden] at h
  have hneg : -x = 1 - x := by
    simpa using congrArg Neg.neg h
  have hone : (1 : ZMod p) = 0 := by
    calc
      1 = (1 - x) + x := by ring
      _ = -x + x := by rw [← hneg]
      _ = 0 := neg_add_cancel x
  exact one_ne_zero hone

theorem mobiusInverse_forward
    {p : ℕ} [NeZero p] [Fact p.Prime] {t : ZMod p}
    (ht1 : t ≠ -1) :
    mobiusInverse (mobiusForward t) = t := by
  have hden : t + 1 ≠ 0 := by
    intro h
    exact ht1 (add_eq_zero_iff_eq_neg.mp h)
  unfold mobiusInverse mobiusForward
  field_simp [hden]
  ring

theorem mobiusForward_inverse
    {p : ℕ} [NeZero p] [Fact p.Prime] {x : ZMod p}
    (hx1 : x ≠ 1) :
    mobiusForward (mobiusInverse x) = x := by
  have hden : 1 - x ≠ 0 := sub_ne_zero.mpr hx1.symm
  unfold mobiusInverse mobiusForward
  field_simp [hden]
  ring

def twoPoleCoefficient
    {p : ℕ} [NeZero p] (a b r : ZMod p) : ZMod p :=
  if r = 0 then b else if r = -1 then -a else 0

theorem poleSupport_twoPoleCoefficient
    {p : ℕ} [NeZero p] [Fact p.Prime] {a b : ZMod p}
    (ha : a ≠ 0) (hb : b ≠ 0) :
    InverseRational.poleSupport (twoPoleCoefficient a b) = {0, -1} := by
  classical
  ext r
  simp only [InverseRational.mem_poleSupport, Finset.mem_insert,
    Finset.mem_singleton]
  unfold twoPoleCoefficient
  by_cases hr0 : r = 0
  · simp [hr0, hb]
  · by_cases hr1 : r = -1
    · simp [hr1, ha]
    · simp [hr0, hr1]

theorem simplePolePhase_twoPoleCoefficient
    {p : ℕ} [NeZero p] [Fact p.Prime] {a b : ZMod p}
    (ha : a ≠ 0) (hb : b ≠ 0) (t : ZMod p) :
    InverseRational.simplePolePhase (twoPoleCoefficient a b) t =
      b * t⁻¹ - a * (t + 1)⁻¹ := by
  rw [InverseRational.simplePolePhase_eq_sum_poleSupport,
    poleSupport_twoPoleCoefficient ha hb]
  have hneg : (-1 : ZMod p) ≠ 0 := neg_ne_zero.mpr one_ne_zero
  simp [twoPoleCoefficient, hneg]
  ring

theorem kloostermanPhase_mobiusForward
    {p : ℕ} [NeZero p] [Fact p.Prime] {a b t : ZMod p}
    (ha : a ≠ 0) (hb : b ≠ 0) (ht0 : t ≠ 0) (ht1 : t ≠ -1) :
    a * mobiusForward t + b * (mobiusForward t)⁻¹ =
      a + b + InverseRational.simplePolePhase
        (twoPoleCoefficient a b) t := by
  have hden : t + 1 ≠ 0 := by
    intro h
    exact ht1 (add_eq_zero_iff_eq_neg.mp h)
  rw [simplePolePhase_twoPoleCoefficient ha hb]
  unfold mobiusForward
  field_simp [ht0, hden]
  ring

noncomputable def mobiusDomain
    (p : ℕ) [NeZero p] : Finset (ZMod p) := by
  classical
  exact Finset.univ.filter fun t => t ≠ 0 ∧ t ≠ -1

noncomputable def mobiusCodomain
    (p : ℕ) [NeZero p] : Finset (ZMod p) := by
  classical
  exact Finset.univ.filter fun x => x ≠ 0 ∧ x ≠ 1

theorem sum_mobiusForward
    {p : ℕ} [NeZero p] [Fact p.Prime] (f : ZMod p → ℂ) :
    (∑ t ∈ mobiusDomain p, f (mobiusForward t)) =
      ∑ x ∈ mobiusCodomain p, f x := by
  classical
  apply Finset.sum_bij (fun t _ht => mobiusForward t)
  · intro t ht
    rw [mobiusDomain, Finset.mem_filter] at ht
    rw [mobiusCodomain, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, mobiusForward_ne_zero ht.2.1 ht.2.2,
      mobiusForward_ne_one ht.2.2⟩
  · intro t ht u hu htu
    rw [mobiusDomain, Finset.mem_filter] at ht hu
    have h := congrArg mobiusInverse htu
    simpa [mobiusInverse_forward ht.2.2,
      mobiusInverse_forward hu.2.2] using h
  · intro x hx
    rw [mobiusCodomain, Finset.mem_filter] at hx
    refine ⟨mobiusInverse x, ?_, ?_⟩
    · rw [mobiusDomain, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, mobiusInverse_ne_zero hx.2.1 hx.2.2,
        mobiusInverse_ne_neg_one hx.2.2⟩
    · exact mobiusForward_inverse hx.2.2
  · intro t ht
    rfl

theorem zeroExtendedTwoPoleSum_eq_domain
    {p : ℕ} [NeZero p] [Fact p.Prime] {a b : ZMod p}
    (ha : a ≠ 0) (hb : b ≠ 0) :
    (∑ t : ZMod p,
        if t ∈ InverseRational.poleSupport (twoPoleCoefficient a b) then 0
        else ZMod.stdAddChar
          (InverseRational.simplePolePhase (twoPoleCoefficient a b) t)) =
      ∑ t ∈ mobiusDomain p,
        ZMod.stdAddChar
          (InverseRational.simplePolePhase (twoPoleCoefficient a b) t) := by
  classical
  rw [poleSupport_twoPoleCoefficient ha hb]
  rw [mobiusDomain, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro t _ht
  by_cases ht0 : t = 0 <;> by_cases ht1 : t = -1 <;>
    simp [ht0, ht1]

theorem sum_eq_one_add_codomain
    {p : ℕ} [NeZero p] [Fact p.Prime] (a b : ZMod p) :
    sum p a b =
      ZMod.stdAddChar (a + b) +
        ∑ x ∈ mobiusCodomain p,
          ZMod.stdAddChar (a * x + b * x⁻¹) := by
  classical
  rw [sum_eq_inverse_phase]
  let U := (Finset.univ : Finset (ZMod p)).filter IsUnit
  have hUone : (1 : ZMod p) ∈ U := by simp [U]
  calc
    (∑ x : ZMod p,
        if IsUnit x then ZMod.stdAddChar (a * x + b * x⁻¹) else 0) =
      ∑ x ∈ U, ZMod.stdAddChar (a * x + b * x⁻¹) := by
        rw [Finset.sum_filter]
    _ = ZMod.stdAddChar (a + b) +
        ∑ x ∈ U.erase 1, ZMod.stdAddChar (a * x + b * x⁻¹) := by
      rw [← Finset.add_sum_erase U
        (fun x => ZMod.stdAddChar (a * x + b * x⁻¹)) hUone]
      simp
    _ = ZMod.stdAddChar (a + b) +
        ∑ x ∈ mobiusCodomain p,
          ZMod.stdAddChar (a * x + b * x⁻¹) := by
      congr 1
      apply Finset.sum_congr
      · ext x
        simp [U, mobiusCodomain, isUnit_iff_ne_zero, and_comm]
      · intro x hx
        rfl

theorem sum_eq_const_mul_one_add_twoPole
    {p : ℕ} [NeZero p] [Fact p.Prime] {a b : ZMod p}
    (ha : a ≠ 0) (hb : b ≠ 0) :
    sum p a b =
      ZMod.stdAddChar (a + b) *
        (1 + ∑ t : ZMod p,
          if t ∈ InverseRational.poleSupport
              (twoPoleCoefficient a b) then 0
          else ZMod.stdAddChar
            (InverseRational.simplePolePhase
              (twoPoleCoefficient a b) t)) := by
  rw [sum_eq_one_add_codomain]
  let R := ∑ t : ZMod p,
    if t ∈ InverseRational.poleSupport (twoPoleCoefficient a b) then 0
    else ZMod.stdAddChar
      (InverseRational.simplePolePhase (twoPoleCoefficient a b) t)
  have hcodomain :
      (∑ x ∈ mobiusCodomain p,
          ZMod.stdAddChar (a * x + b * x⁻¹)) =
        ZMod.stdAddChar (a + b) * R := by
    calc
      (∑ x ∈ mobiusCodomain p,
          ZMod.stdAddChar (a * x + b * x⁻¹)) =
        ∑ t ∈ mobiusDomain p,
          ZMod.stdAddChar
            (a * mobiusForward t + b * (mobiusForward t)⁻¹) :=
          (sum_mobiusForward
            (fun x => ZMod.stdAddChar (a * x + b * x⁻¹))).symm
      _ = ∑ t ∈ mobiusDomain p,
          ZMod.stdAddChar
            (a + b + InverseRational.simplePolePhase
              (twoPoleCoefficient a b) t) := by
        apply Finset.sum_congr rfl
        intro t ht
        rw [mobiusDomain, Finset.mem_filter] at ht
        rw [kloostermanPhase_mobiusForward ha hb ht.2.1 ht.2.2]
      _ = ∑ t ∈ mobiusDomain p,
          ZMod.stdAddChar (a + b) *
            ZMod.stdAddChar
              (InverseRational.simplePolePhase
                (twoPoleCoefficient a b) t) := by
        apply Finset.sum_congr rfl
        intro t _ht
        rw [AddChar.map_add_eq_mul]
      _ = ZMod.stdAddChar (a + b) *
          ∑ t ∈ mobiusDomain p,
            ZMod.stdAddChar
              (InverseRational.simplePolePhase
                (twoPoleCoefficient a b) t) := by
        rw [Finset.mul_sum]
      _ = ZMod.stdAddChar (a + b) * R := by
        rw [← zeroExtendedTwoPoleSum_eq_domain ha hb]
  rw [hcodomain]
  ring

theorem norm_sum_le_three_sqrt_add_one
    {p : ℕ} [NeZero p] [Fact p.Prime] (hp : 2 < p)
    {a b : ZMod p} (ha : a ≠ 0) (hb : b ≠ 0) :
    ‖sum p a b‖ ≤ 3 * Real.sqrt (p : ℝ) + 1 := by
  let coeff := twoPoleCoefficient a b
  let support := InverseRational.poleSupport coeff
  have hsupport : support = {0, -1} := by
    simpa only [support, coeff] using poleSupport_twoPoleCoefficient ha hb
  have hneg : (-1 : ZMod p) ≠ 0 := neg_ne_zero.mpr one_ne_zero
  have hnonempty : support.Nonempty := by
    rw [hsupport]
    simp
  have hcard : support.card < p := by
    rw [hsupport]
    simp
    omega
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
  have hweil :
      ‖∑ t : ZMod p,
          if t ∈ support then 0
          else ZMod.stdAddChar
            (InverseRational.simplePolePhase coeff t)‖ ≤
        ((2 * support.card - 1 : ℕ) : ℝ) * Real.sqrt (p : ℝ) := by
    simpa only [support] using
      RationalStepanov.norm_zeroExtendedSimplePolePhase_sum_le
        hp1 coeff hnonempty hcard
  have hsupportCard : support.card = 2 := by
    rw [hsupport]
    simp
  have hweil' :
      ‖∑ t : ZMod p,
          if t ∈ support then 0
          else ZMod.stdAddChar
            (InverseRational.simplePolePhase coeff t)‖ ≤
        3 * Real.sqrt (p : ℝ) := by
    rw [hsupportCard] at hweil
    norm_num at hweil
    exact hweil
  rw [sum_eq_const_mul_one_add_twoPole ha hb, norm_mul,
    AddChar.norm_apply, one_mul]
  calc
    ‖1 + ∑ t : ZMod p,
        if t ∈ InverseRational.poleSupport
            (twoPoleCoefficient a b) then 0
        else ZMod.stdAddChar
          (InverseRational.simplePolePhase
            (twoPoleCoefficient a b) t)‖ ≤
      1 + ‖∑ t : ZMod p,
        if t ∈ InverseRational.poleSupport
            (twoPoleCoefficient a b) then 0
        else ZMod.stdAddChar
          (InverseRational.simplePolePhase
            (twoPoleCoefficient a b) t)‖ := by
        simpa using norm_add_le (1 : ℂ)
          (∑ t : ZMod p,
            if t ∈ InverseRational.poleSupport
                (twoPoleCoefficient a b) then 0
            else ZMod.stdAddChar
              (InverseRational.simplePolePhase
                (twoPoleCoefficient a b) t))
    _ ≤ 1 + 3 * Real.sqrt (p : ℝ) := by
      have hweil'' :
          ‖∑ t : ZMod p,
              if t ∈ InverseRational.poleSupport
                  (twoPoleCoefficient a b) then 0
              else ZMod.stdAddChar
                (InverseRational.simplePolePhase
                  (twoPoleCoefficient a b) t)‖ ≤
            3 * Real.sqrt (p : ℝ) := by
        simpa only [support, coeff] using hweil'
      exact add_le_add_right hweil'' 1
    _ = 3 * Real.sqrt (p : ℝ) + 1 := by ring

end Kloosterman

end Erdos387

end


namespace OMA.Heil

open Finset

variable {p : ℕ} [Fact p.Prime]

noncomputable abbrev ψ (p : ℕ) [Fact p.Prime] : AddChar (ZMod p) ℂ :=
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  ZMod.stdAddChar

lemma prim : (ψ p).IsPrimitive := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  exact ZMod.isPrimitive_stdAddChar p

lemma orth (b : ZMod p) : ∑ x : ZMod p, ψ p (x * b) = if b = 0 then (p : ℂ) else 0 := by
  rw [AddChar.sum_mulShift b prim, ZMod.card]
  split_ifs <;> simp

lemma orth' (b : ZMod p) : ∑ x : ZMod p, ψ p (b * x) = if b = 0 then (p : ℂ) else 0 := by
  simp_rw [mul_comm b]; exact orth b

noncomputable def K (a b : ZMod p) : ℂ := ∑ x : ZMod p, ψ p (a * x + b * x⁻¹)

lemma K_zero_zero : K (p := p) 0 0 = p := by
  simp [K, ZMod.card]

lemma K_zero_left (b : ZMod p) (hb : b ≠ 0) : K 0 b = 0 := by
  unfold K
  simp only [zero_mul, zero_add]
  rw [show (∑ x : ZMod p, ψ p (b * x⁻¹)) = ∑ x : ZMod p, ψ p (b * x) from
    Fintype.sum_equiv (Equiv.inv (ZMod p)) _ _ (fun x => rfl)]
  rw [orth', if_neg hb]

lemma K_zero_right (a : ZMod p) (ha : a ≠ 0) : K a 0 = 0 := by
  unfold K
  simp only [zero_mul, add_zero]
  rw [orth', if_neg ha]

noncomputable def B (p : ℕ) : ℝ := 3 * Real.sqrt p + 2

lemma B_nonneg : 0 ≤ B p := by unfold B; positivity

lemma K'_le (hodd : 2 < p) (a b : ZMod p) :
    ‖K a b - (if a = 0 ∧ b = 0 then (p : ℂ) else 0)‖ ≤ B p := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  by_cases ha : a = 0
  · by_cases hb : b = 0
    · subst a; subst b; simp [K_zero_zero, B_nonneg]
    · subst a; simp [K_zero_left b hb, hb, B_nonneg]
  · by_cases hb : b = 0
    · subst b; simp [K_zero_right a ha, ha, B_nonneg]
    simp only [ha, false_and, if_false, sub_zero]
    have hsum : K a b = Erdos387.Kloosterman.sum p a b + 1 := by
      rw [Erdos387.Kloosterman.sum_eq_inverse_phase]
      unfold K
      have term (x : ZMod p) : ψ p (a*x+b*x⁻¹) =
          (if IsUnit x then ZMod.stdAddChar (a*x+b*x⁻¹) else 0) +
          (if x = 0 then 1 else 0) := by
        by_cases hx : x = 0
        · subst x; simp
        · simp [isUnit_iff_ne_zero, hx, ψ]
      calc
        _ = ∑ x : ZMod p, ((if IsUnit x then ZMod.stdAddChar (a*x+b*x⁻¹) else 0) +
              (if x = 0 then 1 else 0)) := Finset.sum_congr rfl (fun x _ => term x)
        _ = _ := by simp [Finset.sum_add_distrib]
    rw [hsum]
    calc
      _ ≤ ‖Erdos387.Kloosterman.sum p a b‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
      _ ≤ B p := by
        have h := Erdos387.Kloosterman.norm_sum_le_three_sqrt_add_one hodd ha hb
        rw [norm_one]; unfold B; linarith

lemma swap3 {α β γ M : Type*} [AddCommMonoid M] (s : Finset α) (t : Finset β) (u : Finset γ)
    (f : α → β → γ → M) :
    ∑ a ∈ s, ∑ b ∈ t, ∑ c ∈ u, f a b c = ∑ b ∈ t, ∑ c ∈ u, ∑ a ∈ s, f a b c := by
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun _ _ => Finset.sum_comm)

lemma ind_eq (y x : ZMod p) :
    (p : ℂ) * (if y = x then (1 : ℂ) else 0) = ∑ k : ZMod p, ψ p (k * (y - x)) := by
  rw [orth]
  simp only [sub_eq_zero]
  split_ifs <;> simp

/-- the index set -/
def D (L : ℕ) : Finset (ℕ × ℕ) := Finset.range L ×ˢ Finset.range L

/-- the residue attached to an index -/
def aD (p n : ℕ) (d : ℕ × ℕ) : ZMod p := ((n + 1 + d.1 + d.2 : ℕ) : ZMod p)

/-- Fourier transform of the weight -/
noncomputable def W (n L : ℕ) (k : ZMod p) : ℂ := ∑ d ∈ D L, ψ p (k * aD p n d)

/-- the count of inverse pairs -/
noncomputable def Qn (p : ℕ) [Fact p.Prime] (n L : ℕ) : ℕ :=
  ∑ d ∈ D L, ∑ e ∈ D L, ∑ x : ZMod p, if aD p n d = x ∧ aD p n e = x⁻¹ then 1 else 0

lemma count_identity (n L : ℕ) :
    (p : ℂ) ^ 2 * (Qn p n L : ℂ) =
      ∑ k : ZMod p, ∑ h : ZMod p, W n L k * W n L h * K (-k) (-h) := by
  have lhs : (p : ℂ) ^ 2 * (Qn p n L : ℂ) =
      ∑ d ∈ D L, ∑ e ∈ D L, ∑ x : ZMod p, ∑ k : ZMod p, ∑ h : ZMod p,
        ψ p (k * aD p n d) * ψ p (h * aD p n e) * ψ p (-k * x + -h * x⁻¹) := by
    unfold Qn
    push_cast
    simp_rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun d _ => Finset.sum_congr rfl (fun e _ =>
      Finset.sum_congr rfl (fun x _ => ?_)))
    have e1 : (p : ℂ) ^ 2 * (if aD p n d = x ∧ aD p n e = x⁻¹ then (1 : ℂ) else 0) =
        ((p : ℂ) * (if aD p n d = x then (1 : ℂ) else 0)) *
        ((p : ℂ) * (if aD p n e = x⁻¹ then (1 : ℂ) else 0)) := by
      split_ifs <;> simp_all <;> ring
    rw [e1, ind_eq, ind_eq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun h _ => ?_))
    rw [← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
    congr 1
    ring
  rw [lhs]
  have rhs : ∑ k : ZMod p, ∑ h : ZMod p, W n L k * W n L h * K (-k) (-h) =
      ∑ k : ZMod p, ∑ h : ZMod p, ∑ d ∈ D L, ∑ e ∈ D L, ∑ x : ZMod p,
        ψ p (k * aD p n d) * ψ p (h * aD p n e) * ψ p (-k * x + -h * x⁻¹) := by
    unfold W K
    refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun h _ => ?_))
    rw [Finset.sum_mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun d _ => ?_)
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun e _ => ?_)
    rw [Finset.mul_sum]
  rw [rhs]
  calc ∑ d ∈ D L, ∑ e ∈ D L, ∑ x : ZMod p, ∑ k : ZMod p, ∑ h : ZMod p,
        ψ p (k * aD p n d) * ψ p (h * aD p n e) * ψ p (-k * x + -h * x⁻¹)
      = ∑ d ∈ D L, ∑ e ∈ D L, ∑ k : ZMod p, ∑ h : ZMod p, ∑ x : ZMod p,
        ψ p (k * aD p n d) * ψ p (h * aD p n e) * ψ p (-k * x + -h * x⁻¹) :=
        Finset.sum_congr rfl (fun d _ => Finset.sum_congr rfl (fun e _ =>
          swap3 _ _ _ (fun x k h => ψ p (k * aD p n d) * ψ p (h * aD p n e) *
            ψ p (-k * x + -h * x⁻¹))))
    _ = ∑ d ∈ D L, ∑ k : ZMod p, ∑ h : ZMod p, ∑ e ∈ D L, ∑ x : ZMod p,
        ψ p (k * aD p n d) * ψ p (h * aD p n e) * ψ p (-k * x + -h * x⁻¹) :=
        Finset.sum_congr rfl (fun d _ =>
          swap3 _ _ _ (fun e k h => ∑ x : ZMod p, ψ p (k * aD p n d) * ψ p (h * aD p n e) *
            ψ p (-k * x + -h * x⁻¹)))
    _ = _ := swap3 _ _ _ (fun d k h => ∑ e ∈ D L, ∑ x : ZMod p, ψ p (k * aD p n d) *
            ψ p (h * aD p n e) * ψ p (-k * x + -h * x⁻¹))

/-- the interval exponential sum -/
noncomputable def S (L : ℕ) (k : ZMod p) : ℂ := ∑ u ∈ Finset.range L, ψ p (k * (u : ZMod p))

lemma W_eq (n L : ℕ) (k : ZMod p) :
    W n L k = ψ p (k * ((n + 1 : ℕ) : ZMod p)) * S L k * S L k := by
  unfold W D S
  rw [Finset.sum_product, mul_assoc, Finset.sum_mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun u _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun v _ => ?_)
  rw [← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
  congr 1
  simp only [aD]
  push_cast
  ring

lemma norm_W (n L : ℕ) (k : ZMod p) : ‖W n L k‖ = ‖S L k‖ ^ 2 := by
  rw [W_eq, norm_mul, norm_mul, AddChar.norm_apply, one_mul, sq]

lemma parseval (L : ℕ) (hL : L ≤ p) : ∑ k : ZMod p, ‖S L k‖ ^ 2 = (p : ℝ) * L := by
  apply Complex.ofReal_injective
  push_cast
  have e : ∀ k : ZMod p, ((‖S L k‖ ^ 2 : ℝ) : ℂ) =
      ∑ u ∈ Finset.range L, ∑ v ∈ Finset.range L, ψ p (k * ((u : ZMod p) - (v : ZMod p))) := by
    intro k
    rw [← Complex.normSq_eq_norm_sq, ← Complex.mul_conj, S, map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl (fun u _ => Finset.sum_congr rfl (fun v _ => ?_))
    rw [← AddChar.map_neg_eq_conj, ← AddChar.map_add_eq_mul]
    congr 1
    ring
  have e' : ∀ k : ZMod p, ((‖S L k‖ : ℂ) ^ 2) =
      ∑ u ∈ Finset.range L, ∑ v ∈ Finset.range L, ψ p (k * ((u : ZMod p) - (v : ZMod p))) := by
    intro k
    exact_mod_cast e k
  simp_rw [e']
  rw [show (∑ k : ZMod p, ∑ u ∈ Finset.range L, ∑ v ∈ Finset.range L,
      ψ p (k * ((u : ZMod p) - (v : ZMod p)))) = ∑ u ∈ Finset.range L, ∑ v ∈ Finset.range L,
      ∑ k : ZMod p, ψ p (k * ((u : ZMod p) - (v : ZMod p))) from
    swap3 _ _ _ (fun (k : ZMod p) (u v : ℕ) => ψ p (k * ((u : ZMod p) - (v : ZMod p))))]
  have inner : ∀ u ∈ Finset.range L, ∑ v ∈ Finset.range L, ∑ k : ZMod p,
      ψ p (k * ((u : ZMod p) - (v : ZMod p))) = (p : ℂ) := by
    intro u hu
    simp_rw [orth, sub_eq_zero]
    have hinj : ∀ v ∈ Finset.range L, ((u : ZMod p) = (v : ZMod p) ↔ u = v) := by
      intro v hv
      rw [ZMod.natCast_eq_natCast_iff']
      have hu' : u < p := lt_of_lt_of_le (Finset.mem_range.mp hu) hL
      have hv' : v < p := lt_of_lt_of_le (Finset.mem_range.mp hv) hL
      rw [Nat.mod_eq_of_lt hu', Nat.mod_eq_of_lt hv']
    rw [Finset.sum_eq_single u]
    · simp
    · intro v hv hvu
      rw [if_neg]
      intro h
      exact hvu ((hinj v hv).mp h).symm
    · intro hu'
      exact absurd hu hu'
  rw [Finset.sum_congr rfl inner, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_comm]

lemma W_zero (n L : ℕ) : W (p := p) n L 0 = (L : ℂ) * L := by
  simp [W, D, Finset.card_product]

lemma sum_norm_W (n L : ℕ) (hL : L ≤ p) : ∑ k : ZMod p, ‖W n L k‖ = (p : ℝ) * L := by
  simp_rw [norm_W]
  exact parseval L hL

lemma main_bound (hodd : 2 < p) (n L : ℕ) (hL : L ≤ p) :
    (L : ℝ) ^ 4 * p - B p * ((p : ℝ) * L) ^ 2 ≤ (p : ℝ) ^ 2 * (Qn p n L : ℝ) := by
  set E : ZMod p → ZMod p → ℂ := fun k h =>
    K (-k) (-h) - (if -k = 0 ∧ -h = 0 then (p : ℂ) else 0) with hE
  have hsplit : ∑ k : ZMod p, ∑ h : ZMod p, W n L k * W n L h * K (-k) (-h) =
      ∑ k : ZMod p, ∑ h : ZMod p, W n L k * W n L h * E k h +
      ∑ k : ZMod p, ∑ h : ZMod p,
        W n L k * W n L h * (if -k = 0 ∧ -h = 0 then (p : ℂ) else 0) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun h _ => ?_)
    simp only [hE]
    ring
  have h2 : ∑ k : ZMod p, ∑ h : ZMod p,
      W n L k * W n L h * (if -k = 0 ∧ -h = 0 then (p : ℂ) else 0) =
      W (p := p) n L 0 * W (p := p) n L 0 * p := by
    rw [Finset.sum_eq_single (0 : ZMod p)]
    · rw [Finset.sum_eq_single (0 : ZMod p)]
      · simp
      · intro h _ hh
        simp [hh]
      · simp
    · intro k _ hk
      apply Finset.sum_eq_zero
      intro h _
      simp [hk]
    · simp
  have hR : ‖∑ k : ZMod p, ∑ h : ZMod p, W n L k * W n L h * E k h‖ ≤
      B p * ((p : ℝ) * L) ^ 2 := by
    calc ‖∑ k : ZMod p, ∑ h : ZMod p, W n L k * W n L h * E k h‖
        ≤ ∑ k : ZMod p, ‖∑ h : ZMod p, W n L k * W n L h * E k h‖ := norm_sum_le _ _
      _ ≤ ∑ k : ZMod p, ∑ h : ZMod p, ‖W n L k‖ * ‖W n L h‖ * B p := by
          apply Finset.sum_le_sum
          intro k _
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun h _ => ?_))
          rw [norm_mul, norm_mul]
          exact mul_le_mul_of_nonneg_left (K'_le hodd (-k) (-h)) (by positivity)
      _ = B p * ((∑ k : ZMod p, ‖W n L k‖) * (∑ h : ZMod p, ‖W n L h‖)) := by
          rw [Finset.sum_mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl (fun k _ => ?_)
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun h _ => ?_)
          ring
      _ = B p * ((p : ℝ) * L) ^ 2 := by
          rw [sum_norm_W n L hL]
          ring
  have hid := count_identity (p := p) n L
  rw [hsplit, h2, W_zero] at hid
  have hreal : (((p : ℝ) ^ 2 * (Qn p n L : ℝ) - (L : ℝ) ^ 4 * p : ℝ) : ℂ) =
      ∑ k : ZMod p, ∑ h : ZMod p, W n L k * W n L h * E k h := by
    push_cast
    rw [hid]
    ring
  have habs : |(p : ℝ) ^ 2 * (Qn p n L : ℝ) - (L : ℝ) ^ 4 * p| ≤ B p * ((p : ℝ) * L) ^ 2 := by
    rw [← Real.norm_eq_abs, ← Complex.norm_real, hreal]
    exact hR
  have := neg_abs_le ((p : ℝ) ^ 2 * (Qn p n L : ℝ) - (L : ℝ) ^ 4 * p)
  linarith

lemma inj_zero (n L : ℕ) (hL : L ≤ p) :
    ((D L).filter (fun d => aD p n d = 0)).card ≤ L := by
  calc ((D L).filter (fun d => aD p n d = 0)).card ≤ (Finset.range L).card := by
        refine Finset.card_le_card_of_injOn (fun d => d.1) ?_ ?_
        · intro d hd
          simp only [coe_filter, Set.mem_setOf_eq, D, Finset.mem_product] at hd
          exact hd.1.1
        · intro d hd d' hd' hdd
          simp only [coe_filter, Set.mem_setOf_eq, D, Finset.mem_product, Finset.mem_range] at hd hd'
          simp only at hdd
          have e : aD p n d = aD p n d' := hd.2.trans hd'.2.symm
          simp only [aD] at e
          push_cast at e
          rw [hdd] at e
          have e2 : ((d.2 : ℕ) : ZMod p) = ((d'.2 : ℕ) : ZMod p) := add_left_cancel e
          rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt (lt_of_lt_of_le hd.1.2 hL),
            Nat.mod_eq_of_lt (lt_of_lt_of_le hd'.1.2 hL)] at e2
          exact Prod.ext hdd e2
    _ = L := Finset.card_range L

lemma exists_pair (n L : ℕ) (hL : L ≤ p) (hQ : (L : ℝ) ^ 2 < (Qn p n L : ℝ)) :
    ∃ d ∈ D L, ∃ e ∈ D L, aD p n d * aD p n e = 1 := by
  by_contra hcon
  push Not at hcon
  have hle : Qn p n L ≤ ((D L).filter (fun d => aD p n d = 0)).card *
      ((D L).filter (fun d => aD p n d = 0)).card := by
    rw [Finset.card_filter, Finset.sum_mul_sum]
    unfold Qn
    apply Finset.sum_le_sum
    intro d hd
    apply Finset.sum_le_sum
    intro e he
    rw [Finset.sum_eq_single (aD p n d)]
    · simp only [true_and]
      by_cases h1 : aD p n e = (aD p n d)⁻¹
      · by_cases h0 : aD p n d = 0
        · have h3 : aD p n e = 0 := by rw [h1, h0, inv_zero]
          simp [h0, h3]
        · exact absurd (by rw [h1]; exact mul_inv_cancel₀ h0) (hcon d hd e he)
      · simp [h1]
    · intro x _ hx
      rw [if_neg]
      rintro ⟨h, _⟩
      exact hx h.symm
    · simp
  have hz := inj_zero (p := p) n L hL
  have : Qn p n L ≤ L * L := hle.trans (Nat.mul_le_mul hz hz)
  have : (Qn p n L : ℝ) ≤ (L : ℝ) ^ 2 := by
    rw [sq]; exact_mod_cast this
  linarith

lemma core (hodd : 2 < p) (n L : ℕ) (hL : L ≤ p) (hL0 : 0 < L) (hbig : (p : ℝ) * (B p + 1) < (L : ℝ) ^ 2) :
    ∃ d ∈ D L, ∃ e ∈ D L, aD p n d * aD p n e = 1 := by
  apply exists_pair n L hL
  have hmb := main_bound (p := p) hodd n L hL
  have hp : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL0
  have key : (p : ℝ) ^ 2 * (L : ℝ) ^ 2 < (p : ℝ) ^ 2 * (Qn p n L : ℝ) := by
    have h1 : (p : ℝ) ^ 2 * (L : ℝ) ^ 2 < (L : ℝ) ^ 4 * p - B p * ((p : ℝ) * L) ^ 2 := by
      have hpos : 0 < (p : ℝ) * (L : ℝ) ^ 2 := by positivity
      have : (p : ℝ) * (L : ℝ) ^ 2 * ((p : ℝ) * (B p + 1)) <
          (p : ℝ) * (L : ℝ) ^ 2 * (L : ℝ) ^ 2 := mul_lt_mul_of_pos_left hbig hpos
      nlinarith
    linarith
  exact lt_of_mul_lt_mul_left key (by positivity)


end OMA.Heil

open OMA.Heil

theorem OMA.solution : type_of% @Erdos445.erdos_445.variants.heath_brown := by
  intro c hc
  set c' : ℝ := min c 1 with hc'def
  have hc'1 : c' ≤ 1 := min_le_right _ _
  have hc'c : c' ≤ c := min_le_left _ _
  have hc'0 : 3 / 4 < c' := lt_min hc (by norm_num)
  have t1 : Filter.Tendsto (fun p : ℕ => (p : ℝ) ^ (2 * c' - 3/2)) Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop (by linarith)).comp tendsto_natCast_atTop_atTop
  have t2 : Filter.Tendsto (fun p : ℕ => (p : ℝ) ^ c') Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop (by linarith)).comp tendsto_natCast_atTop_atTop
  filter_upwards [t1.eventually_gt_atTop 96, t2.eventually_ge_atTop 4,
    Filter.eventually_ge_atTop 3] with p hp1 hp2 hp3 hprime n
  haveI : Fact p.Prime := ⟨hprime⟩
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hprime.pos
  have hp1' : (1 : ℝ) ≤ p := by exact_mod_cast (show 1 ≤ p by omega)
  set H : ℝ := (p : ℝ) ^ c' with hH
  set L : ℕ := ⌊H / 2⌋₊ with hLdef
  have hH0 : 0 ≤ H := by positivity
  have hLle : (L : ℝ) ≤ H / 2 := Nat.floor_le (by positivity)
  have hLge : H / 2 - 1 < (L : ℝ) := Nat.sub_one_lt_floor _
  have hHp : H ≤ p := by
    have := Real.rpow_le_rpow_of_exponent_le hp1' hc'1
    rwa [Real.rpow_one] at this
  have hHc : H ≤ (p : ℝ) ^ c := Real.rpow_le_rpow_of_exponent_le hp1' hc'c
  have hLp : L ≤ p := by
    have : (L : ℝ) ≤ p := by linarith
    exact_mod_cast this
  have hL4 : H / 4 ≤ (L : ℝ) := by linarith
  have hL0 : 0 < L := by
    have : (0 : ℝ) < L := by linarith
    exact_mod_cast this
  have hsqrt : 1 ≤ Real.sqrt (p : ℝ) := Real.one_le_sqrt.mpr hp1'
  have hprod : 0 < (p : ℝ) * Real.sqrt p := by positivity
  have e : H ^ 2 = (p : ℝ) ^ (2 * c' - 3/2) * ((p : ℝ) * Real.sqrt p) := by
    rw [hH, ← Real.rpow_natCast, ← Real.rpow_mul hp0.le, Real.sqrt_eq_rpow]
    calc
      _ = (p : ℝ) ^ ((2*c' - 3/2) + (1 + 1/2)) := by congr 1; push_cast; ring
      _ = _ := by rw [Real.rpow_add hp0, Real.rpow_add hp0, Real.rpow_one]
  have hlarge : 96 * ((p : ℝ) * Real.sqrt p) < H ^ 2 :=
    e ▸ mul_lt_mul_of_pos_right hp1 hprod
  have hfloor : (H / 4) ^ 2 ≤ (L : ℝ) ^ 2 := pow_le_pow_left₀ (by positivity) hL4 2
  have hbig : (p : ℝ) * (B p + 1) < (L : ℝ)^2 := by
    unfold B
    have := mul_nonneg hp0.le (sub_nonneg.mpr hsqrt)
    nlinarith
  obtain ⟨d, hd, e, he, hde⟩ := core (by omega) n L hLp hL0 hbig
  simp only [D, Finset.mem_product, Finset.mem_range] at hd he
  unfold Erdos445.Erdos445Prop
  refine ⟨n + 1 + d.1 + d.2, n + 1 + e.1 + e.2, by omega, ?_, by omega, ?_, ?_⟩
  · have : ((n + 1 + d.1 + d.2 : ℕ) : ℝ) ≤ n + 2 * L - 1 := by
      have : n + 1 + d.1 + d.2 + 1 ≤ n + 2 * L := by omega
      have : ((n + 1 + d.1 + d.2 + 1 : ℕ) : ℝ) ≤ ((n + 2 * L : ℕ) : ℝ) := by exact_mod_cast this
      push_cast at this ⊢
      linarith
    linarith
  · have : ((n + 1 + e.1 + e.2 : ℕ) : ℝ) ≤ n + 2 * L - 1 := by
      have : n + 1 + e.1 + e.2 + 1 ≤ n + 2 * L := by omega
      have : ((n + 1 + e.1 + e.2 + 1 : ℕ) : ℝ) ≤ ((n + 2 * L : ℕ) : ℝ) := by exact_mod_cast this
      push_cast at this ⊢
      linarith
    linarith
  · rw [← ZMod.natCast_eq_natCast_iff]
    push_cast
    simp only [aD] at hde
    push_cast at hde
    exact hde

