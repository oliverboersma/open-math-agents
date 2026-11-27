import Mathlib

/-!
# A common nonconstant divisor for a polynomial ideal

Problem: mse-2822876
Source: https://math.stackexchange.com/questions/2822876/is-there-a-non-constant-h-in-mathbbcx-1-dots-x-n-that-divides-ever
Question author: Leonardo Schultz, 2018-06-17; CC BY-SA 4.0.
Formalization credit: @lucasfreund2-cmd

The same mathematical statement is Exercise 5.5.3, page 169, in Hanspeter Kraft,
Basics from Algebraic Geometry, Appendix A. The general UFD argument is recorded
in Will Sawin's answer and tj_'s prime-avoidance comment at:
https://mathoverflow.net/questions/410693/a-criterion-for-whether-an-ideal-is-contained-in-a-principal-ideal

Positive total degree expresses nonconstancy, including exclusion of zero.
The hypothesis concerns every pair of elements of the ideal; it imposes no
distinctness or nonzero requirement on those elements. The number of variables
is arbitrary. For zero variables the hypothesis is impossible. No assumption
that the ideal is nonzero, principal, or given by a chosen finite generating
set is added.
-/

namespace OMA.S_mse_2822876

theorem main :
    ∀ (n : ℕ) (I : Ideal (MvPolynomial (Fin n) ℂ)),
      (∀ f ∈ I, ∀ g ∈ I,
        ∃ h : MvPolynomial (Fin n) ℂ, 0 < h.totalDegree ∧ h ∣ f ∧ h ∣ g) →
      ∃ h : MvPolynomial (Fin n) ℂ, 0 < h.totalDegree ∧ ∀ f ∈ I, h ∣ f := by
  sorry

end OMA.S_mse_2822876
