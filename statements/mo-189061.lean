import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.Complex.Basic

/-!
# Perturbing a polynomial's constant term

Source: https://mathoverflow.net/questions/189061
Credit: @eliayousf

For a real polynomial, evaluation at a complex point uses the usual
embedding of the reals into the complex numbers. The right half-plane
is defined by strictly positive real part. The target states the source's
claim about all real constant perturbations.
-/

namespace OMA.S_mo_189061

def hasRightRoot (p : Polynomial ℝ) : Prop :=
  ∃ z : ℂ, 0 < z.re ∧ p.eval₂ Complex.ofRealHom z = 0

theorem main : ∀ p : Polynomial ℝ, p.eval 0 = 0 → hasRightRoot p →
    ∀ ε : ℝ, hasRightRoot (p + Polynomial.C ε) := by
  sorry

end OMA.S_mo_189061
