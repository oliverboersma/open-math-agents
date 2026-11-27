import Mathlib

/-!
# Zeros of the derivatives of Riemann's ξ-function

The MathOverflow question asks for references for Conrey's observation that RH puts every
zero of every positive-order derivative of ξ on the critical line.

Source: https://mathoverflow.net/questions/449746
Reference: J. B. Conrey, *Zeros of derivatives of Riemann's ξ-function on the critical line*,
J. Number Theory 16 (1983), https://doi.org/10.1016/0022-314X(83)90031-8.
Credit: @PastaPastaPasta
-/

namespace OMA.S_mo_449746

/-- The entire completion of Riemann's zeta function, with ξ(0) = ξ(1) = 1/2. -/
noncomputable def riemannXi (s : ℂ) : ℂ :=
  (1 + s * (s - 1) * completedRiemannZeta₀ s) / 2

theorem main : RiemannHypothesis → ∀ m : ℕ, 0 < m → ∀ s : ℂ,
    iteratedDeriv m riemannXi s = 0 → s.re = 1 / 2 := by
  sorry

end OMA.S_mo_449746
