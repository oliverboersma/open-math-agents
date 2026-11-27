import Mathlib.RingTheory.PowerSeries.Log
import Mathlib.Analysis.Complex.Basic

/-!
# Integrality of powers of logarithmic exponential generating function moments

Source: https://oeis.org/A167138 (Paul D. Hanna, OEIS Foundation, CC BY-SA 4.0).
A167139 records the same universal conjecture. The input sequence is allowed
arbitrary complex values. Substitution into its exponential generating function
uses the formal logarithm of 1+X. Integrality means that every coefficient is
the image of an integer.
-/

namespace OMA.S_oeis_a167138

noncomputable def egf (L : ℕ → ℂ) : PowerSeries ℂ := PowerSeries.mk (fun n => L n / n.factorial)

noncomputable def transform (L : ℕ → ℂ) : PowerSeries ℂ := (egf L).subst (PowerSeries.log ℂ)

def integralSeries (S : PowerSeries ℂ) : Prop := ∀ n : ℕ, ∃ z : ℤ, PowerSeries.coeff n S = z

theorem main : ∀ L : ℕ → ℂ, integralSeries (transform L) → ∀ m : ℕ, 0 < m →
    integralSeries (transform (fun n => L n ^ m)) := by
  sorry

end OMA.S_oeis_a167138
