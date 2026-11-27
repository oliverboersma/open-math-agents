import FormalConjectures.ErdosProblems.«830»
import Mathlib

/-! Pomerance's first bound A(x) ≤ x exp (-(log x)^(1/3)) for the number of amicable pairs
from his later bound A(x) ≤ x exp (-(1/2 + o(1)) sqrt (log x log log log x)), which is the
catalogue's Erdos830.erdos_830.variants.pomerance_stronger. Since
(1/2 + o(1)) sqrt (log x log log log x) is eventually at least (log x)^(1/3), the later bound
is eventually the smaller one; that comparison is a statement about real functions only. -/

namespace OMA.R_Erdos830_erdos_830_variants_pomerance_R1
open Filter Asymptotics

/-- Pomerance's bound with exponent (1/2 + o(1)) sqrt (log x log log log x). -/
def H1 : Prop := ∃ o : ℝ → ℝ, o =o[atTop] (1 : ℝ → ℝ) ∧ ∀ᶠ x : ℝ in atTop,
  Erdos830.A x ≤
    x * Real.exp (-(1 / 2 + o x) * Real.sqrt (Real.log x * Real.log (Real.log (Real.log x))))

/-- For o(x) tending to 0, the bound with exponent (1/2 + o(x)) sqrt (log x log log log x)
is eventually below the bound with exponent (log x)^(1/3). -/
def H2 : Prop := ∀ o : ℝ → ℝ, o =o[atTop] (1 : ℝ → ℝ) → ∀ᶠ x : ℝ in atTop,
  x * Real.exp (-(1 / 2 + o x) * Real.sqrt (Real.log x * Real.log (Real.log (Real.log x)))) ≤
    x * Real.exp (-Real.nthRoot 3 (Real.log x))

theorem main : H1 → H2 → type_of% @Erdos830.erdos_830.variants.pomerance := by
  rintro ⟨o, ho, h⟩ h2
  filter_upwards [h, h2 o ho] with x hx hx2
  exact hx.trans hx2

end OMA.R_Erdos830_erdos_830_variants_pomerance_R1
