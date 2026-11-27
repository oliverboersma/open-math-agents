import FormalConjectures.GreensOpenProblems.«14»
import Mathlib

/-! Green's lower bound for W(3, r) from Hunter's improvement. Hunter, Improved lower
bounds for van der Waerden numbers (2022), proves that W(3, r) is at least of order
exp (c (log r)^(2 - o(1))). With the same constant and the same error function, the
function exp (c (log r)^(4/3 - o(1))) is eventually smaller, since log r ≥ 1 and the
exponent 4/3 - o(r) is below 2 - o(r). -/

namespace OMA.R_Green14_green_14_lower_bound_green_R1
open Filter Topology

/-- Hunter's lower bound for W(3, r). -/
def H1 : Prop := ∃ c : ℝ, 0 < c ∧ ∃ (o : ℕ → ℝ) (_ : Tendsto o atTop (𝓝 0)),
  (fun (r : ℕ) => Real.exp (c * (Real.log r) ^ (2 - o r))) =O[atTop]
    (fun r => (Green14.W 3 r : ℝ))

/-- Comparison of the two shapes with the same constant and error function. -/
def H2 : Prop := ∀ c : ℝ, 0 < c → ∀ o : ℕ → ℝ,
  (fun (r : ℕ) => Real.exp (c * (Real.log r) ^ (4 / 3 - o r))) =O[atTop]
    fun (r : ℕ) => Real.exp (c * (Real.log r) ^ (2 - o r))

theorem main : H1 → H2 → type_of% @Green14.green_14_lower_bound_green := by
  rintro ⟨c, hc, o, ho, hhunter⟩ hcomp
  exact ⟨c, hc, o, ho, (hcomp c hc o).trans hhunter⟩

end OMA.R_Green14_green_14_lower_bound_green_R1
