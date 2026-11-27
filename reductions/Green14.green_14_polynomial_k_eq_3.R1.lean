import FormalConjectures.GreensOpenProblems.«14»
import Mathlib

/-! No polynomial growth for W(3, r), from Green's superpolynomial lower bound. Green,
New lower bounds for van der Waerden numbers (2021), proves that W(3, r) is at least of
order exp (c (log r)^(4/3 - o(1))). A bound of this shape is not O(r^d) for any d, which
is a statement about real functions only, so a polynomial bound for W(3, r) would
contradict it by transitivity. -/

namespace OMA.R_Green14_green_14_polynomial_k_eq_3_R1
open Filter Topology

/-- Green's lower bound for W(3, r). -/
def H1 : Prop := ∃ c : ℝ, 0 < c ∧ ∃ (o : ℕ → ℝ) (_ : Tendsto o atTop (𝓝 0)),
  (fun (r : ℕ) => Real.exp (c * (Real.log r) ^ (4 / 3 - o r))) =O[atTop]
    fun r => (Green14.W 3 r : ℝ)

/-- A function of the shape exp (c (log r)^(4/3 - o(1))) is not polynomially bounded. -/
def H2 : Prop := ∀ c : ℝ, 0 < c → ∀ o : ℕ → ℝ, Tendsto o atTop (𝓝 0) → ∀ d : ℕ,
  ¬ (fun (r : ℕ) => Real.exp (c * (Real.log r) ^ (4 / 3 - o r))) =O[atTop]
    fun (r : ℕ) => (r : ℝ) ^ d

theorem main : H1 → H2 → type_of% @Green14.green_14_polynomial_k_eq_3 := by
  rintro ⟨c, hc, o, ho, hgreen⟩ hsuper ⟨d, hd⟩
  exact hsuper c hc o ho d (hgreen.trans hd)

end OMA.R_Green14_green_14_polynomial_k_eq_3_R1
