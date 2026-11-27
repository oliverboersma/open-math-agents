import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# The sum of floors with Fibonacci denominators

The terms begin with F(2)=1, F(3)=2. Natural-number division supplies the
floors. The real sum defining value has only finitely many nonzero terms.
The reciprocal Fibonacci constant includes F(1)=1 as well. Asymptotic
equivalence to (constant-1)n is stated as convergence of the ratio to one.

Source: https://oeis.org/A038663 (conjecture by Vaclav Kotesovec)
Constant: https://oeis.org/A079586
Credit: @KoaOkano
-/

namespace OMA.S_oeis_a038663

noncomputable def value (n : ℕ) : ℝ := ∑' k : ℕ, ((n / Nat.fib (k+2) : ℕ) : ℝ)

noncomputable def reciprocalConstant : ℝ := ∑' k : ℕ, 1 / (Nat.fib (k+1) : ℝ)

open Filter Topology

theorem main : Tendsto (fun n : ℕ => value n / ((reciprocalConstant-1)*(n:ℝ)))
    atTop (𝓝 1) := by
  sorry

end OMA.S_oeis_a038663
