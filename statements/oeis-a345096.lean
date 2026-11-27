import Mathlib.Data.Rat.Floor
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# The floor and ceiling double sum in A345096

The quotient in the exponent is rational, so each floor and ceiling is
taken before the exponent is converted to a natural number. The two
summation intervals both begin at one. Convergence of a(n)/n² to 1/2
is equivalent to the source's a(n) ~ n²/2.

Source: https://oeis.org/A345096
Credit: @KoaOkano
-/

namespace OMA.S_oeis_a345096

open Finset Filter Topology

def summand (n k i : ℕ) : ℕ :=
  let q : ℚ := (n : ℚ) / ((k^i : ℕ) : ℚ)
  k ^ (1 - ⌈q⌉ + ⌊q⌋).toNat

def value (n : ℕ) : ℕ :=
  ∑ k ∈ Icc 1 n, ∑ i ∈ Icc 1 k, summand n k i

theorem main : Tendsto (fun n : ℕ => (value n : ℝ) / (n:ℝ)^2) atTop (𝓝 (1/2)) := by
  sorry

end OMA.S_oeis_a345096
