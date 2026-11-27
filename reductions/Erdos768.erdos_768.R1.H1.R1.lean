import OMAReductions.R_Erdos768_erdos_768_R1
import Mathlib

-- Reduction Erdos768.erdos_768.R1.H1.R1 of Erdős Problem 768
-- Credit: @senamakel
-- Splits the primes-in-logarithmic-intervals estimate (Lemma 2.8 of Eric Li, The Sylow Divisor Condition, arXiv:2606.24872,
-- an unrefereed preprint) into the prime number theorem with a power-saving error term for the Chebyshev psi function
-- (the MediumPNT theorem of the PrimeNumberTheoremAnd project, a known theorem) and the elementary passage from it
-- to the count of primes in a logarithmic interval.
-- Lean source of that argument: github.com/ericlisg/erdos768-lean (commit e46ab245f1e5eb2d1f0b184874c4e32e02ad16c9, Apache-2.0).

open Filter Asymptotics

namespace OMA.R_Erdos768_erdos_768_R1_H1_R1

def H1 : Prop :=
  ∃ c > 0, (Chebyshev.psi - id) =O[atTop] fun x : ℝ => x * Real.exp (-c * (Real.log x) ^ ((1 : ℝ) / 10))

def H2 : Prop :=
  (∃ c > 0, (Chebyshev.psi - id) =O[atTop] fun x : ℝ => x * Real.exp (-c * (Real.log x) ^ ((1 : ℝ) / 10))) →
  ∀ u δ : ℕ → ℝ, Tendsto u atTop atTop → (∀ᶠ n in atTop, (u n)⁻¹ ^ 2 ≤ δ n ∧ δ n ≤ 1) →
    Tendsto (fun n : ℕ => (((Finset.Icc 1 ⌊Real.exp (u n)⌋₊).filter (fun p => Nat.Prime p ∧ Real.exp (u n - δ n) < (p : ℝ))).card : ℝ) / ((1 - Real.exp (-(δ n))) * Real.exp (u n) / (u n))) atTop (nhds 1)

theorem main : H1 → H2 → OMA.R_Erdos768_erdos_768_R1.H1 := by
  intro h1 h2
  exact h2 h1

end OMA.R_Erdos768_erdos_768_R1_H1_R1
