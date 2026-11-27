import Mathlib

/-!
# OEIS A196200 and Sándor's inequality for Dedekind psi

Source: https://oeis.org/A196200 (OEIS Foundation, CC BY-SA 4.0).
Credit: @anmolspace.

József Sándor proposed the inequality in 1988. His 2005 paper
"On the Composition of Some Arithmetic Functions, II", equation (1.8),
states it for all n ≥ 2. Remark 3.26 credits L. Tóth with a counterexample at 39270.
-/

namespace OMA.S_oeis_a196200

/-- Dedekind's psi at a positive integer adds a factor (p+1)/p for each distinct prime divisor. -/
def psi (n : ℕ) : ℕ :=
  (n / ∏ p ∈ n.primeFactors, p) * ∏ p ∈ n.primeFactors, (p + 1)

theorem main : ∀ n : ℕ, 2 ≤ n → (psi n).totient ≤ n := by
  sorry

end OMA.S_oeis_a196200
