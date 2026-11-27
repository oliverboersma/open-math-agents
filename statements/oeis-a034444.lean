import Mathlib.NumberTheory.Divisors
import Mathlib.Algebra.Ring.Parity

/-!
# OEIS A034444

Source: https://oeis.org/A034444 (OEIS Foundation, CC BY-SA 4.0).
Ivan N. Ianakiev conjectured that for every positive n and every
nonnegative exponent k, the sum of the k-th powers of the odd unitary
divisors of n divides the corresponding sum over all unitary divisors.
The entry records a proof by Peter Bala, with a correction by David Radcliffe.
A divisor d of n is unitary when d and n / d are relatively prime.
-/

namespace OMA.S_oeis_a034444

def unitary (n : ℕ) : Finset ℕ := n.divisors.filter (fun d => Nat.Coprime d (n / d))

theorem main : ∀ n : ℕ, 0 < n → ∀ k : ℕ,
    (∑ d ∈ (unitary n).filter Odd, d^k) ∣ ∑ d ∈ unitary n, d^k := by
  sorry

end OMA.S_oeis_a034444
