import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Schulte’s adjacent-gcd sum (OEIS A384531)

Source: https://oeis.org/A384531
Credit: @anmolspace

Werner Schulte defines the sequence multiplicatively by its values on prime
powers. The empty product gives a(1) = 1. David Radcliffe published a proof
of the proposed gcd identity in Notes on two arithmetical functions.
-/

namespace OMA.S_oeis_a384531

/-- The defining product over the positive exponents in the factorization of n. -/
def a (n : ℕ) : ℕ :=
  ∏ p ∈ n.primeFactors,
    let e := n.factorization p
    ((2*e + 1)*p - 2*e) * p^(e-1)

/-- The adjacent-gcd sum agrees with the defining product at every positive index. -/
theorem main : ∀ n : ℕ, 0 < n →
    a n = ∑ i ∈ Finset.range n, (i+1).gcd n * (i+2).gcd n := by
  sorry

end OMA.S_oeis_a384531
