import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Prime divisors of central binomial coefficients

Source: https://oeis.org/A394454 (Vincenzo Librandi, OEIS Foundation, CC BY-SA 4.0).
For every prime p there are infinitely many positive n such that p divides C(2n,n).
The entry also observes that the sum of the distinct prime divisors has infinite limsup.
-/

namespace OMA.S_oeis_a394454

def a (n : ℕ) : ℕ := ∑ p ∈ n.centralBinom.primeFactors, p

theorem main :
    (∀ p : ℕ, p.Prime → {n : ℕ | 1 ≤ n ∧ p ∣ n.centralBinom}.Infinite) ∧
    (∀ B N : ℕ, ∃ n > N, B < a n) := by
  sorry

end OMA.S_oeis_a394454
