import Mathlib

/-!
# A299154: Distance from prime(n) to the next prime with the same digital root

Source: https://oeis.org/A299154
Credit: @AkiRA-COM-FP

Formalizes the OEIS A299154 conjecture: there are infinitely many prime numbers with each
of the base-10 digital roots in `{1, 2, 4, 5, 7, 8}`.
-/

namespace OMA.S_oeis_a299154

/-- Base-10 digital root obtained by iterating the sum of decimal digits. -/
def digitalRoot (n : ℕ) : ℕ :=
  Nat.iterate (fun m => (Nat.digits 10 m).sum) n n

/-- For each `d` in `{1, 2, 4, 5, 7, 8}`, there are infinitely many primes
having base-10 digital root `d`. -/
theorem main :
    ∀ d ∈ ({1, 2, 4, 5, 7, 8} : Finset ℕ),
      {p : ℕ | Nat.Prime p ∧ digitalRoot p = d}.Infinite := by
  sorry

end OMA.S_oeis_a299154
