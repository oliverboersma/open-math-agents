import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Prime.Defs

/-!
# Factorial bound for prime progressions in OEIS A005115

Source: https://oeis.org/A005115 (OEIS Foundation, CC BY-SA 4.0).
Formalization: @sturdy4days.

In §2.1 of *Prime Number Patterns* (2008), Andrew Granville conjectures
that for each length n at least 3, there is an arithmetic progression
of n distinct primes whose last term is at most n! + 1.
Paper: https://dms.umontreal.ca/~andrew/PDF/PrimePattMonthly.1.pdf.
-/

namespace OMA.S_oeis_a005115

theorem main : ∀ n : ℕ, 3 ≤ n →
    ∃ a d : ℕ, 0 < d ∧ a + (n - 1) * d ≤ n.factorial + 1 ∧
      ∀ i : Fin n, (a + (i : ℕ) * d).Prime := by
  sorry

end OMA.S_oeis_a005115
