import Mathlib

/-!
# OEIS A045473: primes congruent to 6 modulo 7

Source: https://oeis.org/A045473 (OEIS Foundation, CC BY-SA 4.0).
Conjecture posed by Federico Provvedi, March 31, 2018.
Formalization by ChatGPT (GPT-6.2), on behalf of @hayalows.

Over the field with p elements, the polynomial obtained by dividing
(1 + X)^7 - 1 by X has three irreducible quadratic factors exactly
for primes p congruent to 6 modulo 7. Monic factors represent the
factorization without ambiguity from nonzero scalar units.
-/

namespace OMA.S_oeis_a045473

open Polynomial

/-- The polynomial quotient, expanded over ZMod p without rational-function division. -/
noncomputable def shiftedQuotient (p : ℕ) : Polynomial (ZMod p) :=
  X ^ 6 + C 7 * X ^ 5 + C 21 * X ^ 4 + C 35 * X ^ 3 +
    C 35 * X ^ 2 + C 21 * X + C 7

theorem main : ∀ (p : ℕ) [Fact p.Prime],
    p % 7 = 6 ↔
      ∃ f g h : Polynomial (ZMod p),
        f.Monic ∧ g.Monic ∧ h.Monic ∧
        Irreducible f ∧ Irreducible g ∧ Irreducible h ∧
        f.natDegree = 2 ∧ g.natDegree = 2 ∧ h.natDegree = 2 ∧
        f * g * h = shiftedQuotient p := by
  sorry

end OMA.S_oeis_a045473
