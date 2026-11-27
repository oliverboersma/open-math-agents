import Mathlib

/-!
# A008784: Numbers k such that sqrt(-1) mod k exists; or, numbers that are primitively
represented by x^2 + y^2.

Source: https://oeis.org/A008784
Credit: @ShoQo

Conjecture (Kaloyan Todorov, Mar 25 2009): "In appears that {a(n)} is the set of proper divisors
of numbers of the form m^2+1." (Franklin T. Adams-Watters, Oct 07 2009: "This conjecture is
correct.")

Formalization notes:
* The terms are the k ≥ 1 such that sqrt(-1) mod k exists, i.e. x^2 = -1 has a solution in
  `ZMod k` (data: 1, 2, 5, 10, 13, ...).
* A proper divisor of N is a divisor of N other than N itself. The claim is that k ≥ 1 is a term
  iff k ∣ m^2 + 1 and k ≠ m^2 + 1 for some natural m.
-/

namespace OMA.S_oeis_a008784

theorem main : ∀ k : ℕ, 1 ≤ k →
    ((∃ x : ZMod k, x ^ 2 = -1) ↔ ∃ m : ℕ, k ∣ m ^ 2 + 1 ∧ k ≠ m ^ 2 + 1) := by
  sorry

end OMA.S_oeis_a008784
