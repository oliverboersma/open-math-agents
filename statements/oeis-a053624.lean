import Mathlib

/-!
# A053624: Highly composite odd numbers: odd numbers where d(n) increases to a record.

Source: https://oeis.org/A053624
Credit: @ShoQo

Conjecture (Harvey P. Dale, Jul 05 2023): "all terms after the first three terms are congruent
to 5 mod 10." (Keith F. Lynch, Jan 12 2024: "Dale's conjecture is correct.")

Formalization notes:
* n is a term iff n is odd and d(m) < d(n) for every odd m < n, where d is the number of
  divisors (`#n.divisors`); data: 1, 3, 9, 15, 45, 105, ...
* "after the first three terms" excludes 1, 3 and 9.
-/

namespace OMA.S_oeis_a053624

/-- n is a highly composite odd number: odd, with more divisors than every smaller odd number. -/
def IsTerm (n : ℕ) : Prop :=
  Odd n ∧ ∀ m : ℕ, Odd m → m < n → m.divisors.card < n.divisors.card

theorem main : ∀ n : ℕ, IsTerm n → n ≠ 1 → n ≠ 3 → n ≠ 9 → n % 10 = 5 := by
  sorry

end OMA.S_oeis_a053624
