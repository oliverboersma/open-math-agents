import Mathlib

/-!
# A242191: Expected value of the highest die when n six-sided dice are rolled, multiplied by 6^n.

Source: https://oeis.org/A242191
Credit: @bnb9001

The sequence has offset 1 (a(1) = 21, a(2) = 161). A roll of `n` dice is a function
`Fin n → Fin 6`, with die values `1..6` represented as `j + 1`; there are `6 ^ n` equally likely
rolls, so the expected highest die times `6 ^ n` is the sum of the highest die over all rolls.

Conjecture (R. J. Mathar, 2014): a(n) = -5^n - 3^n + 6^(n+1) - 2^n - 1 - 4^n, with a stated
rational generating function that is equivalent to this closed form. Robert Israel notes that
the conjecture is true. We state the closed form for every `n ≥ 1`.
-/

namespace OMA.S_oeis_a242191

/-- The highest die (values `1..6`) in the roll `f`. -/
def highest {n : ℕ} (f : Fin n → Fin 6) : ℕ := Finset.univ.sup (fun i => (f i : ℕ) + 1)

/-- A242191: the sum of the highest die over all `6 ^ n` rolls of `n` dice. -/
def a (n : ℕ) : ℕ := ∑ f : Fin n → Fin 6, highest f

/-- For every `n ≥ 1`, `a n = 6^(n+1) - 5^n - 4^n - 3^n - 2^n - 1`. -/
theorem main : ∀ n : ℕ, 1 ≤ n →
    (a n : ℤ) = 6 ^ (n + 1) - 5 ^ n - 4 ^ n - 3 ^ n - 2 ^ n - 1 := by
  sorry

end OMA.S_oeis_a242191
