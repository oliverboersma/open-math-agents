import Mathlib.Data.Finset.Prod
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Finset.Card

/-!
# Period six for differences of OEIS A106252

The entry counts sorted positive triples up to n for which each coordinate
divides the sum of the other two. John W. Layman recorded the question about
the first differences. Clark Kimberling later supplied a formula for the count.
The empty interval at n = 0 gives the natural initial count of zero.

Source: https://oeis.org/A106252
Credit: @erood (Lean formalization with Codex)
-/

namespace OMA.S_oeis_a106252

def triples (n : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  let box := Finset.Icc 1 n
  (box ×ˢ (box ×ˢ box)).filter fun ⟨x, y, z⟩ =>
    x ≤ y ∧ y ≤ z ∧ x ∣ y + z ∧ y ∣ x + z ∧ z ∣ x + y

def a (n : ℕ) : ℕ := (triples n).card

theorem main : ∀ n : ℕ, a (n + 7) - a (n + 6) = a (n + 1) - a n := by
  sorry

end OMA.S_oeis_a106252
