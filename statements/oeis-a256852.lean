import Mathlib

/-!
# A256852: Number of ways to write prime(n) = a^2 + b^4.

Source: https://oeis.org/A256852
Credit: @bnb9001

The sequence has offset 1, with prime(1) = 2. The representations use positive integers `a` and
`b`, as the data show (a(1) = 1 from 2 = 1^2 + 1^4, and a(7) = 2 from 17 = 4^2 + 1^4 = 1^2 + 2^4).
Since `a^2 ≤ p` and `b^4 ≤ p`, it is enough to count pairs with `1 ≤ a, b ≤ p`.

Conjecture: a(n) ≤ 2. Jonathan Sondow notes that the conjecture is true, by the uniqueness part
of Fermat's two-squares theorem.
-/

namespace OMA.S_oeis_a256852

/-- The number of pairs of positive integers `(a, b)` with `a ^ 2 + b ^ 4 = p`. -/
def count (p : ℕ) : ℕ :=
  ((Finset.Icc 1 p ×ˢ Finset.Icc 1 p).filter (fun ab => ab.1 ^ 2 + ab.2 ^ 4 = p)).card

/-- A256852: the number of ways to write the `n`-th prime as `a ^ 2 + b ^ 4`. -/
noncomputable def a (n : ℕ) : ℕ := count (Nat.nth Nat.Prime (n - 1))

/-- For every `n ≥ 1`, `a n ≤ 2`. -/
theorem main : ∀ n : ℕ, 1 ≤ n → a n ≤ 2 := by
  sorry

end OMA.S_oeis_a256852
