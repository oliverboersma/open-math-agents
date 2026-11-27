import Mathlib

/-!
# A140472: a(n) = a(n - a(n-1)) + a(floor(n/2)).

Source: https://oeis.org/A140472
Credit: @Raimo33

Conjecture (Jon Maiga, Aug 16 2019): a(n) = (n + A006519(n))/2 for n > 0.

Formalization notes:
* Offset 0, with a(0) = 0, a(1) = 1 and a(n) = a(n - a(n-1)) + a(floor(n/2)) for n >= 2, as in
  the Mathematica and Haskell programs of the entry (data: 0, 1, 2, 2, 4, 3, 4, 4, 8, ...).
* The recursion is self-referential, so the sequence is described by the predicate `IsA140472`
  on functions `ℕ → ℕ`. The statement asserts that such a function exists and that every such
  function satisfies the conjectured formula.
* In ℕ, `n - f (n - 1)` is truncated subtraction; along the sequence `a(n-1) ≤ n - 1`, so it is
  the integer difference.
* A006519(n) is the highest power of 2 dividing n, here `2 ^ padicValNat 2 n`.
-/

namespace OMA.S_oeis_a140472

/-- `f` satisfies the defining initial values and recurrence of A140472. -/
def IsA140472 (f : ℕ → ℕ) : Prop :=
  f 0 = 0 ∧ f 1 = 1 ∧ ∀ n : ℕ, 2 ≤ n → f n = f (n - f (n - 1)) + f (n / 2)

/-- Maiga's conjecture: a(n) = (n + A006519(n)) / 2 for n > 0. -/
theorem main : (∃ f : ℕ → ℕ, IsA140472 f) ∧
    ∀ f : ℕ → ℕ, IsA140472 f → ∀ n : ℕ, 0 < n → f n = (n + 2 ^ padicValNat 2 n) / 2 := by
  sorry

end OMA.S_oeis_a140472
