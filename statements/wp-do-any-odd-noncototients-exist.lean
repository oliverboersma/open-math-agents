import Mathlib

/-!
# Do any odd noncototients exist?

Source: https://en.wikipedia.org/wiki/Noncototient
Credit: @ihateSAS

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.

The source: "a **noncototient** is a positive integer `n` that cannot be expressed as the
difference between a positive integer `m` and the number of coprime integers below it. That is,
`m - φ(m) = n` has no solution for `m`"; the cototient of `m` is `m - φ(m)`.

The source then says "It is conjectured that all noncototients are even", and observes that `1`,
`3` and `5` are all cototients (`1 = 2 - φ(2)`, `3 = 9 - φ(9)`, `5 = 25 - φ(25)`).  The open
question is whether some *odd* number fails to be a cototient.

So the proposition formalized below is: there exists an odd natural number that is not of the form
`m - φ(m)` for any positive `m`.
-/

namespace OMA.S_wp_do_any_odd_noncototients_exist

-- definitions the statement needs (no sorry, no axiom)

/-- `n` is a **cototient** when `n = m - φ(m)` for some positive integer `m`. -/
def IsCototient (n : ℕ) : Prop :=
  ∃ m : ℕ, 0 < m ∧ m - Nat.totient m = n

/-- Do any odd noncototients exist? -/
theorem main : ∃ n : ℕ, Odd n ∧ ¬ IsCototient n := by
  sorry

end OMA.S_wp_do_any_odd_noncototients_exist
