import Mathlib

/-!
# Conjecture: No positive integer can be written as $a^b+b^a$ in more than one way

Source: https://math.stackexchange.com/questions/3286093/conjecture-no-positive-integer-can-be-written-as-abba-in-more-than-one-way
Credit: @mgv27

Are there distinct integers $a,b,m,n>1$ such that $a^b+b^a=m^n+n^m$? That is, is there ever an
integer that can be written as $a^b+b^a$ in more than one way? The asker claims the answer is
No; no solutions are known (searches reported in the comments go well beyond $a,b \le 1000$).

Formalization notes:
* `main` follows the title: the map `{a, b} ↦ a^b + b^a` on unordered pairs of integers `≥ 2`
  is injective, i.e. `a^b + b^a = m^n + n^m` forces `{a, b} = {m, n}` as unordered pairs.
* If the pairs share an entry (say `a = m`), strict monotonicity of `b ↦ a^b + b^a` already
  forces `b = n`; so beyond the body's "distinct `a, b, m, n`" version, `main` only adds the
  cases `a = b` or `m = n` (sums of the form `2 a^a`), as the title's wording requires.
* A pure-Python search over `2 ≤ b ≤ a < 300` found no collision.
-/

namespace OMA.S_mse_3286093

/-- The Leyland-type value `a^b + b^a`. -/
def L (a b : ℕ) : ℕ := a ^ b + b ^ a

/-- No integer is `a^b + b^a` (with `a, b ≥ 2`) for two different unordered pairs `{a, b}`. -/
theorem main : ∀ a b m n : ℕ, 2 ≤ a → 2 ≤ b → 2 ≤ m → 2 ≤ n →
    L a b = L m n → (a = m ∧ b = n) ∨ (a = n ∧ b = m) := by
  sorry

end OMA.S_mse_3286093
