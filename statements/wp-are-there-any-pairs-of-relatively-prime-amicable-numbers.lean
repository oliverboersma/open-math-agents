import Mathlib

/-!
# Are there any pairs of relatively prime amicable numbers?

Source: https://en.wikipedia.org/wiki/Amicable_numbers (§ Other results)
Credit: @ihateSAS

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.

The source: "Amicable numbers are two different natural numbers related in such a way that the sum
of the proper divisors of each is equal to the other number."  The open question asked here is
whether *any* such pair consists of two numbers that are relatively prime, i.e. have gcd one.

Writing `sigma n` for the sum of *all* positive divisors of `n`, the sum of the proper divisors of
`n` is `sigma n - n`, so "the sum of the proper divisors of `a` is `b` and conversely" is stated
without truncated subtraction as `sigma a = a + b` and `sigma b = a + b`.  This is exactly the
standard reformulation, and it is what the first amicable pair `(220, 284)` satisfies:
`sigma 220 = 504 = 220 + 284 = sigma 284`.

So the proposition formalized below is: there exist distinct, relatively prime `a` and `b` forming
an amicable pair.  The source states the question as: "every known pair shares at least one common
prime factor. It is not known whether a pair of coprime amicable numbers exists, though if any does,
the product of the two must be greater than `10 ^ 67`."  Hence no bound is imposed on `a` and `b`
here: the question is bare existence.
-/

namespace OMA.S_wp_are_there_any_pairs_of_relatively_prime_amicable_numbers

-- definitions the statement needs (no sorry, no axiom)

/-- The sum of the positive divisors of `n` (including `n` itself). -/
def sigma (n : ℕ) : ℕ :=
  n.divisors.sum fun d => d

/-- `a` and `b` form an **amicable pair**: they are different, and the sum of the proper divisors
of each equals the other number, i.e. `sigma a = a + b` and `sigma b = a + b`. -/
def IsAmicablePair (a b : ℕ) : Prop :=
  a ≠ b ∧ sigma a = a + b ∧ sigma b = a + b

/-- Are there any pairs of relatively prime amicable numbers? -/
theorem main : ∃ a b : ℕ, IsAmicablePair a b ∧ a.Coprime b := by
  sorry

end OMA.S_wp_are_there_any_pairs_of_relatively_prime_amicable_numbers
