import Mathlib

/-!
# A071621: Primes that can be written as a * b + c * d, where a, b, c and d are also primes

Source: https://oeis.org/A071621
Credit: @niclorusso

Conjecture (in the comments of A071621): Only the primes 2, 3, 5, 7, 11 and 17 are not
representable by this form.

Conventions:
* a, b, c, d range over the primes (not necessarily distinct).
* "Only the primes 2, 3, 5, 7, 11 and 17 are not representable" is stated as a set equality.
-/

namespace OMA.S_oeis_a071621

/-- `r = a * b + c * d` for some primes `a, b, c, d`. -/
def IsRepresentable (r : ℕ) : Prop :=
  ∃ a b c d : ℕ, a.Prime ∧ b.Prime ∧ c.Prime ∧ d.Prime ∧ a * b + c * d = r

/-- The conjecture on A071621: the primes that are not of the form `a * b + c * d` with `a, b, c, d`
prime are exactly `2, 3, 5, 7, 11, 17`. -/
theorem main : {r : ℕ | r.Prime ∧ ¬ IsRepresentable r} = {2, 3, 5, 7, 11, 17} := by
  sorry

end OMA.S_oeis_a071621
