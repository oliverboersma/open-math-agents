import Mathlib

/-!
# Are there infinitely many palindromic primes to every base?

Source: https://en.wikipedia.org/wiki/Palindromic_prime
Credit: @ihateSAS

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.

The source: a **palindromic prime** is a prime number that is a palindromic number in a given base,
i.e. its base-`b` expansion reads the same in both directions.  The open question is whether, for
*every* base `b ≥ 2`, infinitely many primes are palindromes in that base.

`Nat.digits b n` is Mathlib's list of the base-`b` digits of `n`, least significant first, with no
leading zeros.  Reading the expansion in both directions is therefore the same as asking whether
that list equals its reverse.

So the proposition formalized below is: for every base `b ≥ 2`, the set of primes `p` whose base-`b`
digit list is a palindrome is infinite.
-/

namespace OMA.S_wp_are_there_infinitely_many_palindromic_primes_to_every_base

-- definitions the statement needs (no sorry, no axiom)

/-- `p` is a **palindromic prime in base `b`**: `p` is prime and its base-`b` expansion reads the
same in both directions. -/
def IsPalindromicPrimeInBase (b p : ℕ) : Prop :=
  p.Prime ∧ (Nat.digits b p).reverse = Nat.digits b p

/-- Are there infinitely many palindromic primes to every base? -/
theorem main : ∀ b : ℕ, 2 ≤ b → {p : ℕ | IsPalindromicPrimeInBase b p}.Infinite := by
  sorry

end OMA.S_wp_are_there_infinitely_many_palindromic_primes_to_every_base
