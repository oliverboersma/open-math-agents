import Mathlib

/-!
# Are there any Wieferich primes in base 47?

Source: https://en.wikipedia.org/wiki/Wieferich_prime
Credit: @ihateSAS

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.

A **Wieferich prime** is a prime `p` such that `p ^ 2` divides `2 ^ (p - 1) - 1`; the notion
generalises to a base `a`: `p ^ 2` divides `a ^ (p - 1) - 1`, with `p` not dividing `a` (otherwise
`a ^ (p - 1) - 1 ≡ -1 (mod p)` and the congruence could not hold).  The open question, item 6 of
the base-dependent list in "List of unsolved problems in mathematics", is whether the base `47`
admits any such prime.

So the proposition formalized below is: there exists a prime `p` with `p ∤ 47` and
`p ^ 2 ∣ 47 ^ (p - 1) - 1`.
-/

namespace OMA.S_wp_are_there_any_wieferich_primes_in_base_47

-- definitions the statement needs (no sorry, no axiom)

/-- `p` is a **Wieferich prime in base `a`**: `p` is prime, `p` does not divide `a`, and `p ^ 2`
divides `a ^ (p - 1) - 1`. -/
def IsWieferichPrimeInBase (a p : ℕ) : Prop :=
  p.Prime ∧ ¬ p ∣ a ∧ p ^ 2 ∣ a ^ (p - 1) - 1

/-- Are there any Wieferich primes in base 47? -/
theorem main : ∃ p : ℕ, IsWieferichPrimeInBase 47 p := by
  sorry

end OMA.S_wp_are_there_any_wieferich_primes_in_base_47
