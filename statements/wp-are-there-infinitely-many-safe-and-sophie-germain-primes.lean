import Mathlib

/-!
# Are there infinitely many safe and Sophie Germain primes?

Source: https://en.wikipedia.org/wiki/Safe_and_Sophie_Germain_primes
Credit: @ihateSAS

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.

The source: "a prime number `p` is a **Sophie Germain prime** if `2 * p + 1` is also prime.  The
number `2 * p + 1` associated with a Sophie Germain prime is called a **safe prime**", and "it is
conjectured that there are infinitely many Sophie Germain primes, but this remains unproven".

The source also states that "finding safe primes and finding Sophie Germain primes are equivalent",
because `p = 2 * q + 1` is a safe prime exactly when `q` is a Sophie Germain prime; the map
`q ↦ 2 * q + 1` is injective.  So a single infinitude statement covers the pair, and the
proposition formalized below is: the set of Sophie Germain primes is infinite.
-/

namespace OMA.S_wp_are_there_infinitely_many_safe_and_sophie_germain_primes

-- definitions the statement needs (no sorry, no axiom)

/-- `p` is a **Sophie Germain prime** when both `p` and `2 * p + 1` are prime; `2 * p + 1` is then
the associated **safe prime**. -/
def IsSophieGermainPrime (p : ℕ) : Prop :=
  p.Prime ∧ (2 * p + 1).Prime

/-- Are there infinitely many safe and Sophie Germain primes? -/
theorem main : {p : ℕ | IsSophieGermainPrime p}.Infinite := by
  sorry

end OMA.S_wp_are_there_infinitely_many_safe_and_sophie_germain_primes
