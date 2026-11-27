import Mathlib

/-!
# Are there infinitely many sexy primes?

Source: https://en.wikipedia.org/wiki/Sexy_prime
Credit: @ihateSAS

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.

The source: "Sexy primes are prime numbers that differ from each other by six", e.g. `5` and `11`,
`11` and `17`; the pairs are `(p, p + 6)`.  The open question, from "List of unsolved problems in
mathematics", is whether there are infinitely many such pairs.

Each pair is counted once, by its smaller member `p`, since the two members differ by six.  So the
proposition formalized below is that the set of `p` with `p` and `p + 6` both prime is infinite.
-/

namespace OMA.S_wp_are_there_infinitely_many_sexy_primes

-- definitions the statement needs (no sorry, no axiom)

/-- `p` is the smaller member of a **sexy prime** pair: both `p` and `p + 6` are prime. -/
def IsSexyPrime (p : ℕ) : Prop :=
  p.Prime ∧ (p + 6).Prime

/-- Are there infinitely many sexy primes? -/
theorem main : {p : ℕ | IsSexyPrime p}.Infinite := by
  sorry

end OMA.S_wp_are_there_infinitely_many_sexy_primes
