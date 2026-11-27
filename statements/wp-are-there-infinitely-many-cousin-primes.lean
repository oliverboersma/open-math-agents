import Mathlib

/-!
# Are there infinitely many cousin primes?

Source: https://en.wikipedia.org/wiki/Cousin_prime
Credit: @ihateSAS

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.

The source: "Cousin primes are prime numbers that differ by four", e.g. `3` and `7`, `7` and `11`,
`13` and `17`.  The open question is whether there are infinitely many such pairs.

Each pair is counted once, by its smaller member `p`, since `p` and `p + 4` cannot both be prime
unless `p` is the smaller of the two.  So the proposition formalized below is that the set of
`p` with `p` and `p + 4` both prime is infinite.
-/

namespace OMA.S_wp_are_there_infinitely_many_cousin_primes

-- definitions the statement needs (no sorry, no axiom)

/-- `p` is the smaller member of a **cousin prime** pair: both `p` and `p + 4` are prime. -/
def IsCousinPrime (p : ℕ) : Prop :=
  p.Prime ∧ (p + 4).Prime

/-- Are there infinitely many cousin primes? -/
theorem main : {p : ℕ | IsCousinPrime p}.Infinite := by
  sorry

end OMA.S_wp_are_there_infinitely_many_cousin_primes
