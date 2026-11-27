import Mathlib

/-!
# Are all Mersenne numbers of prime index square-free?

Source: https://en.wikipedia.org/wiki/Mersenne_number
Credit: @ihateSAS

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.

The Mersenne number of index `n` is `M n = 2 ^ n - 1`; the source calls the index prime when it
says "of prime index".  The open question (Wikipedia, "Mersenne prime", section *Open questions*;
also Open Problem Garden, "Are all Mersenne Numbers with prime exponent square-free?") is whether
every such number is square-free, i.e. whether each prime factor of `2 ^ p - 1` occurs exactly once
in its factorisation, for every prime `p`.

So the proposition formalized below is: for every prime `p`, `2 ^ p - 1` is square-free.
All Mersenne numbers with prime exponent known so far are square-free; whether this holds in
general is open (Guy, *Unsolved Problems in Number Theory*, A3).
-/

namespace OMA.S_wp_are_all_mersenne_numbers_of_prime_index_square_free

-- definitions the statement needs (no sorry, no axiom)

/-- The Mersenne number of index `n`, `M n = 2 ^ n - 1`. -/
def mersenne (n : ℕ) : ℕ :=
  2 ^ n - 1

/-- Are all Mersenne numbers of prime index square-free? -/
theorem main : ∀ p : ℕ, p.Prime → Squarefree (mersenne p) := by
  sorry

end OMA.S_wp_are_all_mersenne_numbers_of_prime_index_square_free
