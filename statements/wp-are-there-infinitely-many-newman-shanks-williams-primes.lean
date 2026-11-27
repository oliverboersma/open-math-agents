import Mathlib

/-!
# Are there infinitely many Newman–Shanks–Williams primes?

Source: https://en.wikipedia.org/wiki/Newman–Shanks–Williams_prime
Credit: @LordMike

The problem appears in the Wikipedia list of unsolved problems in mathematics (number theory) as
Are there infinitely many Newman–Shanks–Williams primes?. The article on the Newman–Shanks–Williams
(NSW) primes says: 'a Newman–Shanks–Williams prime (NSW prime) is a prime number which can be
written in the form S_{2m+1} = ((1 + sqrt 2)^(2m+1) + (1 - sqrt 2)^(2m+1)) / 2. ... The sequence S
can be described by the recurrence relation S_0 = 1, S_1 = 1, S_n = 2 S_{n-1} + S_{n-2} for all
n >= 2. The first few terms are 1, 1, 3, 7, 17, 41, 99, ...' (the first NSW primes are 7, 41, 239,
9369319, 63018038201, ..., with indices 3, 5, 7, 19, 29, ...).

Modelling choices:
* `nswSeq` is the recurrence S_0 = S_1 = 1, S_(n+2) = 2 S_(n+1) + S_n over the naturals, exactly as
  in the source (the closed form with (1 + sqrt 2)^(2m+1) is equivalent and not used).
* An NSW prime is a prime number `p` with `p = nswSeq (2 * m + 1)` for some `m`; the claim is that
  the set of such primes is infinite. (Since `nswSeq` is strictly increasing from index 1 on, this
  is the same as infinitely many odd indices `n` with `nswSeq n` prime.) Primes at even indices
  (S_2 = 3, S_4 = 17, S_8 = 577, ...) are not NSW primes and are deliberately excluded.
* The source asks a yes/no question and states no conjectured answer. The statement below is the
  affirmative direction (infinitely many NSW primes), the natural direction of the question, in
  line with the usual expectation for such prime families. The answer could be negative.
-/

namespace OMA.S_wp_are_there_infinitely_many_newman_shanks_williams_primes

/-- The sequence S: S_0 = 1, S_1 = 1, S_(n+2) = 2 * S_(n+1) + S_n (OEIS A001333). -/
def nswSeq : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | (n + 2) => 2 * nswSeq (n + 1) + nswSeq n

/-- There are infinitely many Newman–Shanks–Williams primes, i.e. infinitely many primes of the
form `S_(2m+1)`. -/
theorem main : {p : ℕ | p.Prime ∧ ∃ m : ℕ, p = nswSeq (2 * m + 1)}.Infinite := by
  sorry

end OMA.S_wp_are_there_infinitely_many_newman_shanks_williams_primes
