import OMAStatements.S_oeis_a070542

-- Reduction oeis-a070542.R1 of A070542: Numbers n such that binomial(2n,n) does not have two prime factors that add to 2n.
-- Credit: @sobrien032
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
T. D. Noe conjectured (OEIS A070542) that 1, 2, 3, 4, 6, 10, 15, 26, 28 and 64 are the only
`n ≥ 1` for which the central binomial coefficient `binomial(2n, n)` has no two distinct prime
factors adding up to `2n`. The statement is an equality of sets, so it splits into its two
inclusions.

`H1` is the finite check that the ten known terms have no such pair of prime factors. Both primes
are below 128, and for each term every pair of distinct primes adding up to `2n` has a member that
does not divide `binomial(2n, n)`.

`H2` is the open part, a strengthening of Goldbach's conjecture: every other `n ≥ 1` has two
distinct prime factors of `binomial(2n, n)` adding up to `2n`.
-/

namespace OMA.R_oeis_a070542_R1

/-- The ten known terms are positive, and for each of them `binomial(2n, n)` has no two distinct
prime factors adding up to `2n`. -/
def H1 : Prop :=
  ({1, 2, 3, 4, 6, 10, 15, 26, 28, 64} : Set ℕ) ⊆
    {n : ℕ | 1 ≤ n ∧ ¬ ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p ≠ q ∧ p ∣ Nat.choose (2 * n) n ∧
        q ∣ Nat.choose (2 * n) n ∧ p + q = 2 * n}

/-- The open part: every `n ≥ 1` for which `binomial(2n, n)` has no two distinct prime factors
adding up to `2n` is one of the ten known terms. -/
def H2 : Prop :=
  {n : ℕ | 1 ≤ n ∧ ¬ ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p ≠ q ∧ p ∣ Nat.choose (2 * n) n ∧
      q ∣ Nat.choose (2 * n) n ∧ p + q = 2 * n} ⊆
    ({1, 2, 3, 4, 6, 10, 15, 26, 28, 64} : Set ℕ)

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a070542.main :=
  fun h1 h2 => Set.Subset.antisymm h2 h1

end OMA.R_oeis_a070542_R1
