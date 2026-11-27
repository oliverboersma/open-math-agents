import Mathlib

/-!
# Are there infinitely many cluster primes?

Source: https://en.wikipedia.org/wiki/cluster_prime
Credit: @ihateSAS

Definition (Wikipedia): a *cluster prime* is a prime number `p` such that every even positive
integer `k <= p - 3` can be written as the difference between two prime numbers not exceeding `p`.
By convention, `2` is not considered to be a cluster prime.

Erdos asked whether there are infinitely many cluster primes; this is still open.
-/

namespace OMA.S_wp_are_there_infinitely_many_cluster_primes

/-- A prime `p` is a cluster prime when every even positive `k` with `k + 3 <= p` is the
difference of two primes both at most `p`. The conjunct `p ≠ 2` records the source convention
that `2` is not a cluster prime: for `p = 2` the range of `k` is empty, so without it the
condition would hold vacuously. The source bound `k <= p - 3` is written `k + 3 <= p`, which is
equivalent over `Nat`. -/
def IsClusterPrime (p : ℕ) : Prop :=
  p.Prime ∧ p ≠ 2 ∧
    ∀ k : ℕ, Even k → 0 < k → k + 3 ≤ p →
      ∃ q r : ℕ, q.Prime ∧ r.Prime ∧ q ≤ p ∧ r ≤ p ∧ q - r = k

/-- Erdos's question: are there infinitely many cluster primes? -/
theorem main : Set.Infinite {p : ℕ | IsClusterPrime p} := by
  sorry

end OMA.S_wp_are_there_infinitely_many_cluster_primes
