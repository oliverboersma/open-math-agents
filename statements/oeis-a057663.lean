import Mathlib

/-!
# A057663: Primes p such that p + 2^p is also a prime.

Source: https://oeis.org/A057663
Credit: @divmxnd0x

The terms `k` satisfy `φ(k + 2^k) = φ(k) + 2^k`, where `φ` is Euler's totient function: if `p` and
`p + 2^p` are prime then `φ(p + 2^p) = p + 2^p - 1 = φ(p) + 2^p`.

Conjecture (Juri-Stepan Gerasimov, May 23 2019): this sequence gives all numbers `k` that satisfy
`φ(k + 2^k) = φ(k) + 2^k`.

Formalization notes:
* The sequence consists of positive integers, so `k` ranges over `k ≥ 1` (for `k = 0` the identity
  reads `φ(1) = φ(0) + 1`, which holds trivially and is not part of the question).
* The statement is the equivalence "k satisfies the identity iff k is a term", for every `k ≥ 1`.
* For `1 ≤ k ≤ 22` the identity holds exactly for `k = 3, 5`, the terms of A057663 in that range
  (the next terms are 89, 317, 701).
-/

namespace OMA.S_oeis_a057663

/-- Gerasimov's conjecture: for `k ≥ 1`, `φ(k + 2^k) = φ(k) + 2^k` holds exactly when `k` and
`k + 2^k` are both prime. -/
theorem main : ∀ k : ℕ, 1 ≤ k →
    (Nat.totient (k + 2 ^ k) = Nat.totient k + 2 ^ k ↔ k.Prime ∧ (k + 2 ^ k).Prime) := by
  sorry

end OMA.S_oeis_a057663
