import Mathlib

/-!
# A241568: Quadratic nonresidues k < prime(n)/2 modulo prime(n) that are Fibonacci numbers

Source: https://oeis.org/A241568
Credit: @niclorusso

a(n) = |{0 < k < prime(n)/2: k is not only a quadratic nonresidue modulo prime(n) but also a
Fibonacci number}|.

Conjecture (Zhi-Wei Sun, in the comments of A241568): (i) a(n) > 0 for all n > 2. In other words,
for any prime p > 3, there is a Fibonacci number among 1, ..., (p-1)/2 which is a quadratic
nonresidue modulo p.

(Only part (i) of the conjecture is formalized here.)

Conventions:
* The Fibonacci numbers are the values of Mathlib's `Nat.fib`.
* For 0 < k < p, k is a quadratic nonresidue modulo the prime p when its class in `ZMod p` is not a
  square: `¬ IsSquare (k : ZMod p)`.
* 0 < k < p/2 for odd p is the same as 1 <= k <= (p - 1)/2.
-/

namespace OMA.S_oeis_a241568

/-- Sun's conjecture (i) on A241568: for every prime `p > 3` there is a Fibonacci number `k` with
`1 <= k <= (p - 1)/2` that is a quadratic nonresidue modulo `p`. -/
theorem main : ∀ p : ℕ, p.Prime → 3 < p →
    ∃ k : ℕ, 1 ≤ k ∧ k ≤ (p - 1) / 2 ∧ (∃ m : ℕ, Nat.fib m = k) ∧ ¬ IsSquare (k : ZMod p) := by
  sorry

end OMA.S_oeis_a241568
