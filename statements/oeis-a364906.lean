import Mathlib

/-!
# Unique linear combinations of prime indices (OEIS A364906)

Source: https://oeis.org/A364906 (Gus Wiseman, OEIS Foundation, CC BY-SA 4.0).

The prime indices of n form the multiset of k with prime(k) dividing n, counted with
multiplicity, where prime(1) = 2; the index of a prime p is the prime counting value
of p. A364906(n) is the number of ways to write the sum of the prime indices of n
(A056239) as a nonnegative linear combination of that multiset: one coefficient per
entry of the multiset, so repeated indices get separate coefficients.

A319319 lists the positive n whose distinct divisors all have different GCDs of prime
indices (the GCD of the empty multiset, for the divisor 1, is 0).

Conjecture (in the entry): the positions of 1 in A364906 are exactly A319319.
-/

namespace OMA.S_oeis_a364906

/-- The prime indices of `n`, listed with multiplicity (prime(1) = 2). -/
def primeIndices (n : ℕ) : List ℕ :=
  n.primeFactorsList.map Nat.primeCounting

/-- A364906(n): the number of coefficient vectors `c`, one coefficient per prime index,
with `∑ c i * y i` equal to the sum of the prime indices `y`. -/
noncomputable def a (n : ℕ) : ℕ :=
  Nat.card {c : Fin (primeIndices n).length → ℕ //
    ∑ i, c i * (primeIndices n).get i = (primeIndices n).sum}

/-- The GCD of the prime indices of `d`. -/
def gcdIndices (d : ℕ) : ℕ := ((primeIndices d : Multiset ℕ)).gcd

/-- Membership in A319319: distinct divisors of `n` have different GCDs of prime indices. -/
def InA319319 (n : ℕ) : Prop :=
  0 < n ∧ Set.InjOn gcdIndices (n.divisors : Set ℕ)

/-- Wiseman's conjecture on A364906: `a n = 1` exactly for the terms of A319319. -/
theorem main : ∀ n : ℕ, 0 < n → (a n = 1 ↔ InA319319 n) := by
  sorry

end OMA.S_oeis_a364906
