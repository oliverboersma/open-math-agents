import Mathlib

/-!
# A000032: Lucas numbers beginning at 2: L(n) = L(n-1) + L(n-2), L(0) = 2, L(1) = 1.

Source: https://oeis.org/A000032
Credit: @OrangeHeadz

The comments of A000032 carry two conjectures. `main` is their conjunction.

## (F) Forberg, Dec 31 2015

A000032: *A conjecture on the divisibility of infinite subsequences of Lucas numbers by prime(n)^m,
m >= 1, is given in A266587, together with the prime entry points.*

A266587 (https://oeis.org/A266587) defines a(n) as the smallest index of a Lucas number divisible by
prime(n), or 0 if there is none, and states:

*Conjecture: Infinite Lucas subsequences divisible by the powers of odd primes, p(n), for which
a(n) > 0, are given by:
Lucas(a(n) + a(n)*(p(n)-1)*(Sum_{j=1..m-1} p(n)^(j-1)) + 2*i*a(n)*p(n)^(m-1)) is divisible by p(n)^m,
where p(n) > 2, i >= 0, m > 1. Note: the formula above also works for m=1 if the Sum is assumed to be
zero when the upper summation index limit is less than initial summation index.*

Conventions for (F):
* The entry point is indexed by the prime p itself rather than by n with p = prime(n): `lucasEntry p`.
  `sInf` of the empty set of naturals is 0, which is exactly the convention *0 if it does not exist*.
* The range of m is m >= 1, as in the A000032 comment and in the note of A266587: for m = 1 the sum
  over `Finset.Icc 1 0` is empty, hence zero, which is the convention the note asks for.
* The index formula is kept as the source writes it (it is not simplified). Natural subtraction is
  exact here: p > 2, m >= 1 and j >= 1.

## (P) Purath, Apr 19 2019

A000032: *While all prime numbers appear as factors in the Fibonacci numbers, this is not the case with
the Lucas numbers. For example, L(n) is never divisible by the following prime numbers < 150: 5, 13,
17, 37, 53, 61, 73, 89, 97, 109, 113, 137, 149 ... See A053028. Conjecture: Three properties can be
determined for these prime numbers:
First observation: The prime factors > 3 occur in the Fibonacci numbers with an odd index.
Second observation: These are the prime numbers p congruent to 2, 3 (modulo 5), which occur both in
Fibonacci(p+1) and in Fibonacci((p+1)/2) as prime factors, or the prime numbers p congruent to 1, 4
(modulo 5), which occur both in Fibonacci((p-1)/2) and in Fibonacci((p-1)/(2^k)) with k >= 2.
Third observation: The Pisano period lengths of these prime numbers, given in A001175, are always
divisible by 4, but not by 8. In contrast, those of the prime factors of Lucas numbers are divisible
either by 2, but not by 4, or by 8.*

Here *these prime numbers* are the primes that divide no Lucas number (A053028): `DividesNoLucas`.

Readings chosen for (P), where the source is ambiguous or literally fails on a degenerate case:
* The observations are read as what the source announces, properties OF these primes (for every such
  prime, ...), not as characterisations. With the reading of k below, the converse of the second
  observation is false: p = 401 and p = 521 = L(13) satisfy its second alternative.
* Second observation, p = 5. The prime 5 is in the list of the source, but it is congruent to neither
  2, 3 nor 1, 4 modulo 5, so the observation read literally fails at 5. The split by p mod 5 is the
  usual one for Fibonacci numbers, where 5 is the excluded prime: the observation is stated for p ≠ 5.
* Second observation, *with k >= 2*: for some k >= 2 such that 2^k divides p - 1 (so that
  (p-1)/(2^k) is an integer). The divisions by 2 are exact, since every such p is odd.
* Third observation, second sentence (*In contrast ...*). It is stated for odd primes: 2 divides
  L(0) = 2 and L(3) = 4, but its Pisano period is 3, so the sentence read literally fails at 2.
* First observation: the restriction *> 3* is kept as a hypothesis (no such prime is <= 3).
* The Pisano period of m (A001175) is the least k > 0 such that F(n + k) ≡ F(n) (mod m) for all n.
-/

namespace OMA.S_oeis_a000032

/-- The Lucas numbers (A000032): `L(0) = 2`, `L(1) = 1`, `L(n) = L(n-1) + L(n-2)`. -/
def lucas : ℕ → ℕ
  | 0 => 2
  | 1 => 1
  | n + 2 => lucas (n + 1) + lucas n

/-- The Lucas entry point of `p` (A266587, indexed by the prime itself): the smallest index of a
Lucas number divisible by `p`, or `0` if no Lucas number is divisible by `p`. -/
noncomputable def lucasEntry (p : ℕ) : ℕ :=
  sInf {k : ℕ | p ∣ lucas k}

/-- The Pisano period of `m` (A001175): the least period `k > 0` of the Fibonacci numbers mod `m`. -/
noncomputable def pisano (m : ℕ) : ℕ :=
  sInf {k : ℕ | 0 < k ∧ ∀ n : ℕ, Nat.fib (n + k) ≡ Nat.fib n [MOD m]}

/-- `p` is a prime that divides no Lucas number (A053028: 5, 13, 17, 37, 53, 61, 73, 89, ...). -/
def DividesNoLucas (p : ℕ) : Prop :=
  p.Prime ∧ ∀ n : ℕ, ¬ p ∣ lucas n

/-- (F) The conjecture of A266587 that the A000032 comment refers to. -/
def Forberg : Prop :=
  ∀ p : ℕ, p.Prime → 2 < p → 0 < lucasEntry p →
    ∀ m i : ℕ, 1 ≤ m →
      p ^ m ∣ lucas (lucasEntry p
        + lucasEntry p * (p - 1) * (∑ j ∈ Finset.Icc 1 (m - 1), p ^ (j - 1))
        + 2 * i * lucasEntry p * p ^ (m - 1))

/-- (P), first observation. -/
def PurathFirst : Prop :=
  ∀ p : ℕ, DividesNoLucas p → 3 < p → ∃ n : ℕ, Odd n ∧ p ∣ Nat.fib n

/-- (P), second observation. -/
def PurathSecond : Prop :=
  ∀ p : ℕ, DividesNoLucas p → p ≠ 5 →
    ((p % 5 = 2 ∨ p % 5 = 3) ∧ p ∣ Nat.fib (p + 1) ∧ p ∣ Nat.fib ((p + 1) / 2)) ∨
    ((p % 5 = 1 ∨ p % 5 = 4) ∧ p ∣ Nat.fib ((p - 1) / 2) ∧
      ∃ k : ℕ, 2 ≤ k ∧ 2 ^ k ∣ p - 1 ∧ p ∣ Nat.fib ((p - 1) / 2 ^ k))

/-- (P), third observation: both of its sentences. -/
def PurathThird : Prop :=
  (∀ p : ℕ, DividesNoLucas p → 4 ∣ pisano p ∧ ¬ 8 ∣ pisano p) ∧
  (∀ p : ℕ, p.Prime → p ≠ 2 → (∃ n : ℕ, p ∣ lucas n) →
    (2 ∣ pisano p ∧ ¬ 4 ∣ pisano p) ∨ 8 ∣ pisano p)

theorem main : Forberg ∧ PurathFirst ∧ PurathSecond ∧ PurathThird := by
  sorry

end OMA.S_oeis_a000032
