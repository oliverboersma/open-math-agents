import Mathlib

/-!
# A003459: Absolute primes (or permutable primes): every permutation of the digits is a prime.

Source: https://oeis.org/A003459
Credit: @mbilenko03

Conjecture (Max Alekseyev, Oct 08 2018): for `n ≥ 23`, `a(n) = A004022(n-21)`, where A004022 lists
the primes of the form `(10^k - 1)/9` (repunit primes: 11, R19, R23, …).

The known terms are `a(1..22) = 2, 3, 5, 7, 11, 13, 17, 31, 37, 71, 73, 79, 97, 113, 131, 199, 311,
337, 373, 733, 919, 991`, and `A004022(1) = 11`. Every repunit prime is permutable (all its digits
are equal), and 11 is the only repunit prime `≤ 991`. So the conjecture says exactly that the
permutable primes greater than `991 = a(22)` are the repunit primes greater than 11, listed in the
same order; equivalently, every permutable prime greater than 991 is a repunit. `main` states it
in this form, which does not need the sequences to be infinite.

Conventions:
- Digits are base 10, via `Nat.digits 10` (least significant first; the order does not matter
  since all permutations are taken). A permutation of the digit list is read back with
  `Nat.ofDigits 10`. A number containing the digit 0 is never permutable (a permutation ending in
  0 gives a multiple of 10), so leading zeros play no role.
- `IsPermutablePrime p` already implies `p` is prime (take the identity permutation).
- A repunit is `(10^k - 1)/9` for some `k`.
-/

namespace OMA.S_oeis_a003459

/-- Every permutation of the decimal digits of `p` is (the digit list of) a prime. -/
def IsPermutablePrime (p : ℕ) : Prop :=
  ∀ l : List ℕ, l.Perm (Nat.digits 10 p) → (Nat.ofDigits 10 l).Prime

theorem main : ∀ p : ℕ, IsPermutablePrime p → 991 < p → ∃ k : ℕ, p = (10 ^ k - 1) / 9 := by
  sorry

end OMA.S_oeis_a003459
