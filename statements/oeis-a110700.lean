import Mathlib

/-!
# A110700: Number of zeros in the smallest prime with Hamming weight n (given by A061712)

Source: https://oeis.org/A110700
Credit: @niclorusso

Conjecture (in the comments of A110700): a(n) is never greater than 3.

Conventions:
* The sequence has offset 1. A061712(n) is the smallest prime with Hamming weight n, i.e. with
  exactly n 1's in binary; a(n) is the number of 0's in its binary expansion.
* `Nat.digits 2 q` lists the binary digits of q (least significant first, no leading zeros), so the
  Hamming weight is `(Nat.digits 2 q).count 1` and the number of zeros is `(Nat.digits 2 q).count 0`.
* The conjecture is stated for every n >= 1 for which the smallest such prime exists (`IsLeast`).
-/

namespace OMA.S_oeis_a110700

/-- The conjecture on A110700: the smallest prime with exactly `n` ones in binary has at most
three zeros in binary. -/
theorem main : ∀ n p : ℕ, 1 ≤ n →
    IsLeast {q : ℕ | q.Prime ∧ (Nat.digits 2 q).count 1 = n} p →
    (Nat.digits 2 p).count 0 ≤ 3 := by
  sorry

end OMA.S_oeis_a110700
