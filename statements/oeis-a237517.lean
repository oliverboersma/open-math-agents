import Mathlib

/-!
# A237517: Pisano period of n^2 divided by Pisano period of n.

Source: https://oeis.org/A237517
Credit: @sntntHb

Data: 1, 2, 3, 4, 5, 1, 7, 8, 9, 5, 11, 1, 13, 7, 15, 16, 17, 9, 19, 10, ...

Conjecture (Saha & Karthik, stated on the OEIS page): `a(n) = 1` only for `n = 1, 6, 12`.

Conventions:
- `pisano m` is the Pisano period of `m`: the least `k > 0` with `F(k) ≡ 0` and `F(k+1) ≡ 1`
  modulo `m` (so `pisano 1 = 1`, `pisano 2 = 3`).
- Since `pisano n` divides `pisano (n^2)` (OEIS comment: "For all n, a(n) | n"), the condition
  `a(n) = pisano (n^2) / pisano n = 1` is stated as `pisano (n^2) = pisano n`.
-/

namespace OMA.S_oeis_a237517

/-- The Pisano period of `m`. -/
noncomputable def pisano (m : ℕ) : ℕ :=
  sInf {k : ℕ | 0 < k ∧ Nat.fib k ≡ 0 [MOD m] ∧ Nat.fib (k + 1) ≡ 1 [MOD m]}

theorem main : {n : ℕ | 0 < n ∧ pisano (n ^ 2) = pisano n} = {1, 6, 12} := by
  sorry

end OMA.S_oeis_a237517
