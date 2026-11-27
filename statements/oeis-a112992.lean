import Mathlib

/-!
# A112992: Numbers k such that ceiling(2^(2^k mod k)/3) is odd

Source: https://oeis.org/A112992
Credit: @xor2k

Formalizes the conjecture in the comments of OEIS A112992 (offset 1), which reads:
Conjecture: the odd values of ceiling(2^(2^k mod k)/3) are Jacobsthal numbers (and the even
values are 1 plus a Jacobsthal number).

Conventions:
* `k` ranges over the positive integers `k >= 1` (the domain of the sequence).
* `c(k) = ceiling(2^(2^k mod k) / 3)`: the exponent `2^k % k` is computed in `ℕ`, the quotient
  `2^(2^k % k) / 3` is the exact rational number, and the ceiling is Mathlib's `Int.ceil`.
* Jacobsthal numbers are the terms of OEIS A001045: `J(0) = 0`, `J(1) = 1`,
  `J(n+2) = J(n+1) + 2*J(n)`; a Jacobsthal number is a value `J(j)` for some `j : ℕ`.
* The conjecture is read as two implications for every `k >= 1`: if `c(k)` is odd then
  `c(k) = J(j)` for some `j`, and if `c(k)` is even then `c(k) = J(j) + 1` for some `j`.
-/

namespace OMA.S_oeis_a112992

/-- Jacobsthal numbers (OEIS A001045): `J(0) = 0`, `J(1) = 1`, `J(n+2) = J(n+1) + 2*J(n)`. -/
def J : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 => J (n + 1) + 2 * J n

/-- `c(k) = ceiling(2^(2^k mod k) / 3)`, with the quotient taken in `ℚ`. -/
def c (k : ℕ) : ℤ :=
  ⌈((2 : ℚ) ^ (2 ^ k % k)) / 3⌉

/-- For every `k >= 1`: odd values of `c(k)` are Jacobsthal numbers, and even values of `c(k)`
are one plus a Jacobsthal number. -/
theorem main :
    ∀ k : ℕ, 1 ≤ k →
      (Odd (c k) → ∃ j : ℕ, c k = (J j : ℤ)) ∧
      (Even (c k) → ∃ j : ℕ, c k = (J j : ℤ) + 1) := by
  sorry

end OMA.S_oeis_a112992
