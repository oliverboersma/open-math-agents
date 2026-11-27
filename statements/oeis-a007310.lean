import Mathlib

/-!
# A007310: Numbers congruent to 1 or 5 mod 6

Source: https://oeis.org/A007310
Credit: @xor2k

Formalizes the OEIS A007310 conjecture (G. Detlefs; a paper proof by P. Bala is cited in the
entry): the terms are the numbers n such that ( Sum_{k = 1..n} k^14 ) mod n = 0.

Conventions: the sequence (offset 1) consists of the positive integers `n` with
`n % 6 = 1` or `n % 6 = 5`. The conjecture says this set coincides with the set of positive
integers `n` such that `n` divides `1^14 + 2^14 + ... + n^14`; it is stated as an equivalence
for every `n ≥ 1`. The sum is over `Finset.Icc 1 n` in `ℕ`, and `(S mod n = 0)` is written
`n ∣ S`.
-/

namespace OMA.S_oeis_a007310

/-- For every `n ≥ 1`: `n ≡ 1` or `5 (mod 6)` if and only if `n ∣ ∑_{k=1}^{n} k^14`. -/
theorem main :
    ∀ n : ℕ, 0 < n → ((n % 6 = 1 ∨ n % 6 = 5) ↔ n ∣ ∑ k ∈ Finset.Icc 1 n, k ^ 14) := by
  sorry

end OMA.S_oeis_a007310
