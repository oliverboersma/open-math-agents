import Mathlib

/-!
# A157218: Number of ways to write the n-th positive odd integer in the form p+2^x+7*2^y with p a prime congruent to 1 mod 6 and x,y positive integers

Source: https://oeis.org/A157218
Credit: @mscheuern

The sequence is `a(n) = |{(p, x, y) : p + 2^x + 7 * 2^y = 2n - 1, p prime, p ≡ 1 (mod 6),
x, y positive integers}|` (OEIS formula line). The comment on the source page reads in full:

> On Feb 24 2009, Zhi-Wei Sun conjectured that a(n)>0 for all n=18,19,...; in other words, any
> odd integer greater than 34 can be written as the sum of a prime congruent to 1 mod 6, a positive
> power of 2 and seven times a positive power of 2. Sun verified the conjecture for odd integers
> below 5*10^7, and Qing-Hu Hou continued the verification for odd integers below 1.5*10^8 (on
> Sun's request). Compare the conjecture with R. Crocker's result that there are infinitely many
> positive odd integers not of the form p + 2^x + 2^y with p an odd prime and x,y positive integers.

`main` states the second form ("in other words") directly: for every odd `m > 34` there are a
prime `p` with `p % 6 = 1` and exponents `x, y ≥ 1` with `m = p + 2 ^ x + 7 * 2 ^ y`. Since the
`n`-th positive odd integer is `2n - 1`, `n ≥ 18` is exactly `2n - 1 > 34`, so this is the same as
`a(n) > 0` for all `n ≥ 18`.

Conventions:
* "positive power of 2" means `2 ^ x` with `x` a positive integer (the formula line says
  "x,y positive integers"), so `1 = 2 ^ 0` is excluded; likewise for `7 * 2 ^ y`.
* `x` and `y` need not differ, and the two powers may be equal.
* The bound is sharp: `33` has no such representation (`a(17) = 0` in the OEIS data).

Compare the sibling conjecture A157225 (the same form with `p ≡ 5 (mod 6)`), which is false: see
`FormalConjectures/OEIS/157225.lean`.
-/

namespace OMA.S_oeis_a157218

/-- Zhi-Wei Sun's conjecture (A157218): every odd integer greater than `34` is the sum of a prime
congruent to `1` modulo `6`, a positive power of `2`, and seven times a positive power of `2`. -/
theorem main :
    ∀ m : ℕ, Odd m → 34 < m →
      ∃ p x y : ℕ, p.Prime ∧ p % 6 = 1 ∧ 0 < x ∧ 0 < y ∧ m = p + 2 ^ x + 7 * 2 ^ y := by
  sorry

end OMA.S_oeis_a157218
