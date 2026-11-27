import Mathlib

/-!
# A191363: Numbers m whose deficiency is 2: sigma(m) - 2*m = -2.

Source: https://oeis.org/A191363
Credit: @mbilenko03

The entry records these conjectures about the terms `m` (positive integers with
`σ(m) = 2m - 2`):
1. `a(1) = 3` is the only odd term of the sequence;
2. all terms are of the form `(F(k) - 1) * F(k) / 2` where `F(k) = 2^(2^k) + 1` is a Fermat
   prime (the entry notes every such number is a term);
3. (Omar E. Pol, Oct 31 2018) all terms are second hexagonal numbers (A014105), i.e. of the form
   `j * (2j + 1)`;
4. (Omar E. Pol, Oct 31 2018) there are no terms with middle divisors.

`main` is the conjunction of the four.

Conventions:
- `σ(m) - 2m = -2` is written `σ(m) + 2 = 2m` in `ℕ`, with `σ = ArithmeticFunction.sigma 1`.
  (`m = 0` is excluded automatically: `σ(0) = 0` in Mathlib.)
- Second hexagonal numbers (A014105) are `j * (2j + 1)`, `j ≥ 0`.
- A middle divisor of `m` (A067742) is a divisor `d` in the half-open interval
  `[sqrt(m/2), sqrt(2m))`; for natural `d`, `m` this is `m ≤ 2 d^2 ∧ d^2 < 2m`.
-/

namespace OMA.S_oeis_a191363

/-- `m` has deficiency 2: `σ(m) = 2m - 2`. -/
def IsTerm (m : ℕ) : Prop := ArithmeticFunction.sigma 1 m + 2 = 2 * m

theorem main :
    (∀ m : ℕ, IsTerm m → Odd m → m = 3) ∧
    (∀ m : ℕ, IsTerm m → ∃ k : ℕ, (2 ^ (2 ^ k) + 1).Prime ∧
      m = (2 ^ (2 ^ k) + 1 - 1) * (2 ^ (2 ^ k) + 1) / 2) ∧
    (∀ m : ℕ, IsTerm m → ∃ j : ℕ, m = j * (2 * j + 1)) ∧
    (∀ m : ℕ, IsTerm m → ¬ ∃ d : ℕ, d ∣ m ∧ m ≤ 2 * d ^ 2 ∧ d ^ 2 < 2 * m) := by
  sorry

end OMA.S_oeis_a191363
