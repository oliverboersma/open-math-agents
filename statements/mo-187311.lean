import Mathlib

/-!
# Sum of two squares and implication of Bunyakovsky conjecture

Source: https://mathoverflow.net/questions/187311
Credit: @zarnab222-dev

Let `a₁, a₂, a₃, a₄ ∈ ℤ[x]` with `aᵢ ≠ ± aⱼ` for `i ≠ j` satisfy `a₁² + a₂² = a₃² + a₄²`, and put
`p = a₁² + a₂²`. The question: must the content of `p` be greater than one when `p` is irreducible?
The affirmative claim is stated.

Translation choices:
* `aᵢ ≠ ± aⱼ, i ≠ j` is written out as the twelve inequalities `aᵢ ≠ aⱼ`, `aᵢ ≠ -aⱼ` for `i < j`
  (the conditions for `i > j` are equivalent to these);
* irreducible means irreducible in `ℚ[x]`: the example in the question,
  `p = 5 · (325 x⁴ - 1184 x³ + 984 x² + 640 x + 80)`, is called irreducible although its content is
  `5`, which rules out irreducibility in `ℤ[x]`;
* the content is `Polynomial.content`, the nonnegative gcd of the coefficients, so
  `greater than one` is `1 < content`.
-/

namespace OMA.S_mo_187311

open Polynomial

theorem main :
    ∀ a₁ a₂ a₃ a₄ : ℤ[X],
      a₁ ≠ a₂ → a₁ ≠ -a₂ → a₁ ≠ a₃ → a₁ ≠ -a₃ → a₁ ≠ a₄ → a₁ ≠ -a₄ →
      a₂ ≠ a₃ → a₂ ≠ -a₃ → a₂ ≠ a₄ → a₂ ≠ -a₄ → a₃ ≠ a₄ → a₃ ≠ -a₄ →
      a₁ ^ 2 + a₂ ^ 2 = a₃ ^ 2 + a₄ ^ 2 →
      Irreducible ((a₁ ^ 2 + a₂ ^ 2).map (Int.castRingHom ℚ)) →
      1 < (a₁ ^ 2 + a₂ ^ 2).content := by
  sorry

end OMA.S_mo_187311
