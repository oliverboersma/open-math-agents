import Mathlib.Data.Nat.Factorization.Defs

/-!
# Rows ending in 33 in OEIS A372313

Ali Sada proposed the conjecture in https://oeis.org/A372313.
The row update uses A372289, by Antti Karttunen and Ali Sada.
Source: https://oeis.org/A372289
Credit: @ptlom (with Codex)
-/

namespace OMA.S_oeis_a372313

/-- A372289. The exponent is the number of factors of two in the input. -/
def transform (x : ℕ) : ℕ :=
  let e := x.factorization 2
  x * 2 ^ e + (4 ^ e - 1) / 3

/-- A372313 with the original one-based row and column indices.
Column zero is a sentinel outside the sequence. -/
def entry (n : ℕ) : ℕ → ℕ
  | 0 => 0
  | 1 => 2 * n - 1
  | k + 2 => transform (entry n (k + 1) + (2 * n - 1))

/-- If the first entry ends in 33, every entry in that row ends in 33. -/
theorem main :
    ∀ n : ℕ, 1 ≤ n → entry n 1 % 100 = 33 →
      ∀ k : ℕ, 1 ≤ k → entry n k % 100 = 33 := by
  sorry

end OMA.S_oeis_a372313
